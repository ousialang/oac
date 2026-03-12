use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::Path;

use anyhow::Context;

use crate::invariant_metadata::{
    build_function_arg_invariant_assumptions_for_names, discover_struct_invariant_bindings,
    InvariantBinding,
};
use crate::ir::{ModelInvariantDefinition, ResolvedProgram};
use crate::precondition_metadata::build_function_precondition_assumptions_for_names;
use crate::verification_cache::{
    VerificationCacheMode, VerificationCacheWritePolicy, VerificationConfig,
    VerificationSummaryCandidate, VerificationSummaryInput, VerificationSummaryKind,
};
use crate::verification_checker::{
    checker_module_with_reachable_callees, sanitize_ident, summarize_solver_output,
};
use crate::verification_cycles::{
    reachable_user_functions, reject_recursion_cycles_with_entry_assumptions,
};
use crate::verification_outcomes::{
    record_outcome, VerificationKind, VerificationOutcome, VerificationOutcomeRecord,
};
use crate::verification_profile::VerificationProfile;
use crate::verification_solver::{format_attempts, solve_chc_with_policy};

#[allow(dead_code)]
pub fn verify_model_invariants_with_qbe(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
) -> anyhow::Result<()> {
    verify_model_invariants_with_qbe_with_config(
        program,
        qbe_module,
        target_dir,
        VerificationConfig::new(
            VerificationProfile::default(),
            VerificationCacheMode::Off,
            target_dir.join("verification_cache"),
            VerificationCacheWritePolicy::PersistUnsat,
        ),
    )
}

#[allow(dead_code)]
pub fn verify_model_invariants_with_qbe_with_profile(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
    profile: VerificationProfile,
) -> anyhow::Result<()> {
    verify_model_invariants_with_qbe_with_config(
        program,
        qbe_module,
        target_dir,
        VerificationConfig::new(
            profile,
            VerificationCacheMode::Off,
            target_dir.join("verification_cache"),
            VerificationCacheWritePolicy::PersistUnsat,
        ),
    )
}

pub(crate) fn verify_model_invariants_with_qbe_with_config(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
    config: VerificationConfig,
) -> anyhow::Result<()> {
    let mut model_invariants = program.model_invariants.clone();
    model_invariants.sort_by(|lhs, rhs| {
        lhs.key
            .cmp(&rhs.key)
            .then(lhs.function_name.cmp(&rhs.function_name))
    });
    if model_invariants.is_empty() {
        return Ok(());
    }

    let invariant_by_struct = discover_struct_invariant_bindings(program)?;
    let verification_dir = target_dir.join("model_invariants");
    std::fs::create_dir_all(&verification_dir).with_context(|| {
        format!(
            "failed to create model invariant verification directory {}",
            verification_dir.display()
        )
    })?;

    let function_map = qbe_module
        .functions
        .iter()
        .map(|function| (function.name.clone(), function.clone()))
        .collect::<HashMap<_, _>>();

    let mut failures = Vec::new();
    for invariant in &model_invariants {
        let reachable = reachable_user_functions(program, &invariant.function_name)?;
        let reachable_names = reachable.iter().cloned().collect::<BTreeSet<_>>();
        let arg_invariant_assumptions = build_function_arg_invariant_assumptions_for_names(
            program,
            &reachable_names,
            &invariant_by_struct,
        )?;
        let function_precondition_assumptions =
            build_function_precondition_assumptions_for_names(program, &reachable_names)?;
        reject_recursion_cycles_with_entry_assumptions(
            program,
            &invariant.function_name,
            &reachable,
            &arg_invariant_assumptions,
            &function_precondition_assumptions,
            "model invariant verification",
        )?;

        let (checker_module, assumptions) =
            build_checker_module(program, invariant, &invariant_by_struct, &function_map)?;
        let checker_qbe = checker_module.to_string();
        let site_stem = format!("site_{}", sanitize_ident(&invariant.function_name));
        let qbe_filename = format!("{}.qbe", site_stem);
        let smt_filename = format!("{}.smt2", site_stem);
        let qbe_path = verification_dir.join(&qbe_filename);
        std::fs::write(&qbe_path, &checker_qbe).with_context(|| {
            format!(
                "failed to write model invariant checker QBE program {}",
                qbe_path.display()
            )
        })?;

        let mut header_comments = vec![
            format!("model invariant {}", invariant.display_name),
            format!("function: {}", invariant.function_name),
            format!("key: {}", invariant.key),
            "bad means exit == 1 is reachable".to_string(),
        ];
        if let Some(source_span) = &invariant.source_span {
            header_comments.insert(1, format!("source: {}", source_span.display_compact()));
        }
        let scripts = qbe_smt::qbe_module_to_annotated_smt_with_assumptions(
            &checker_module,
            "main",
            &qbe_smt::EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
            &assumptions,
            &qbe_smt::ArtifactAnnotations { header_comments },
        )
        .map_err(|err| {
            anyhow::anyhow!(
                "failed to encode model invariant checker QBE for {}: {}\n{}",
                invariant.function_name,
                err,
                err.render_report_plain("model-invariant-checker")
            )
        })?;

        let smt_path = verification_dir.join(&smt_filename);
        std::fs::write(&smt_path, &scripts.artifact_smt).with_context(|| {
            format!(
                "failed to write model invariant SMT obligation {}",
                smt_path.display()
            )
        })?;

        let summary = VerificationSummaryCandidate::from_inputs(
            &invariant.function_name,
            VerificationSummaryKind::ModelInvariantFunction,
            &[VerificationSummaryInput {
                kind: VerificationKind::ModelInvariant,
                local_id: invariant.function_name.clone(),
                smt: scripts.solver_smt.clone(),
            }],
        );
        let cached_summary_match = if config.cache_reads_enabled() {
            summary.matches_persisted_unsat(&config.cache_root)?
        } else {
            false
        };
        if config.cache_trust_enabled() && cached_summary_match {
            record_outcome(VerificationOutcomeRecord {
                kind: VerificationKind::ModelInvariant,
                obligation_id: invariant.function_name.clone(),
                caller: invariant.function_name.clone(),
                callee: None,
                invariant_key: Some(invariant.key.clone()),
                outcome: VerificationOutcome::Unsat,
                fixture: None,
            });
            continue;
        }

        match solve_chc_with_policy(&scripts.solver_smt, config.profile) {
            Ok(run) if run.final_run.result == qbe_smt::SolverResult::Unsat => {
                record_outcome(VerificationOutcomeRecord {
                    kind: VerificationKind::ModelInvariant,
                    obligation_id: invariant.function_name.clone(),
                    caller: invariant.function_name.clone(),
                    callee: None,
                    invariant_key: Some(invariant.key.clone()),
                    outcome: verification_outcome_from_solver_result(run.final_run.result),
                    fixture: None,
                });
                if !cached_summary_match && config.cache_writes_enabled() {
                    summary.persist_unsat(&config.cache_root)?;
                }
            }
            Ok(run) if run.final_run.result == qbe_smt::SolverResult::Sat => {
                record_outcome(VerificationOutcomeRecord {
                    kind: VerificationKind::ModelInvariant,
                    obligation_id: invariant.function_name.clone(),
                    caller: invariant.function_name.clone(),
                    callee: None,
                    invariant_key: Some(invariant.key.clone()),
                    outcome: verification_outcome_from_solver_result(run.final_run.result),
                    fixture: None,
                });
                let solver_excerpt =
                    summarize_solver_output(&run.final_run.stdout, &run.final_run.stderr)
                        .map(|excerpt| format!(", solver_excerpt={excerpt}"))
                        .unwrap_or_default();
                let cache_excerpt =
                    if cached_summary_match && config.cache_mode == VerificationCacheMode::Strict {
                        ", cached_summary_revalidation=mismatch"
                    } else {
                        ""
                    };
                failures.push(format!(
                    "{} (function={}, invariant=\"{}\", qbe_artifact={}, smt_artifact={}{}{})",
                    invariant.function_name,
                    invariant.function_name,
                    render_invariant_label(invariant),
                    qbe_filename,
                    smt_filename,
                    cache_excerpt,
                    solver_excerpt
                ));
            }
            Ok(run) => {
                record_outcome(VerificationOutcomeRecord {
                    kind: VerificationKind::ModelInvariant,
                    obligation_id: invariant.function_name.clone(),
                    caller: invariant.function_name.clone(),
                    callee: None,
                    invariant_key: Some(invariant.key.clone()),
                    outcome: verification_outcome_from_solver_result(run.final_run.result),
                    fixture: None,
                });
                let solver_excerpt =
                    summarize_solver_output(&run.final_run.stdout, &run.final_run.stderr)
                        .map(|excerpt| format!(", solver_excerpt={excerpt}"))
                        .unwrap_or_default();
                let attempts = format_attempts(&run.attempts);
                let cache_excerpt =
                    if cached_summary_match && config.cache_mode == VerificationCacheMode::Strict {
                        ", cached_summary_revalidation=mismatch"
                    } else {
                        ""
                    };
                return Err(anyhow::anyhow!(
                    "solver returned unknown for model invariant obligation {} (function={}, invariant=\"{}\", qbe_artifact={}, smt_artifact={}, attempts={}{}{}). verification is fail-closed until this obligation is proven unsat",
                    invariant.function_name,
                    invariant.function_name,
                    render_invariant_label(invariant),
                    qbe_filename,
                    smt_filename,
                    attempts,
                    cache_excerpt,
                    solver_excerpt
                ));
            }
            Err(err) => {
                return Err(anyhow::anyhow!(
                    "failed to solve model invariant obligation {}: {}\n{}",
                    invariant.function_name,
                    err,
                    err.render_report_plain("model-invariant-obligation")
                ))
            }
        }
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(anyhow::anyhow!(
            "model invariant verification failed (SAT counterexamples found):\n{}",
            failures.join("\n")
        ))
    }
}

fn verification_outcome_from_solver_result(result: qbe_smt::SolverResult) -> VerificationOutcome {
    match result {
        qbe_smt::SolverResult::Sat => VerificationOutcome::Sat,
        qbe_smt::SolverResult::Unsat => VerificationOutcome::Unsat,
        qbe_smt::SolverResult::Unknown => VerificationOutcome::Unknown,
    }
}

fn render_invariant_label(invariant: &ModelInvariantDefinition) -> String {
    if let Some(identifier) = &invariant.identifier {
        format!("{} (id={})", invariant.display_name, identifier)
    } else {
        invariant.display_name.clone()
    }
}

fn build_checker_module(
    program: &ResolvedProgram,
    invariant: &ModelInvariantDefinition,
    invariant_by_struct: &HashMap<String, Vec<InvariantBinding>>,
    function_map: &HashMap<String, qbe::Function>,
) -> anyhow::Result<(qbe::Module, qbe_smt::ModuleAssumptions)> {
    let function = function_map
        .get(&invariant.function_name)
        .ok_or_else(|| anyhow::anyhow!("missing QBE function {}", invariant.function_name))?;
    let mut checker = function.clone();
    checker.name = "main".to_string();
    checker.linkage = qbe::Linkage::private();
    checker.return_ty = Some(qbe::Type::Word);
    rewrite_returns_to_bad(&mut checker)?;

    let mut checker_to_program_name = HashMap::new();
    if invariant.function_name != "main" {
        checker_to_program_name.insert("main".to_string(), invariant.function_name.clone());
    }

    checker_module_with_reachable_callees(
        program,
        invariant_by_struct,
        function_map,
        &checker,
        &checker_to_program_name,
    )
}

fn rewrite_returns_to_bad(function: &mut qbe::Function) -> anyhow::Result<()> {
    let mut found_return = false;
    let mut used_temps = collect_temps_in_function(function);
    for block in &mut function.blocks {
        let mut rewritten = Vec::with_capacity(block.items.len());
        for item in std::mem::take(&mut block.items) {
            match item {
                qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Ret(Some(
                    value,
                )))) => {
                    found_return = true;
                    let bad_temp = fresh_unique_temp("mi_bad", &mut used_temps);
                    rewritten.push(qbe::BlockItem::Statement(qbe::Statement::Assign(
                        qbe::Value::Temporary(bad_temp.clone()),
                        qbe::Type::Word,
                        qbe::Instr::Cmp(qbe::Type::Word, qbe::Cmp::Eq, value, qbe::Value::Const(0)),
                    )));
                    rewritten.push(qbe::BlockItem::Statement(qbe::Statement::Volatile(
                        qbe::Instr::Ret(Some(qbe::Value::Temporary(bad_temp))),
                    )));
                }
                qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Ret(None))) => {
                    return Err(anyhow::anyhow!(
                        "model invariant checker expected Bool return but found void return in {}",
                        function.name
                    ));
                }
                other => rewritten.push(other),
            }
        }
        block.items = rewritten;
    }

    if found_return {
        Ok(())
    } else {
        Err(anyhow::anyhow!(
            "model invariant checker function {} has no return instruction",
            function.name
        ))
    }
}

fn collect_temps_in_function(function: &qbe::Function) -> HashSet<String> {
    let mut out = HashSet::new();
    for (_, value) in &function.arguments {
        collect_temp_from_value(value, &mut out);
    }
    for block in &function.blocks {
        for item in &block.items {
            if let qbe::BlockItem::Statement(statement) = item {
                collect_temps_from_statement(statement, &mut out);
            }
        }
    }
    out
}

fn collect_temps_from_statement(statement: &qbe::Statement, out: &mut HashSet<String>) {
    match statement {
        qbe::Statement::Assign(dest, _, instr) => {
            collect_temp_from_value(dest, out);
            collect_temps_from_instr(instr, out);
        }
        qbe::Statement::Volatile(instr) => {
            collect_temps_from_instr(instr, out);
        }
    }
}

fn collect_temps_from_instr(instr: &qbe::Instr, out: &mut HashSet<String>) {
    use qbe::Instr;

    match instr {
        Instr::Add(lhs, rhs)
        | Instr::Sub(lhs, rhs)
        | Instr::Mul(lhs, rhs)
        | Instr::Div(lhs, rhs)
        | Instr::Rem(lhs, rhs)
        | Instr::And(lhs, rhs)
        | Instr::Or(lhs, rhs)
        | Instr::Udiv(lhs, rhs)
        | Instr::Urem(lhs, rhs)
        | Instr::Sar(lhs, rhs)
        | Instr::Shr(lhs, rhs)
        | Instr::Shl(lhs, rhs) => {
            collect_temp_from_value(lhs, out);
            collect_temp_from_value(rhs, out);
        }
        Instr::Cmp(_, _, lhs, rhs) => {
            collect_temp_from_value(lhs, out);
            collect_temp_from_value(rhs, out);
        }
        Instr::Copy(value)
        | Instr::Cast(value)
        | Instr::Extsw(value)
        | Instr::Extuw(value)
        | Instr::Extsh(value)
        | Instr::Extuh(value)
        | Instr::Extsb(value)
        | Instr::Extub(value)
        | Instr::Exts(value)
        | Instr::Truncd(value)
        | Instr::Stosi(value)
        | Instr::Stoui(value)
        | Instr::Dtosi(value)
        | Instr::Dtoui(value)
        | Instr::Swtof(value)
        | Instr::Uwtof(value)
        | Instr::Sltof(value)
        | Instr::Ultof(value)
        | Instr::Vastart(value) => {
            collect_temp_from_value(value, out);
        }
        Instr::Ret(value) => {
            if let Some(value) = value {
                collect_temp_from_value(value, out);
            }
        }
        Instr::Jnz(value, _, _) => {
            collect_temp_from_value(value, out);
        }
        Instr::Call(_, args, _) => {
            for (_, value) in args {
                collect_temp_from_value(value, out);
            }
        }
        Instr::Store(_, destination, value) => {
            collect_temp_from_value(destination, out);
            collect_temp_from_value(value, out);
        }
        Instr::Load(_, source) => {
            collect_temp_from_value(source, out);
        }
        Instr::Blit(source, destination, _) => {
            collect_temp_from_value(source, out);
            collect_temp_from_value(destination, out);
        }
        Instr::Vaarg(_, value) => {
            collect_temp_from_value(value, out);
        }
        Instr::Phi(_, left, _, right) => {
            collect_temp_from_value(left, out);
            collect_temp_from_value(right, out);
        }
        Instr::Jmp(_)
        | Instr::Alloc4(_)
        | Instr::Alloc8(_)
        | Instr::Alloc16(_)
        | Instr::DbgFile(_)
        | Instr::DbgLoc(_, _)
        | Instr::Hlt => {}
    }
}

fn collect_temp_from_value(value: &qbe::Value, out: &mut HashSet<String>) {
    if let qbe::Value::Temporary(name) = value {
        out.insert(name.clone());
    }
}

fn fresh_unique_temp(base: &str, used: &mut HashSet<String>) -> String {
    if !used.contains(base) {
        used.insert(base.to_string());
        return base.to_string();
    }
    let mut index = 0usize;
    loop {
        let candidate = format!("{}_{}", base, index);
        if !used.contains(&candidate) {
            used.insert(candidate.clone());
            return candidate;
        }
        index += 1;
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::fs;

    use super::{
        verify_model_invariants_with_qbe, verify_model_invariants_with_qbe_with_config,
        verify_model_invariants_with_qbe_with_profile,
    };
    use crate::ir::ResolvedProgram;
    use crate::verification_cache::{
        VerificationCacheMode, VerificationCacheWritePolicy, VerificationConfig,
    };
    use crate::verification_profile::VerificationProfile;
    use crate::verification_solver::test_support;
    use crate::{ir, parser, qbe_backend, tokenizer};

    fn resolve_program(source: &str) -> ir::ResolvedProgram {
        let tokens = tokenizer::tokenize(source.to_string()).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        ir::resolve(ast).expect("resolve source")
    }

    fn run(result: qbe_smt::SolverResult, stdout: &str, stderr: &str) -> qbe_smt::SolverRun {
        qbe_smt::SolverRun {
            result,
            stdout: stdout.to_string(),
            stderr: stderr.to_string(),
        }
    }

    fn retain_model_invariants_by_display_name(program: &mut ResolvedProgram, names: &[&str]) {
        let wanted = names.iter().copied().collect::<HashSet<_>>();
        program
            .model_invariants
            .retain(|model| wanted.contains(model.display_name.as_str()));
    }

    fn config(root: &std::path::Path, mode: VerificationCacheMode) -> VerificationConfig {
        VerificationConfig::new(
            VerificationProfile::Candidate,
            mode,
            root.join("verification_cache"),
            VerificationCacheWritePolicy::PersistUnsat,
        )
    }

    fn model_cache_entry_count(cache_root: &std::path::Path, root_name: &str) -> usize {
        let dir = cache_root
            .join("model_invariant_function")
            .join(crate::verification_checker::sanitize_ident(root_name));
        if !dir.exists() {
            return 0;
        }
        fs::read_dir(dir)
            .expect("read model invariant cache dir")
            .filter_map(|entry| entry.ok().map(|entry| entry.path()))
            .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("json"))
            .count()
    }

    #[test]
    fn no_model_invariants_is_noop() {
        let source = r#"
fun main() -> I32 {
	return 0
}
"#;
        let mut program = resolve_program(source);
        program.model_invariants.clear();
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        verify_model_invariants_with_qbe(&program, &qbe_module, tempdir.path())
            .expect("no model invariants should pass");
    }

    #[test]
    fn verifies_model_invariants_even_when_unreachable_from_main() {
        let source = r#"
invariant "pair is ordered" for (lhs: I32, rhs: I32) {
	return lhs <= rhs
}

fun main() -> I32 {
	return 0
}
"#;
        let mut program = resolve_program(source);
        retain_model_invariants_by_display_name(&mut program, &["pair is ordered"]);
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        let function_name = program.model_invariants[0].function_name.clone();
        test_support::with_mock_solver_runs(
            vec![Ok(run(qbe_smt::SolverResult::Sat, "sat", ""))],
            || {
                let err = verify_model_invariants_with_qbe_with_profile(
                    &program,
                    &qbe_module,
                    tempdir.path(),
                    VerificationProfile::Baseline,
                )
                .expect_err("SAT model invariant must fail");
                let message = err.to_string();
                assert!(message.contains("model invariant verification failed"));
                assert!(message.contains(&function_name));
            },
        );
    }

    #[test]
    fn unknown_model_invariants_fail_closed_with_attempt_ladder() {
        let source = r#"
invariant "pair is ordered" for (lhs: I32, rhs: I32) {
	return lhs <= rhs
}

fun main() -> I32 {
	return 0
}
"#;
        let mut program = resolve_program(source);
        retain_model_invariants_by_display_name(&mut program, &["pair is ordered"]);
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        test_support::with_mock_solver_runs(
            vec![
                Ok(run(
                    qbe_smt::SolverResult::Unknown,
                    "unknown\n(reason-unknown timeout)",
                    "",
                )),
                Ok(run(
                    qbe_smt::SolverResult::Unknown,
                    "unknown\n(reason-unknown timeout)",
                    "",
                )),
            ],
            || {
                let err = verify_model_invariants_with_qbe_with_profile(
                    &program,
                    &qbe_module,
                    tempdir.path(),
                    VerificationProfile::Baseline,
                )
                .expect_err("unknown model invariants must fail closed");
                let message = err.to_string();
                assert!(message.contains("solver returned unknown for model invariant obligation"));
                assert!(message.contains("attempts=[10s:unknown"));
            },
        );
    }

    #[test]
    fn model_invariant_cache_trust_hit_skips_solver() {
        let source = r#"
invariant "pair is ordered" for (lhs: I32, rhs: I32) {
	return lhs <= rhs
}

fun main() -> I32 {
	return 0
}
"#;
        let mut program = resolve_program(source);
        retain_model_invariants_by_display_name(&mut program, &["pair is ordered"]);
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        let config = config(tempdir.path(), VerificationCacheMode::Trust);
        let function_name = program.model_invariants[0].function_name.clone();

        test_support::with_mock_solver_runs(
            vec![Ok(run(qbe_smt::SolverResult::Unsat, "unsat", ""))],
            || {
                verify_model_invariants_with_qbe_with_config(
                    &program,
                    &qbe_module,
                    tempdir.path(),
                    config.clone(),
                )
                .expect("first verification should populate the cache");
            },
        );
        assert_eq!(
            model_cache_entry_count(&config.cache_root, &function_name),
            1
        );

        test_support::with_mock_solver_runs(vec![], || {
            verify_model_invariants_with_qbe_with_config(
                &program,
                &qbe_module,
                tempdir.path(),
                config.clone(),
            )
            .expect("trusted cache hit should skip solver invocations");
            assert!(
                test_support::observed_timeouts().is_empty(),
                "trusted model-invariant cache hit should not invoke the solver"
            );
        });
    }

    #[test]
    fn model_invariant_strict_cache_mismatch_fails_closed() {
        let source = r#"
invariant "pair is ordered" for (lhs: I32, rhs: I32) {
	return lhs <= rhs
}

fun main() -> I32 {
	return 0
}
"#;
        let mut program = resolve_program(source);
        retain_model_invariants_by_display_name(&mut program, &["pair is ordered"]);
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        let trust_config = config(tempdir.path(), VerificationCacheMode::Trust);

        test_support::with_mock_solver_runs(
            vec![Ok(run(qbe_smt::SolverResult::Unsat, "unsat", ""))],
            || {
                verify_model_invariants_with_qbe_with_config(
                    &program,
                    &qbe_module,
                    tempdir.path(),
                    trust_config.clone(),
                )
                .expect("first verification should populate the cache");
            },
        );

        let strict_config = config(tempdir.path(), VerificationCacheMode::Strict);
        test_support::with_mock_solver_runs(
            vec![Ok(run(qbe_smt::SolverResult::Sat, "sat", ""))],
            || {
                let err = verify_model_invariants_with_qbe_with_config(
                    &program,
                    &qbe_module,
                    tempdir.path(),
                    strict_config.clone(),
                )
                .expect_err("strict cache mismatch must fail closed");
                assert!(err
                    .to_string()
                    .contains("cached_summary_revalidation=mismatch"));
            },
        );
    }

    #[test]
    fn model_invariants_apply_struct_argument_invariant_assumptions() {
        let source = r#"
struct Counter {
	value: I32,
}

invariant positive_value "counter value must stay non-negative" for (v: Counter) {
	return v.value >= 0
}

invariant "pair counters stay non-negative" for (lhs: Counter, rhs: Counter) {
	return lhs.value >= 0 && rhs.value >= 0
}

fun main() -> I32 {
	return 0
}
"#;
        let mut program = resolve_program(source);
        retain_model_invariants_by_display_name(&mut program, &["pair counters stay non-negative"]);
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        test_support::with_mock_solver_runs(
            vec![Ok(run(qbe_smt::SolverResult::Unsat, "unsat", ""))],
            || {
                verify_model_invariants_with_qbe_with_profile(
                    &program,
                    &qbe_module,
                    tempdir.path(),
                    VerificationProfile::Baseline,
                )
                .expect("model invariant with struct argument assumptions should verify");
            },
        );

        let artifacts = std::fs::read_dir(tempdir.path().join("model_invariants"))
            .expect("read model invariant artifacts")
            .filter_map(|entry| entry.ok().map(|entry| entry.path()))
            .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("smt2"))
            .collect::<Vec<_>>();
        assert_eq!(
            artifacts.len(),
            1,
            "expected one model invariant SMT artifact"
        );

        let smt = std::fs::read_to_string(&artifacts[0]).expect("read smt artifact");
        let assumption_count = smt.matches("(distinct arg_inv_ret_").count();
        assert!(
            assumption_count >= 2,
            "expected struct invariant assumptions for both Counter parameters, saw {assumption_count}: {smt}"
        );
    }

    #[test]
    fn rejects_cycles_introduced_by_argument_invariant_edges() {
        let source = r#"
struct Counter {
	value: I32,
}

invariant positive_value "counter value must stay non-negative" for (v: Counter) {
	return __model__invariant__pair_total(v, v)
}

invariant pair_total "pair is always comparable" for (lhs: Counter, rhs: Counter) {
	return lhs.value <= rhs.value || rhs.value <= lhs.value
}

fun main() -> I32 {
	return 0
}
"#;
        let mut program = resolve_program(source);
        retain_model_invariants_by_display_name(
            &mut program,
            &[
                "counter value must stay non-negative",
                "pair is always comparable",
            ],
        );
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        let err = verify_model_invariants_with_qbe_with_profile(
            &program,
            &qbe_module,
            tempdir.path(),
            VerificationProfile::Baseline,
        )
        .expect_err("arg-invariant cycle should fail closed");
        assert!(err.to_string().contains("includes entry-assumption edges"));
    }
}
