use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::Path;

use anyhow::Context;

use crate::ast_walk::{self, AstPathStyle};
use crate::invariant_metadata::{
    build_function_arg_invariant_assumptions_for_names, discover_struct_invariant_bindings,
    InvariantBinding,
};
use crate::ir::ResolvedProgram;
use crate::parser::Statement;
use crate::precondition_metadata::build_function_precondition_assumptions_for_names;
use crate::verification_cache::{
    VerificationCacheMode, VerificationCacheWritePolicy, VerificationConfig,
    VerificationSummaryCandidate, VerificationSummaryInput, VerificationSummaryKind,
};
use crate::verification_checker::{
    checker_module_with_reachable_callees, prune_function_to_target, rewrite_returns_to_zero,
    sanitize_ident, should_assume_main_argc_non_negative, summarize_solver_output,
};
use crate::verification_cycles::{
    reachable_user_functions, reject_recursion_cycles_with_entry_assumptions,
};
use crate::verification_outcomes::{
    record_outcome, VerificationKind, VerificationOutcome, VerificationOutcomeRecord,
};
use crate::verification_profile::VerificationProfile;
use crate::verification_solver::{format_attempts, solve_chc_with_policy};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct VerificationRoot {
    function_name: String,
    summary_kind: VerificationSummaryKind,
}

#[derive(Clone, Debug)]
struct FunctionPreconditionSite {
    id: String,
    root_name: String,
    summary_kind: VerificationSummaryKind,
    caller: String,
    callee: String,
    callee_call_ordinal: usize,
    clause_ordinal: usize,
    helper_function_name: String,
}

#[derive(Clone, Debug)]
pub(crate) struct PreparedFunctionPreconditionSite {
    site: FunctionPreconditionSite,
    qbe_filename: String,
    smt_filename: String,
    smt: String,
}

impl PreparedFunctionPreconditionSite {
    pub(crate) fn root_name(&self) -> &str {
        &self.site.root_name
    }

    pub(crate) fn summary_kind(&self) -> VerificationSummaryKind {
        self.site.summary_kind
    }

    pub(crate) fn summary_input(&self) -> VerificationSummaryInput {
        VerificationSummaryInput {
            kind: VerificationKind::Precondition,
            local_id: self.site.id.clone(),
            smt: self.smt.clone(),
        }
    }
}

#[allow(dead_code)]
pub(crate) fn verify_function_preconditions_with_qbe(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
) -> anyhow::Result<()> {
    verify_function_preconditions_with_qbe_with_profile(
        program,
        qbe_module,
        target_dir,
        VerificationProfile::default(),
    )
}

#[allow(dead_code)]
pub(crate) fn verify_function_preconditions_with_qbe_with_profile(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
    profile: VerificationProfile,
) -> anyhow::Result<()> {
    verify_function_preconditions_with_qbe_with_config(
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

pub(crate) fn verify_function_preconditions_with_qbe_with_config(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
    config: VerificationConfig,
) -> anyhow::Result<()> {
    let prepared =
        prepare_function_preconditions_with_config(program, qbe_module, target_dir, &config)?;
    verify_prepared_function_preconditions(&prepared, &config, &HashSet::new())
}

pub(crate) fn prepare_function_preconditions_with_config(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
    _config: &VerificationConfig,
) -> anyhow::Result<Vec<PreparedFunctionPreconditionSite>> {
    let invariant_by_struct = discover_struct_invariant_bindings(program)?;
    let roots = collect_verification_roots(program, &invariant_by_struct);
    if roots.is_empty() {
        return Ok(Vec::new());
    }

    let function_map = qbe_module
        .functions
        .iter()
        .map(|function| (function.name.clone(), function.clone()))
        .collect::<HashMap<_, _>>();

    let verification_dir = target_dir.join("preconditions");
    std::fs::create_dir_all(&verification_dir).with_context(|| {
        format!(
            "failed to create precondition verification directory {}",
            verification_dir.display()
        )
    })?;

    let mut prepared = Vec::new();
    for root in roots {
        let reachable = reachable_user_functions(program, &root.function_name)?;
        let sites = collect_precondition_sites(program, &reachable, &root)?;
        if sites.is_empty() {
            continue;
        }

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
            &root.function_name,
            &reachable,
            &arg_invariant_assumptions,
            &function_precondition_assumptions,
            "function precondition verification",
        )?;

        for site in sites {
            let (checker_module, checker_function, assumptions) =
                build_site_checker_module(program, &invariant_by_struct, &function_map, &site)?;
            let checker_qbe = checker_module.to_string();
            let site_stem = format!("site_{}", sanitize_ident(&site.id));
            let qbe_filename = format!("{}.qbe", site_stem);
            let smt_filename = format!("{}.smt2", site_stem);

            let qbe_path = verification_dir.join(&qbe_filename);
            std::fs::write(&qbe_path, &checker_qbe).with_context(|| {
                format!(
                    "failed to write function precondition checker QBE program {}",
                    qbe_path.display()
                )
            })?;

            let smt = qbe_smt::qbe_module_to_smt_with_assumptions(
                &checker_module,
                "main",
                &qbe_smt::EncodeOptions {
                    assume_main_argc_non_negative: should_assume_main_argc_non_negative(
                        &site.root_name,
                        &checker_function,
                    ),
                    first_arg_i32_range: None,
                },
                &assumptions,
            )
            .map_err(|err| {
                anyhow::anyhow!(
                    "failed to encode function precondition checker QBE for {}: {}\n{}",
                    site.id,
                    err,
                    err.render_report_plain("precondition-checker")
                )
            })?;

            let smt_path = verification_dir.join(&smt_filename);
            std::fs::write(&smt_path, &smt).with_context(|| {
                format!(
                    "failed to write function precondition SMT obligation {}",
                    smt_path.display()
                )
            })?;

            prepared.push(PreparedFunctionPreconditionSite {
                site,
                qbe_filename,
                smt_filename,
                smt,
            });
        }
    }

    prepared.sort_by(|lhs, rhs| lhs.site.id.cmp(&rhs.site.id));
    Ok(prepared)
}

pub(crate) fn verify_prepared_function_preconditions(
    prepared_sites: &[PreparedFunctionPreconditionSite],
    config: &VerificationConfig,
    cached_ordinary_roots: &HashSet<String>,
) -> anyhow::Result<()> {
    let model_summaries = build_model_summary_candidates(prepared_sites);
    let mut matched_model_summaries = HashSet::<String>::new();

    if config.cache_reads_enabled() {
        for (root_name, summary) in &model_summaries {
            if summary.matches_persisted_unsat(&config.cache_root)? {
                matched_model_summaries.insert(root_name.clone());
            }
        }
    }

    let mut sat_failures = Vec::new();
    let mut model_roots_with_non_unsat = HashSet::<String>::new();

    for prepared in prepared_sites {
        let trust_skip = match prepared.summary_kind() {
            VerificationSummaryKind::OrdinaryFunction => {
                config.cache_trust_enabled() && cached_ordinary_roots.contains(prepared.root_name())
            }
            VerificationSummaryKind::ModelInvariantFunction => {
                config.cache_trust_enabled()
                    && matched_model_summaries.contains(prepared.root_name())
            }
        };
        if trust_skip {
            record_outcome(VerificationOutcomeRecord {
                kind: VerificationKind::Precondition,
                obligation_id: prepared.site.id.clone(),
                caller: prepared.site.caller.clone(),
                callee: Some(prepared.site.callee.clone()),
                invariant_key: None,
                outcome: VerificationOutcome::Unsat,
                fixture: None,
            });
            continue;
        }

        let strict_cache_mismatch = config.cache_mode == VerificationCacheMode::Strict
            && match prepared.summary_kind() {
                VerificationSummaryKind::OrdinaryFunction => {
                    cached_ordinary_roots.contains(prepared.root_name())
                }
                VerificationSummaryKind::ModelInvariantFunction => {
                    matched_model_summaries.contains(prepared.root_name())
                }
            };

        match solve_chc_with_policy(&prepared.smt, config.profile) {
            Ok(run) if run.final_run.result == qbe_smt::SolverResult::Unsat => {
                record_outcome(VerificationOutcomeRecord {
                    kind: VerificationKind::Precondition,
                    obligation_id: prepared.site.id.clone(),
                    caller: prepared.site.caller.clone(),
                    callee: Some(prepared.site.callee.clone()),
                    invariant_key: None,
                    outcome: verification_outcome_from_solver_result(run.final_run.result),
                    fixture: None,
                });
            }
            Ok(run) if run.final_run.result == qbe_smt::SolverResult::Sat => {
                record_outcome(VerificationOutcomeRecord {
                    kind: VerificationKind::Precondition,
                    obligation_id: prepared.site.id.clone(),
                    caller: prepared.site.caller.clone(),
                    callee: Some(prepared.site.callee.clone()),
                    invariant_key: None,
                    outcome: verification_outcome_from_solver_result(run.final_run.result),
                    fixture: None,
                });
                if prepared.summary_kind() == VerificationSummaryKind::ModelInvariantFunction {
                    model_roots_with_non_unsat.insert(prepared.root_name().to_string());
                }
                let solver_excerpt =
                    summarize_solver_output(&run.final_run.stdout, &run.final_run.stderr)
                        .map(|excerpt| format!(", solver_excerpt={excerpt}"))
                        .unwrap_or_default();
                let cache_excerpt = if strict_cache_mismatch {
                    ", cached_summary_revalidation=mismatch"
                } else {
                    ""
                };
                sat_failures.push(format!(
                    "{} (root={}, caller={}, callee={}, clause={}, qbe_artifact={}, smt_artifact={}{}{})",
                    prepared.site.id,
                    prepared.site.root_name,
                    prepared.site.caller,
                    prepared.site.callee,
                    prepared.site.clause_ordinal,
                    prepared.qbe_filename,
                    prepared.smt_filename,
                    cache_excerpt,
                    solver_excerpt
                ));
            }
            Ok(run) => {
                record_outcome(VerificationOutcomeRecord {
                    kind: VerificationKind::Precondition,
                    obligation_id: prepared.site.id.clone(),
                    caller: prepared.site.caller.clone(),
                    callee: Some(prepared.site.callee.clone()),
                    invariant_key: None,
                    outcome: verification_outcome_from_solver_result(run.final_run.result),
                    fixture: None,
                });
                if prepared.summary_kind() == VerificationSummaryKind::ModelInvariantFunction {
                    model_roots_with_non_unsat.insert(prepared.root_name().to_string());
                }
                let solver_excerpt =
                    summarize_solver_output(&run.final_run.stdout, &run.final_run.stderr)
                        .map(|excerpt| format!(", solver_excerpt={excerpt}"))
                        .unwrap_or_default();
                let attempts = format_attempts(&run.attempts);
                let cache_excerpt = if strict_cache_mismatch {
                    ", cached_summary_revalidation=mismatch"
                } else {
                    ""
                };
                return Err(anyhow::anyhow!(
                    "solver returned unknown for function precondition obligation {} (root={}, caller={}, callee={}, clause={}, qbe_artifact={}, smt_artifact={}, attempts={}{}{}). verification is fail-closed until this obligation is proven unsat",
                    prepared.site.id,
                    prepared.site.root_name,
                    prepared.site.caller,
                    prepared.site.callee,
                    prepared.site.clause_ordinal,
                    prepared.qbe_filename,
                    prepared.smt_filename,
                    attempts,
                    cache_excerpt,
                    solver_excerpt
                ));
            }
            Err(err) => {
                return Err(anyhow::anyhow!(
                    "failed to solve function precondition obligation {}: {}\n{}",
                    prepared.site.id,
                    err,
                    err.render_report_plain("function-precondition-obligation")
                ))
            }
        }
    }

    if config.cache_writes_enabled() {
        for (root_name, summary) in &model_summaries {
            if matched_model_summaries.contains(root_name)
                || model_roots_with_non_unsat.contains(root_name)
            {
                continue;
            }
            summary.persist_unsat(&config.cache_root)?;
        }
    }

    if sat_failures.is_empty() {
        Ok(())
    } else {
        Err(anyhow::anyhow!(
            "function precondition verification failed (SAT counterexamples found):\n{}",
            sat_failures.join("\n")
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

fn build_model_summary_candidates(
    prepared_sites: &[PreparedFunctionPreconditionSite],
) -> BTreeMap<String, VerificationSummaryCandidate> {
    let mut inputs_by_root = BTreeMap::<String, Vec<VerificationSummaryInput>>::new();
    for prepared in prepared_sites {
        if prepared.summary_kind() != VerificationSummaryKind::ModelInvariantFunction {
            continue;
        }
        inputs_by_root
            .entry(prepared.root_name().to_string())
            .or_default()
            .push(prepared.summary_input());
    }

    inputs_by_root
        .into_iter()
        .map(|(root_name, inputs)| {
            (
                root_name.clone(),
                VerificationSummaryCandidate::from_inputs(
                    &root_name,
                    VerificationSummaryKind::ModelInvariantFunction,
                    &inputs,
                ),
            )
        })
        .collect()
}

fn collect_verification_roots(
    program: &ResolvedProgram,
    invariant_by_struct: &HashMap<String, Vec<InvariantBinding>>,
) -> Vec<VerificationRoot> {
    let mut roots = BTreeSet::<VerificationRoot>::new();
    if program.function_definitions.contains_key("main") {
        roots.insert(VerificationRoot {
            function_name: "main".to_string(),
            summary_kind: VerificationSummaryKind::OrdinaryFunction,
        });
    }
    for function_name in invariant_by_struct.values().flat_map(|bindings| {
        bindings
            .iter()
            .map(|binding| binding.function_name.to_string())
    }) {
        roots.insert(VerificationRoot {
            function_name,
            summary_kind: VerificationSummaryKind::OrdinaryFunction,
        });
    }
    for function_name in program
        .function_preconditions
        .values()
        .flat_map(|definitions| {
            definitions
                .iter()
                .map(|definition| definition.helper_function_name.to_string())
        })
    {
        roots.insert(VerificationRoot {
            function_name,
            summary_kind: VerificationSummaryKind::OrdinaryFunction,
        });
    }
    for invariant in &program.model_invariants {
        roots.insert(VerificationRoot {
            function_name: invariant.function_name.clone(),
            summary_kind: VerificationSummaryKind::ModelInvariantFunction,
        });
    }
    roots.into_iter().collect()
}

fn collect_precondition_sites(
    program: &ResolvedProgram,
    reachable: &HashSet<String>,
    root: &VerificationRoot,
) -> anyhow::Result<Vec<FunctionPreconditionSite>> {
    let mut sites = Vec::new();
    let mut functions = reachable.iter().cloned().collect::<Vec<_>>();
    functions.sort();

    for function_name in functions {
        let function = program
            .function_definitions
            .get(&function_name)
            .ok_or_else(|| anyhow::anyhow!("missing function definition for {}", function_name))?;

        let mut callee_ordinals = HashMap::<String, usize>::new();
        for (top_statement_index, statement) in function.body.iter().enumerate() {
            let mut expr_index_map = HashMap::new();
            let mut expr_index = 0usize;
            index_statement_expressions(statement, "", &mut expr_index, &mut expr_index_map);

            let mut call_nodes = Vec::new();
            collect_call_nodes_from_statement(statement, "", &mut call_nodes);

            for (expr_path, callee_name) in call_nodes {
                let current_ordinal = *callee_ordinals.entry(callee_name.clone()).or_insert(0);
                if let Some(entry) = callee_ordinals.get_mut(&callee_name) {
                    *entry += 1;
                }

                if !program.function_definitions.contains_key(&callee_name) {
                    continue;
                }
                let Some(definitions) = program.function_preconditions.get(&callee_name) else {
                    continue;
                };
                let expr_index = *expr_index_map.get(&expr_path).ok_or_else(|| {
                    anyhow::anyhow!("missing expression index for path {}", expr_path)
                })?;

                for definition in definitions {
                    let id = format!(
                        "{}#{}#{}#{}#pre_{}",
                        root.function_name,
                        function_name,
                        top_statement_index,
                        expr_index,
                        definition.clause_ordinal
                    );
                    sites.push(FunctionPreconditionSite {
                        id,
                        root_name: root.function_name.clone(),
                        summary_kind: root.summary_kind,
                        caller: function_name.clone(),
                        callee: callee_name.clone(),
                        callee_call_ordinal: current_ordinal,
                        clause_ordinal: definition.clause_ordinal,
                        helper_function_name: definition.helper_function_name.clone(),
                    });
                }
            }
        }
    }

    sites.sort_by(|lhs, rhs| lhs.id.cmp(&rhs.id));
    Ok(sites)
}

fn index_statement_expressions(
    statement: &Statement,
    statement_path: &str,
    next_index: &mut usize,
    out: &mut HashMap<String, usize>,
) {
    ast_walk::walk_statement_expressions(
        statement,
        statement_path,
        AstPathStyle::StructInvariants,
        &mut |expression_path, _| {
            out.insert(expression_path.to_string(), *next_index);
            *next_index += 1;
        },
    );
}

fn collect_call_nodes_from_statement(
    statement: &Statement,
    statement_path: &str,
    out: &mut Vec<(String, String)>,
) {
    ast_walk::walk_statement_calls(
        statement,
        statement_path,
        AstPathStyle::StructInvariants,
        &mut |expression_path, call_name| {
            out.push((expression_path.to_string(), call_name.to_string()));
        },
    );
}

fn build_site_checker_module(
    program: &ResolvedProgram,
    invariant_by_struct: &HashMap<String, Vec<InvariantBinding>>,
    function_map: &HashMap<String, qbe::Function>,
    site: &FunctionPreconditionSite,
) -> anyhow::Result<(qbe::Module, qbe::Function, qbe_smt::ModuleAssumptions)> {
    let caller = function_map
        .get(&site.caller)
        .ok_or_else(|| anyhow::anyhow!("missing QBE function for caller {}", site.caller))?;
    let mut checker = caller.clone();
    checker.name = "main".to_string();
    checker.linkage = qbe::Linkage::private();
    checker.return_ty = Some(qbe::Type::Word);

    rewrite_returns_to_zero(&mut checker);
    inject_site_check_and_return(&mut checker, site)?;

    let mut checker_to_program_name = HashMap::new();
    if site.caller != "main" {
        checker_to_program_name.insert("main".to_string(), site.caller.clone());
    }

    let (module, assumptions) = checker_module_with_reachable_callees(
        program,
        invariant_by_struct,
        function_map,
        &checker,
        &checker_to_program_name,
    )?;
    Ok((module, checker, assumptions))
}

fn inject_site_check_and_return(
    function: &mut qbe::Function,
    site: &FunctionPreconditionSite,
) -> anyhow::Result<()> {
    let mut call_count = 0usize;
    let mut used_temps = collect_temps_in_function(function);
    let mut target = None::<(usize, usize, Vec<(qbe::Type, qbe::Value)>)>;

    for (block_index, block) in function.blocks.iter().enumerate() {
        for item_index in 0..block.items.len() {
            let call_info = match &block.items[item_index] {
                qbe::BlockItem::Statement(qbe::Statement::Assign(
                    _dest,
                    _ty,
                    qbe::Instr::Call(name, args, variadic_index),
                )) => {
                    if name == &site.callee {
                        Some((args.clone(), *variadic_index))
                    } else {
                        None
                    }
                }
                qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Call(
                    name,
                    args,
                    variadic_index,
                ))) => {
                    if name == &site.callee {
                        Some((args.clone(), *variadic_index))
                    } else {
                        None
                    }
                }
                _ => None,
            };

            let Some((args, variadic_index)) = call_info else {
                continue;
            };

            if call_count == site.callee_call_ordinal {
                if variadic_index.is_some() {
                    return Err(anyhow::anyhow!(
                        "unsupported variadic call at function precondition site {}",
                        site.id
                    ));
                }
                target = Some((block_index, item_index, args));
                break;
            }

            call_count += 1;
        }

        if target.is_some() {
            break;
        }
    }

    let Some((target_block_index, target_item_index, args)) = target else {
        return Err(anyhow::anyhow!(
            "failed to locate QBE call for function precondition site {} (callee={}, ordinal={})",
            site.id,
            site.callee,
            site.callee_call_ordinal
        ));
    };

    prune_function_to_target(function, target_block_index);

    let pre_temp = fresh_unique_temp("pre_ret", &mut used_temps);
    let bad_temp = fresh_unique_temp("pre_bad", &mut used_temps);
    let block = &mut function.blocks[target_block_index];
    let mut new_items = block.items[..target_item_index].to_vec();
    new_items.push(qbe::BlockItem::Statement(qbe::Statement::Assign(
        qbe::Value::Temporary(pre_temp.clone()),
        qbe::Type::Word,
        qbe::Instr::Call(site.helper_function_name.clone(), args, None),
    )));
    new_items.push(qbe::BlockItem::Statement(qbe::Statement::Assign(
        qbe::Value::Temporary(bad_temp.clone()),
        qbe::Type::Word,
        qbe::Instr::Cmp(
            qbe::Type::Word,
            qbe::Cmp::Eq,
            qbe::Value::Temporary(pre_temp),
            qbe::Value::Const(0),
        ),
    )));
    new_items.push(qbe::BlockItem::Statement(qbe::Statement::Volatile(
        qbe::Instr::Ret(Some(qbe::Value::Temporary(bad_temp))),
    )));
    block.items = new_items;
    Ok(())
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
    use super::{
        prepare_function_preconditions_with_config, verify_function_preconditions_with_qbe,
    };
    use crate::verification_cache::{
        VerificationCacheMode, VerificationCacheWritePolicy, VerificationConfig,
        VerificationSummaryKind,
    };
    use crate::verification_profile::VerificationProfile;
    use crate::{ir, parser, qbe_backend, tokenizer};

    fn resolve_program(source: &str) -> ir::ResolvedProgram {
        let tokens = tokenizer::tokenize(source.to_string()).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        ir::resolve(ast).expect("resolve source")
    }

    fn config(root: &std::path::Path) -> VerificationConfig {
        VerificationConfig::new(
            VerificationProfile::Candidate,
            VerificationCacheMode::Off,
            root.join("verification_cache"),
            VerificationCacheWritePolicy::PersistUnsat,
        )
    }

    #[test]
    fn precondition_verification_passes_for_satisfied_callsites() {
        let program = resolve_program(
            r#"
fun guarded(x: I32) -> I32 pre {
	x > 5
} {
	return x
}

fun main() -> I32 {
	return guarded(7)
}
"#,
        );
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        verify_function_preconditions_with_qbe(&program, &qbe_module, tempdir.path())
            .expect("satisfied precondition callsites should verify");
    }

    #[test]
    fn precondition_verification_fails_for_unsatisfied_callsites() {
        let program = resolve_program(
            r#"
fun guarded(x: I32) -> I32 pre {
	x > 5
} {
	return x
}

fun main() -> I32 {
	return guarded(3)
}
"#,
        );
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        let err = verify_function_preconditions_with_qbe(&program, &qbe_module, tempdir.path())
            .expect_err("unsatisfied precondition callsites must fail");
        let message = err.to_string();
        assert!(message.contains("function precondition verification failed"));
        assert!(message.contains("caller=main"));
        assert!(message.contains("callee=guarded"));
        assert!(message.contains("clause=0"));
    }

    #[test]
    fn precondition_helpers_are_checked_as_ordinary_roots() {
        let program = resolve_program(
            r#"
fun predicate(x: I32) -> Bool pre {
	x > 100
} {
	return true
}

fun guarded(x: I32) -> I32 pre {
	predicate(x)
} {
	return x
}

fun main() -> I32 {
	return guarded(7)
}
"#,
        );
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        let err = verify_function_preconditions_with_qbe(&program, &qbe_module, tempdir.path())
            .expect_err("transitive precondition calls from synthesized helpers must be checked");
        let message = err.to_string();
        assert!(message.contains("callee=predicate"));
        assert!(message.contains("caller=__pre__guarded__clause_0"));
    }

    #[test]
    fn precondition_verification_checks_model_invariant_roots() {
        let program = resolve_program(
            r#"
fun guarded(x: I32) -> I32 pre {
	x > 5
} {
	return x
}

invariant constant_call "constant call must satisfy guard" for (lhs: I32, rhs: I32) {
	return guarded(3) == guarded(3)
}

fun main() -> I32 {
	return 0
}
"#,
        );
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        let err = verify_function_preconditions_with_qbe(&program, &qbe_module, tempdir.path())
            .expect_err("model invariant roots must enforce callee preconditions");
        let message = err.to_string();
        assert!(message.contains("root=__model__invariant__constant_call"));
        assert!(message.contains("callee=guarded"));
    }

    #[test]
    fn prepare_function_preconditions_collects_multiclause_sites() {
        let program = resolve_program(
            r#"
fun guarded(x: I32) -> I32 pre {
	x > 5
	x < 20
} {
	return x
}

invariant constant_call "constant call must satisfy guard" for (lhs: I32, rhs: I32) {
	return guarded(10) == guarded(10)
}

fun main() -> I32 {
	return guarded(10)
}
"#,
        );
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        let prepared = prepare_function_preconditions_with_config(
            &program,
            &qbe_module,
            tempdir.path(),
            &config(tempdir.path()),
        )
        .expect("prepare precondition obligations");

        let ordinary = prepared
            .iter()
            .filter(|prepared| prepared.summary_kind() == VerificationSummaryKind::OrdinaryFunction)
            .count();
        let model = prepared
            .iter()
            .filter(|prepared| {
                prepared.summary_kind() == VerificationSummaryKind::ModelInvariantFunction
            })
            .count();

        assert!(
            ordinary >= 2,
            "expected ordinary-root multiclause obligations"
        );
        assert!(model >= 2, "expected model-root multiclause obligations");
    }
}
