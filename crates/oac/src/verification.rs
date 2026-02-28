use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::Path;

use anyhow::Context;

use crate::ir::ResolvedProgram;
use crate::parser::{Expression, Statement};

const Z3_TIMEOUT_SECONDS: u64 = 10;

#[derive(Debug)]
pub enum VerificationError {
    Prove(anyhow::Error),
    StructInvariant(anyhow::Error),
}

#[derive(Clone, Debug)]
pub(crate) struct VerificationContext {
    pub(crate) reachable: HashSet<String>,
    pub(crate) function_map: HashMap<String, qbe::Function>,
}

#[derive(Clone, Copy)]
pub(crate) struct ObligationBatchConfig<'a> {
    pub verification_subdir: &'a str,
    pub create_dir_error_prefix: &'a str,
    pub write_qbe_error_prefix: &'a str,
    pub write_smt_error_prefix: &'a str,
    pub encode_error_prefix: &'a str,
    pub encode_report_name: &'a str,
    pub unknown_error_prefix: &'a str,
    pub solve_error_prefix: &'a str,
    pub solve_report_name: &'a str,
    pub sat_failure_header: &'a str,
}

pub fn verify_all_obligations_with_qbe(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
) -> Result<(), VerificationError> {
    let context =
        build_verification_context(program, qbe_module).map_err(VerificationError::Prove)?;

    let prove_sites = crate::prove::collect_prove_sites(&context.function_map, &context.reachable)
        .map_err(VerificationError::Prove)?;
    let invariant_by_struct = crate::struct_invariants::discover_invariants(program)
        .map_err(VerificationError::StructInvariant)?;
    let invariant_sites = crate::struct_invariants::collect_obligation_sites(
        program,
        &context.reachable,
        &invariant_by_struct,
    )
    .map_err(VerificationError::StructInvariant)?;

    if prove_sites.is_empty() && invariant_sites.is_empty() {
        return Ok(());
    }

    if !prove_sites.is_empty() {
        reject_recursion_cycles(program, "main", &context.reachable, "prove verification")
            .map_err(VerificationError::Prove)?;
        run_obligation_batch(
            &context.function_map,
            &prove_sites,
            target_dir,
            &crate::prove::PROVE_BATCH_CONFIG,
            |site| site.id.as_str(),
            crate::prove::build_site_checker_function,
            crate::prove::should_assume_main_argc_non_negative,
            crate::prove::format_sat_failure,
        )
        .map_err(VerificationError::Prove)?;
    } else {
        reject_recursion_cycles(
            program,
            "main",
            &context.reachable,
            "struct invariant verification",
        )
        .map_err(VerificationError::StructInvariant)?;
    }

    if !invariant_sites.is_empty() {
        run_obligation_batch(
            &context.function_map,
            &invariant_sites,
            target_dir,
            &crate::struct_invariants::INVARIANT_BATCH_CONFIG,
            |site| site.id.as_str(),
            crate::struct_invariants::build_site_checker_function,
            crate::struct_invariants::should_assume_main_argc_non_negative,
            crate::struct_invariants::format_sat_failure,
        )
        .map_err(VerificationError::StructInvariant)?;
    }

    Ok(())
}

pub(crate) fn build_verification_context(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
) -> anyhow::Result<VerificationContext> {
    let reachable = reachable_user_functions(program, "main")?;
    let function_map = qbe_module
        .functions
        .iter()
        .map(|function| (function.name.clone(), function.clone()))
        .collect::<HashMap<_, _>>();
    Ok(VerificationContext {
        reachable,
        function_map,
    })
}

pub(crate) fn run_obligation_batch<O, FId, FBuildChecker, FAssumeArgc, FFormatSat>(
    function_map: &HashMap<String, qbe::Function>,
    obligations: &[O],
    target_dir: &Path,
    config: &ObligationBatchConfig<'_>,
    obligation_id: FId,
    build_checker: FBuildChecker,
    should_assume_main_argc_non_negative: FAssumeArgc,
    format_sat_failure: FFormatSat,
) -> anyhow::Result<()>
where
    FId: Fn(&O) -> &str,
    FBuildChecker: Fn(&HashMap<String, qbe::Function>, &O) -> anyhow::Result<qbe::Function>,
    FAssumeArgc: Fn(&O, &qbe::Function) -> bool,
    FFormatSat: Fn(&O, &qbe::Function, &str, &str, &qbe_smt::SolverRun) -> String,
{
    let verification_dir = target_dir.join(config.verification_subdir);
    std::fs::create_dir_all(&verification_dir).with_context(|| {
        format!(
            "{} {}",
            config.create_dir_error_prefix,
            verification_dir.display()
        )
    })?;

    let mut failures = Vec::new();
    for obligation in obligations {
        let id = obligation_id(obligation);
        let checker_function = build_checker(function_map, obligation)?;
        let checker_qbe = checker_function.to_string();
        let site_stem = format!("site_{}", sanitize_ident(id));
        let qbe_filename = format!("{}.qbe", site_stem);
        let smt_filename = format!("{}.smt2", site_stem);

        let qbe_path = verification_dir.join(&qbe_filename);
        std::fs::write(&qbe_path, &checker_qbe)
            .with_context(|| format!("{} {}", config.write_qbe_error_prefix, qbe_path.display()))?;

        let smt = qbe_smt::qbe_to_smt(
            &checker_function,
            &qbe_smt::EncodeOptions {
                assume_main_argc_non_negative: should_assume_main_argc_non_negative(
                    obligation,
                    &checker_function,
                ),
                first_arg_i32_range: None,
            },
        )
        .map_err(|err| {
            anyhow::anyhow!(
                "{} {}: {}\n{}",
                config.encode_error_prefix,
                id,
                err,
                err.render_report_plain(config.encode_report_name)
            )
        })?;

        let smt_path = verification_dir.join(&smt_filename);
        std::fs::write(&smt_path, &smt)
            .with_context(|| format!("{} {}", config.write_smt_error_prefix, smt_path.display()))?;

        match qbe_smt::solve_chc_script_with_diagnostics(&smt, Z3_TIMEOUT_SECONDS) {
            Ok(run) if run.result == qbe_smt::SolverResult::Unsat => {}
            Ok(run) if run.result == qbe_smt::SolverResult::Sat => {
                failures.push(format_sat_failure(
                    obligation,
                    &checker_function,
                    &qbe_filename,
                    &smt_filename,
                    &run,
                ))
            }
            Ok(_run) => {
                return Err(anyhow::anyhow!("{} {}", config.unknown_error_prefix, id));
            }
            Err(err) => {
                return Err(anyhow::anyhow!(
                    "{} {}: {}\n{}",
                    config.solve_error_prefix,
                    id,
                    err,
                    err.render_report_plain(config.solve_report_name)
                ))
            }
        }
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(anyhow::anyhow!(
            "{}\n{}",
            config.sat_failure_header,
            failures.join("\n")
        ))
    }
}

pub(crate) fn reachable_user_functions(
    program: &ResolvedProgram,
    root: &str,
) -> anyhow::Result<HashSet<String>> {
    let mut reachable = HashSet::new();
    let mut stack = vec![root.to_string()];

    while let Some(function_name) = stack.pop() {
        if !reachable.insert(function_name.clone()) {
            continue;
        }

        let function = program
            .function_definitions
            .get(&function_name)
            .ok_or_else(|| {
                anyhow::anyhow!("reachable function {} is missing definition", function_name)
            })?;

        let mut callees = BTreeSet::new();
        for statement in &function.body {
            collect_called_user_functions_in_statement(statement, program, &mut callees);
        }
        for callee in callees {
            if !reachable.contains(&callee) {
                stack.push(callee);
            }
        }
    }

    Ok(reachable)
}

pub(crate) fn reject_recursion_cycles(
    program: &ResolvedProgram,
    root: &str,
    reachable: &HashSet<String>,
    verification_kind: &str,
) -> anyhow::Result<()> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum VisitState {
        Visiting,
        Visited,
    }

    fn dfs(
        program: &ResolvedProgram,
        function: &str,
        reachable: &HashSet<String>,
        states: &mut HashMap<String, VisitState>,
        stack: &mut Vec<String>,
        verification_kind: &str,
    ) -> anyhow::Result<()> {
        if let Some(VisitState::Visited) = states.get(function) {
            return Ok(());
        }
        if let Some(VisitState::Visiting) = states.get(function) {
            let pos = stack.iter().position(|name| name == function).unwrap_or(0);
            let mut cycle = stack[pos..].join(" -> ");
            if !cycle.is_empty() {
                cycle.push_str(" -> ");
            }
            cycle.push_str(function);
            return Err(anyhow::anyhow!(
                "recursion cycles are unsupported by {}: {}",
                verification_kind,
                cycle
            ));
        }

        states.insert(function.to_string(), VisitState::Visiting);
        stack.push(function.to_string());

        let func = program
            .function_definitions
            .get(function)
            .ok_or_else(|| anyhow::anyhow!("missing function definition for {}", function))?;
        let mut callees = BTreeSet::new();
        for statement in &func.body {
            collect_called_user_functions_in_statement(statement, program, &mut callees);
        }
        for callee in callees {
            if reachable.contains(&callee) {
                dfs(
                    program,
                    &callee,
                    reachable,
                    states,
                    stack,
                    verification_kind,
                )?;
            }
        }

        stack.pop();
        states.insert(function.to_string(), VisitState::Visited);
        Ok(())
    }

    let mut states = HashMap::new();
    let mut stack = Vec::new();
    if reachable.contains(root) {
        dfs(
            program,
            root,
            reachable,
            &mut states,
            &mut stack,
            verification_kind,
        )?;
    }
    Ok(())
}

pub(crate) fn sanitize_ident(input: &str) -> String {
    let mut out = String::new();
    for (i, ch) in input.chars().enumerate() {
        let keep = ch.is_ascii_alphanumeric() || ch == '_';
        if keep {
            if i == 0 && ch.is_ascii_digit() {
                out.push('_');
            }
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() {
        "_sym".to_string()
    } else {
        out
    }
}

pub(crate) fn summarize_solver_output(stdout: &str, stderr: &str) -> Option<String> {
    let mut snippets = stdout
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .skip(1)
        .take(2)
        .map(|line| line.to_string())
        .collect::<Vec<_>>();

    if snippets.is_empty() {
        snippets = stderr
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
            .take(1)
            .map(|line| line.to_string())
            .collect::<Vec<_>>();
    }

    if snippets.is_empty() {
        None
    } else {
        Some(snippets.join(" | "))
    }
}

fn collect_called_user_functions_in_statement(
    statement: &Statement,
    program: &ResolvedProgram,
    out: &mut BTreeSet<String>,
) {
    match statement {
        Statement::StructDef { .. } => {}
        Statement::Assign { value, .. } => {
            collect_called_user_functions_in_expr(value, program, out)
        }
        Statement::Return { expr } => collect_called_user_functions_in_expr(expr, program, out),
        Statement::Expression { expr } => collect_called_user_functions_in_expr(expr, program, out),
        Statement::Prove { condition } => {
            collect_called_user_functions_in_expr(condition, program, out)
        }
        Statement::Assert { condition } => {
            collect_called_user_functions_in_expr(condition, program, out)
        }
        Statement::Conditional {
            condition,
            body,
            else_body,
        } => {
            collect_called_user_functions_in_expr(condition, program, out);
            for statement in body {
                collect_called_user_functions_in_statement(statement, program, out);
            }
            if let Some(else_body) = else_body {
                for statement in else_body {
                    collect_called_user_functions_in_statement(statement, program, out);
                }
            }
        }
        Statement::While { condition, body } => {
            collect_called_user_functions_in_expr(condition, program, out);
            for statement in body {
                collect_called_user_functions_in_statement(statement, program, out);
            }
        }
        Statement::Match { subject, arms } => {
            collect_called_user_functions_in_expr(subject, program, out);
            for arm in arms {
                for statement in &arm.body {
                    collect_called_user_functions_in_statement(statement, program, out);
                }
            }
        }
    }
}

fn collect_called_user_functions_in_expr(
    expr: &Expression,
    program: &ResolvedProgram,
    out: &mut BTreeSet<String>,
) {
    match expr {
        Expression::Call(name, args) => {
            if program.function_definitions.contains_key(name) {
                out.insert(name.clone());
            }
            for arg in args {
                collect_called_user_functions_in_expr(arg, program, out);
            }
        }
        Expression::PostfixCall { callee, args } => {
            if let Expression::FieldAccess {
                struct_variable,
                field,
            } = callee.as_ref()
            {
                let call = crate::parser::qualify_namespace_function_name(struct_variable, field);
                if program.function_definitions.contains_key(&call) {
                    out.insert(call);
                }
            }
            collect_called_user_functions_in_expr(callee, program, out);
            for arg in args {
                collect_called_user_functions_in_expr(arg, program, out);
            }
        }
        Expression::BinOp(_, lhs, rhs) => {
            collect_called_user_functions_in_expr(lhs, program, out);
            collect_called_user_functions_in_expr(rhs, program, out);
        }
        Expression::UnaryOp(_, expr) => collect_called_user_functions_in_expr(expr, program, out),
        Expression::StructValue { field_values, .. } => {
            for (_, value) in field_values {
                collect_called_user_functions_in_expr(value, program, out);
            }
        }
        Expression::Match { subject, arms } => {
            collect_called_user_functions_in_expr(subject, program, out);
            for arm in arms {
                collect_called_user_functions_in_expr(&arm.value, program, out);
            }
        }
        Expression::Literal(_) | Expression::Variable(_) | Expression::FieldAccess { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use crate::{ir, parser, qbe_backend, tokenizer};

    use super::{verify_all_obligations_with_qbe, VerificationError};

    fn resolve_program(source: &str) -> ir::ResolvedProgram {
        let tokens = tokenizer::tokenize(source.to_string()).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        ir::resolve(ast).expect("resolve source")
    }

    #[test]
    fn verify_all_is_noop_when_no_obligations_exist() {
        let source = r#"
fun main() -> I32 {
	return 0
}
"#;
        let program = resolve_program(source);
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        verify_all_obligations_with_qbe(&program, &qbe_module, tempdir.path())
            .expect("no obligations should pass");
    }

    #[test]
    fn prove_failure_short_circuits_struct_invariant_batch() {
        let source = r#"
struct Counter {
	value: I32,
}

invariant "counter non-negative" for (v: Counter) {
	return v.value >= 0
}

fun make_counter(v: I32) -> Counter {
	return Counter struct { value: v, }
}

fun main() -> I32 {
	prove(false)
	c = make_counter(0 - 1)
	return 0
}
"#;
        let program = resolve_program(source);
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        let err = verify_all_obligations_with_qbe(&program, &qbe_module, tempdir.path())
            .expect_err("prove obligation should fail before invariant checks");
        match err {
            VerificationError::Prove(err) => {
                if !err
                    .to_string()
                    .to_lowercase()
                    .contains("solver unavailable")
                {
                    assert!(
                        err.to_string().contains("SAT counterexamples found"),
                        "expected SAT prove failure, got: {err}"
                    );
                }
            }
            VerificationError::StructInvariant(err) => {
                panic!("expected prove error, got invariant error: {err}");
            }
        }

        assert!(
            !tempdir.path().join("struct_invariants").exists(),
            "struct invariant batch should not run after prove failure"
        );
    }
}
