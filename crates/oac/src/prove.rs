use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::Path;

use anyhow::Context;

use crate::ir::ResolvedProgram;
use crate::parser::{Expression, Statement};
use crate::qbe_backend::PROVE_MARKER_PREFIX;

const Z3_TIMEOUT_SECONDS: u64 = 10;

#[derive(Clone, Debug)]
struct ProveSite {
    id: String,
    caller: String,
    marker_temp: String,
}

pub fn verify_prove_obligations_with_qbe(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
) -> anyhow::Result<()> {
    let reachable = reachable_user_functions(program, "main")?;

    let function_map = qbe_module
        .functions
        .iter()
        .map(|function| (function.name.clone(), function.clone()))
        .collect::<HashMap<_, _>>();

    let sites = collect_prove_sites(&function_map, &reachable)?;
    if sites.is_empty() {
        return Ok(());
    }

    reject_recursion_cycles(program, "main", &reachable)?;
    solve_prove_sites(&function_map, &sites, target_dir)
}

fn reachable_user_functions(
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

fn reject_recursion_cycles(
    program: &ResolvedProgram,
    root: &str,
    reachable: &HashSet<String>,
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
                "recursion cycles are unsupported by prove verification: {}",
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
                dfs(program, &callee, reachable, states, stack)?;
            }
        }

        stack.pop();
        states.insert(function.to_string(), VisitState::Visited);
        Ok(())
    }

    let mut states = HashMap::new();
    let mut stack = Vec::new();
    if reachable.contains(root) {
        dfs(program, root, reachable, &mut states, &mut stack)?;
    }
    Ok(())
}

fn collect_prove_sites(
    function_map: &HashMap<String, qbe::Function>,
    reachable: &HashSet<String>,
) -> anyhow::Result<Vec<ProveSite>> {
    let mut functions = reachable.iter().cloned().collect::<Vec<_>>();
    functions.sort();

    let mut sites = Vec::new();
    for function_name in functions {
        let function = function_map
            .get(&function_name)
            .ok_or_else(|| anyhow::anyhow!("missing QBE function {}", function_name))?;

        for (block_index, block) in function.blocks.iter().enumerate() {
            for (item_index, item) in block.items.iter().enumerate() {
                let qbe::BlockItem::Statement(qbe::Statement::Assign(
                    qbe::Value::Temporary(dest),
                    _,
                    qbe::Instr::Copy(_),
                )) = item
                else {
                    continue;
                };

                if !dest.starts_with(PROVE_MARKER_PREFIX) {
                    continue;
                }

                sites.push(ProveSite {
                    id: format!("{}#{}#{}", function_name, block_index, item_index),
                    caller: function_name.clone(),
                    marker_temp: dest.clone(),
                });
            }
        }
    }

    sites.sort_by(|a, b| a.id.cmp(&b.id));
    Ok(sites)
}

fn solve_prove_sites(
    function_map: &HashMap<String, qbe::Function>,
    sites: &[ProveSite],
    target_dir: &Path,
) -> anyhow::Result<()> {
    let verification_dir = target_dir.join("prove");
    std::fs::create_dir_all(&verification_dir).with_context(|| {
        format!(
            "failed to create prove verification directory {}",
            verification_dir.display()
        )
    })?;

    let mut failures = Vec::new();
    for site in sites {
        let checker_function = build_site_checker_function(function_map, site)?;
        let checker_qbe = checker_function.to_string();
        let site_stem = format!("site_{}", sanitize_ident(&site.id));
        let qbe_filename = format!("{}.qbe", site_stem);
        let smt_filename = format!("{}.smt2", site_stem);

        let qbe_path = verification_dir.join(&qbe_filename);
        std::fs::write(&qbe_path, &checker_qbe).with_context(|| {
            format!(
                "failed to write prove checker QBE program {}",
                qbe_path.display()
            )
        })?;

        let smt = qbe_smt::qbe_to_smt(
            &checker_function,
            &qbe_smt::EncodeOptions {
                assume_main_argc_non_negative: should_assume_main_argc_non_negative(
                    site,
                    &checker_function,
                ),
                first_arg_i32_range: None,
            },
        )
        .map_err(|err| {
            anyhow::anyhow!(
                "failed to encode prove checker QBE for {}: {}\n{}",
                site.id,
                err,
                err.render_report_plain("prove-checker")
            )
        })?;

        let smt_path = verification_dir.join(&smt_filename);
        std::fs::write(&smt_path, &smt).with_context(|| {
            format!(
                "failed to write prove SMT obligation {}",
                smt_path.display()
            )
        })?;

        match qbe_smt::solve_chc_script_with_diagnostics(&smt, Z3_TIMEOUT_SECONDS) {
            Ok(run) if run.result == qbe_smt::SolverResult::Unsat => {}
            Ok(run) if run.result == qbe_smt::SolverResult::Sat => {
                let solver_excerpt = summarize_solver_output(&run.stdout, &run.stderr)
                    .map(|excerpt| format!(", solver_excerpt={excerpt}"))
                    .unwrap_or_default();
                let mut failure = format!(
                    "{} (caller={}, qbe_artifact={}, smt_artifact={}",
                    site.id, site.caller, qbe_filename, smt_filename
                );
                failure.push_str(&solver_excerpt);
                failure.push(')');
                failures.push(failure);
            }
            Ok(_run) => {
                return Err(anyhow::anyhow!(
                    "solver returned unknown for prove obligation {}",
                    site.id
                ));
            }
            Err(err) => {
                return Err(anyhow::anyhow!(
                    "failed to solve prove obligation {}: {}\n{}",
                    site.id,
                    err,
                    err.render_report_plain("prove-obligation")
                ))
            }
        }
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(anyhow::anyhow!(
            "prove verification failed (SAT counterexamples found):\n{}",
            failures.join("\n")
        ))
    }
}

fn build_site_checker_function(
    function_map: &HashMap<String, qbe::Function>,
    site: &ProveSite,
) -> anyhow::Result<qbe::Function> {
    let caller = function_map
        .get(&site.caller)
        .ok_or_else(|| anyhow::anyhow!("missing QBE function for caller {}", site.caller))?;
    let mut checker = caller.clone();
    checker.name = "main".to_string();
    checker.linkage = qbe::Linkage::private();
    checker.return_ty = Some(qbe::Type::Word);

    rewrite_returns_to_zero(&mut checker);
    inject_site_check_and_return(&mut checker, site)?;
    crate::struct_invariants::inline_reachable_user_calls(&mut checker, function_map)?;

    Ok(checker)
}

fn rewrite_returns_to_zero(function: &mut qbe::Function) {
    for block in &mut function.blocks {
        for item in &mut block.items {
            let qbe::BlockItem::Statement(qbe::Statement::Volatile(instr)) = item else {
                continue;
            };
            if matches!(instr, qbe::Instr::Ret(_)) {
                *instr = qbe::Instr::Ret(Some(qbe::Value::Const(0)));
            }
        }
    }
}

fn inject_site_check_and_return(
    function: &mut qbe::Function,
    site: &ProveSite,
) -> anyhow::Result<()> {
    let mut found = false;
    let bad_temp = format!("{}_bad", site.marker_temp);

    for block in &mut function.blocks {
        for item_index in 0..block.items.len() {
            let qbe::BlockItem::Statement(qbe::Statement::Assign(
                qbe::Value::Temporary(dest),
                _,
                qbe::Instr::Copy(_),
            )) = &block.items[item_index]
            else {
                continue;
            };
            if dest != &site.marker_temp {
                continue;
            }

            let mut new_items = block.items[..=item_index].to_vec();
            new_items.push(qbe::BlockItem::Statement(qbe::Statement::Assign(
                qbe::Value::Temporary(bad_temp.clone()),
                qbe::Type::Word,
                qbe::Instr::Cmp(
                    qbe::Type::Word,
                    qbe::Cmp::Eq,
                    qbe::Value::Temporary(site.marker_temp.clone()),
                    qbe::Value::Const(0),
                ),
            )));
            new_items.push(qbe::BlockItem::Statement(qbe::Statement::Volatile(
                qbe::Instr::Ret(Some(qbe::Value::Temporary(bad_temp.clone()))),
            )));
            block.items = new_items;
            found = true;
            break;
        }
        if found {
            break;
        }
    }

    if found {
        Ok(())
    } else {
        Err(anyhow::anyhow!(
            "failed to locate prove marker {} for site {}",
            site.marker_temp,
            site.id
        ))
    }
}

fn sanitize_ident(input: &str) -> String {
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

fn should_assume_main_argc_non_negative(site: &ProveSite, checker: &qbe::Function) -> bool {
    if site.caller != "main" {
        return false;
    }
    if checker.arguments.len() != 2 {
        return false;
    }
    matches!(checker.arguments[0].0, qbe::Type::Word)
        && matches!(checker.arguments[1].0, qbe::Type::Long)
}

fn summarize_solver_output(stdout: &str, stderr: &str) -> Option<String> {
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

#[cfg(test)]
mod tests {
    use crate::{ir, parser, qbe_backend, tokenizer};

    use super::verify_prove_obligations_with_qbe;

    #[test]
    fn no_prove_sites_is_noop() {
        let source = r#"
fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let program = ir::resolve(ast).expect("resolve source");
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        verify_prove_obligations_with_qbe(&program, &qbe_module, tempdir.path())
            .expect("no prove obligations should pass");
    }
}
