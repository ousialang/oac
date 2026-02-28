use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::path::Path;

use anyhow::Context;

use crate::ir::{ResolvedProgram, TypeDef};
use crate::parser::{Expression, Statement};

const Z3_TIMEOUT_SECONDS: u64 = 10;

pub fn verify_struct_invariants(
    program: &ResolvedProgram,
    target_dir: &Path,
) -> anyhow::Result<()> {
    let qbe_module = crate::qbe_backend::compile(program.clone());
    verify_struct_invariants_with_qbe(program, &qbe_module, target_dir)
}

pub fn verify_struct_invariants_with_qbe(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
) -> anyhow::Result<()> {
    let invariant_by_struct = discover_invariants(program)?;
    let reachable = reachable_user_functions(program, "main")?;
    let sites = collect_obligation_sites(program, &reachable, &invariant_by_struct)?;
    if sites.is_empty() {
        return Ok(());
    }
    reject_recursion_cycles(program, "main", &reachable)?;
    solve_obligations_qbe(program, &qbe_module, &sites, target_dir)
}

#[derive(Clone, Debug)]
struct ObligationSite {
    id: String,
    caller: String,
    callee: String,
    callee_call_ordinal: usize,
    struct_name: String,
    invariant_fn: String,
    invariant_display_name: String,
    invariant_identifier: Option<String>,
}

#[derive(Clone, Debug)]
struct InvariantBinding {
    function_name: String,
    display_name: String,
    identifier: Option<String>,
}

fn discover_invariants(
    program: &ResolvedProgram,
) -> anyhow::Result<HashMap<String, InvariantBinding>> {
    let mut invariant_by_struct = HashMap::new();

    for (struct_name, invariant) in &program.struct_invariants {
        let ty = program
            .type_definitions
            .get(struct_name)
            .ok_or_else(|| anyhow::anyhow!("invariant targets unknown type {}", struct_name))?;
        if !matches!(ty, TypeDef::Struct(_)) {
            return Err(anyhow::anyhow!(
                "invariant \"{}\" must target a struct type, but {} is not a struct",
                invariant.display_name,
                struct_name
            ));
        }

        let func_def = program
            .function_definitions
            .get(&invariant.function_name)
            .ok_or_else(|| {
                anyhow::anyhow!(
                    "missing function definition for invariant \"{}\" ({})",
                    invariant.display_name,
                    invariant.function_name
                )
            })?;
        let sig = &func_def.sig;
        if sig.parameters.len() != 1 {
            return Err(anyhow::anyhow!(
                "invariant \"{}\" must have exactly one parameter of type {}",
                invariant.display_name,
                struct_name
            ));
        }
        if sig.parameters[0].ty != *struct_name {
            return Err(anyhow::anyhow!(
                "invariant \"{}\" must have signature fun {}(v: {}) -> Bool",
                invariant.display_name,
                invariant.function_name,
                struct_name
            ));
        }
        if sig.return_type != "Bool" {
            return Err(anyhow::anyhow!(
                "invariant \"{}\" must return Bool, got {}",
                invariant.display_name,
                sig.return_type
            ));
        }

        if let Some(existing) = invariant_by_struct.insert(
            struct_name.to_string(),
            InvariantBinding {
                function_name: invariant.function_name.clone(),
                display_name: invariant.display_name.clone(),
                identifier: invariant.identifier.clone(),
            },
        ) {
            return Err(anyhow::anyhow!(
                "struct {} has multiple invariants: \"{}\" and \"{}\"",
                struct_name,
                existing.display_name,
                invariant.display_name
            ));
        }
    }

    Ok(invariant_by_struct)
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
                "recursion cycles are unsupported by struct invariant verification: {}",
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

fn collect_obligation_sites(
    program: &ResolvedProgram,
    reachable: &HashSet<String>,
    invariant_by_struct: &HashMap<String, InvariantBinding>,
) -> anyhow::Result<Vec<ObligationSite>> {
    let mut sites = Vec::new();
    let mut functions = reachable.iter().cloned().collect::<Vec<_>>();
    functions.sort();
    let invariant_function_names = invariant_by_struct
        .values()
        .map(|binding| binding.function_name.as_str())
        .collect::<HashSet<_>>();

    for function_name in functions {
        if invariant_function_names.contains(function_name.as_str()) {
            continue;
        }

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

                let callee_sig = program
                    .function_sigs
                    .get(&callee_name)
                    .ok_or_else(|| anyhow::anyhow!("missing signature for {}", callee_name))?;

                let return_type = &callee_sig.return_type;
                let TypeDef::Struct(_) = program
                    .type_definitions
                    .get(return_type)
                    .ok_or_else(|| anyhow::anyhow!("unknown return type {}", return_type))?
                else {
                    continue;
                };

                let Some(invariant_binding) = invariant_by_struct.get(return_type) else {
                    continue;
                };

                let expr_index = *expr_index_map.get(&expr_path).ok_or_else(|| {
                    anyhow::anyhow!("missing expression index for path {}", expr_path)
                })?;

                let id = format!("{}#{}#{}", function_name, top_statement_index, expr_index);

                sites.push(ObligationSite {
                    id,
                    caller: function_name.clone(),
                    callee: callee_name,
                    callee_call_ordinal: current_ordinal,
                    struct_name: return_type.clone(),
                    invariant_fn: invariant_binding.function_name.clone(),
                    invariant_display_name: invariant_binding.display_name.clone(),
                    invariant_identifier: invariant_binding.identifier.clone(),
                });
            }
        }
    }

    sites.sort_by(|a, b| a.id.cmp(&b.id));
    Ok(sites)
}

fn index_statement_expressions(
    statement: &Statement,
    statement_path: &str,
    next_index: &mut usize,
    out: &mut HashMap<String, usize>,
) {
    match statement {
        Statement::StructDef { .. } => {}
        Statement::Assign { value, .. } => index_expression(
            value,
            &join_path(statement_path, "assign.value"),
            next_index,
            out,
        ),
        Statement::Return { expr } => index_expression(
            expr,
            &join_path(statement_path, "return.expr"),
            next_index,
            out,
        ),
        Statement::Expression { expr } => index_expression(
            expr,
            &join_path(statement_path, "expr.expr"),
            next_index,
            out,
        ),
        Statement::Prove { condition } => index_expression(
            condition,
            &join_path(statement_path, "prove.cond"),
            next_index,
            out,
        ),
        Statement::Assert { condition } => index_expression(
            condition,
            &join_path(statement_path, "assert.cond"),
            next_index,
            out,
        ),
        Statement::Conditional {
            condition,
            body,
            else_body,
        } => {
            index_expression(
                condition,
                &join_path(statement_path, "if.cond"),
                next_index,
                out,
            );
            let then_base = join_path(statement_path, "if.then");
            for (i, nested) in body.iter().enumerate() {
                index_statement_expressions(
                    nested,
                    &join_path(&then_base, &i.to_string()),
                    next_index,
                    out,
                );
            }
            if let Some(else_body) = else_body {
                let else_base = join_path(statement_path, "if.else");
                for (i, nested) in else_body.iter().enumerate() {
                    index_statement_expressions(
                        nested,
                        &join_path(&else_base, &i.to_string()),
                        next_index,
                        out,
                    );
                }
            }
        }
        Statement::While { condition, body } => {
            index_expression(
                condition,
                &join_path(statement_path, "while.cond"),
                next_index,
                out,
            );
            let body_base = join_path(statement_path, "while.body");
            for (i, nested) in body.iter().enumerate() {
                index_statement_expressions(
                    nested,
                    &join_path(&body_base, &i.to_string()),
                    next_index,
                    out,
                );
            }
        }
        Statement::Match { subject, arms } => {
            index_expression(
                subject,
                &join_path(statement_path, "match.subject"),
                next_index,
                out,
            );
            for (arm_index, arm) in arms.iter().enumerate() {
                let arm_base = join_path(statement_path, &format!("match.arm.{}", arm_index));
                for (stmt_index, nested) in arm.body.iter().enumerate() {
                    index_statement_expressions(
                        nested,
                        &join_path(&arm_base, &stmt_index.to_string()),
                        next_index,
                        out,
                    );
                }
            }
        }
    }
}

fn index_expression(
    expression: &Expression,
    expression_path: &str,
    next_index: &mut usize,
    out: &mut HashMap<String, usize>,
) {
    out.insert(expression_path.to_string(), *next_index);
    *next_index += 1;

    match expression {
        Expression::Match { subject, arms } => {
            index_expression(
                subject,
                &join_path(expression_path, "match.subject"),
                next_index,
                out,
            );
            for (i, arm) in arms.iter().enumerate() {
                index_expression(
                    &arm.value,
                    &join_path(expression_path, &format!("match.arm.{}", i)),
                    next_index,
                    out,
                );
            }
        }
        Expression::Call(_, args) => {
            for (i, arg) in args.iter().enumerate() {
                index_expression(
                    arg,
                    &join_path(expression_path, &format!("call.arg.{}", i)),
                    next_index,
                    out,
                );
            }
        }
        Expression::PostfixCall { callee, args } => {
            index_expression(
                callee,
                &join_path(expression_path, "postfix.callee"),
                next_index,
                out,
            );
            for (i, arg) in args.iter().enumerate() {
                index_expression(
                    arg,
                    &join_path(expression_path, &format!("postfix.arg.{}", i)),
                    next_index,
                    out,
                );
            }
        }
        Expression::BinOp(_, lhs, rhs) => {
            index_expression(lhs, &join_path(expression_path, "bin.lhs"), next_index, out);
            index_expression(rhs, &join_path(expression_path, "bin.rhs"), next_index, out);
        }
        Expression::UnaryOp(_, expr) => {
            index_expression(
                expr,
                &join_path(expression_path, "unary.expr"),
                next_index,
                out,
            );
        }
        Expression::StructValue { field_values, .. } => {
            for (field_name, expr) in field_values {
                index_expression(
                    expr,
                    &join_path(expression_path, &format!("struct.field.{}", field_name)),
                    next_index,
                    out,
                );
            }
        }
        Expression::Literal(_) | Expression::Variable(_) | Expression::FieldAccess { .. } => {}
    }
}

fn collect_call_nodes_from_statement(
    statement: &Statement,
    statement_path: &str,
    out: &mut Vec<(String, String)>,
) {
    match statement {
        Statement::StructDef { .. } => {}
        Statement::Assign { value, .. } => collect_call_nodes_from_expression(
            value,
            &join_path(statement_path, "assign.value"),
            out,
        ),
        Statement::Return { expr } => {
            collect_call_nodes_from_expression(expr, &join_path(statement_path, "return.expr"), out)
        }
        Statement::Expression { expr } => {
            collect_call_nodes_from_expression(expr, &join_path(statement_path, "expr.expr"), out)
        }
        Statement::Prove { condition } => collect_call_nodes_from_expression(
            condition,
            &join_path(statement_path, "prove.cond"),
            out,
        ),
        Statement::Assert { condition } => collect_call_nodes_from_expression(
            condition,
            &join_path(statement_path, "assert.cond"),
            out,
        ),
        Statement::Conditional {
            condition,
            body,
            else_body,
        } => {
            collect_call_nodes_from_expression(
                condition,
                &join_path(statement_path, "if.cond"),
                out,
            );
            let then_base = join_path(statement_path, "if.then");
            for (i, nested) in body.iter().enumerate() {
                collect_call_nodes_from_statement(
                    nested,
                    &join_path(&then_base, &i.to_string()),
                    out,
                );
            }
            if let Some(else_body) = else_body {
                let else_base = join_path(statement_path, "if.else");
                for (i, nested) in else_body.iter().enumerate() {
                    collect_call_nodes_from_statement(
                        nested,
                        &join_path(&else_base, &i.to_string()),
                        out,
                    );
                }
            }
        }
        Statement::While { condition, body } => {
            collect_call_nodes_from_expression(
                condition,
                &join_path(statement_path, "while.cond"),
                out,
            );
            let body_base = join_path(statement_path, "while.body");
            for (i, nested) in body.iter().enumerate() {
                collect_call_nodes_from_statement(
                    nested,
                    &join_path(&body_base, &i.to_string()),
                    out,
                );
            }
        }
        Statement::Match { subject, arms } => {
            collect_call_nodes_from_expression(
                subject,
                &join_path(statement_path, "match.subject"),
                out,
            );
            for (arm_index, arm) in arms.iter().enumerate() {
                let arm_base = join_path(statement_path, &format!("match.arm.{}", arm_index));
                for (stmt_index, nested) in arm.body.iter().enumerate() {
                    collect_call_nodes_from_statement(
                        nested,
                        &join_path(&arm_base, &stmt_index.to_string()),
                        out,
                    );
                }
            }
        }
    }
}

fn collect_call_nodes_from_expression(
    expression: &Expression,
    expression_path: &str,
    out: &mut Vec<(String, String)>,
) {
    match expression {
        Expression::Call(name, args) => {
            out.push((expression_path.to_string(), name.clone()));
            for (i, arg) in args.iter().enumerate() {
                collect_call_nodes_from_expression(
                    arg,
                    &join_path(expression_path, &format!("call.arg.{}", i)),
                    out,
                );
            }
        }
        Expression::PostfixCall { callee, args } => {
            if let Expression::FieldAccess {
                struct_variable,
                field,
            } = callee.as_ref()
            {
                let call = crate::parser::qualify_namespace_function_name(struct_variable, field);
                out.push((expression_path.to_string(), call));
            }
            collect_call_nodes_from_expression(
                callee,
                &join_path(expression_path, "postfix.callee"),
                out,
            );
            for (i, arg) in args.iter().enumerate() {
                collect_call_nodes_from_expression(
                    arg,
                    &join_path(expression_path, &format!("postfix.arg.{}", i)),
                    out,
                );
            }
        }
        Expression::BinOp(_, lhs, rhs) => {
            collect_call_nodes_from_expression(lhs, &join_path(expression_path, "bin.lhs"), out);
            collect_call_nodes_from_expression(rhs, &join_path(expression_path, "bin.rhs"), out);
        }
        Expression::UnaryOp(_, expr) => {
            collect_call_nodes_from_expression(
                expr,
                &join_path(expression_path, "unary.expr"),
                out,
            );
        }
        Expression::StructValue { field_values, .. } => {
            for (field_name, expr) in field_values {
                collect_call_nodes_from_expression(
                    expr,
                    &join_path(expression_path, &format!("struct.field.{}", field_name)),
                    out,
                );
            }
        }
        Expression::Match { subject, arms } => {
            collect_call_nodes_from_expression(
                subject,
                &join_path(expression_path, "match.subject"),
                out,
            );
            for (i, arm) in arms.iter().enumerate() {
                collect_call_nodes_from_expression(
                    &arm.value,
                    &join_path(expression_path, &format!("match.arm.{}", i)),
                    out,
                );
            }
        }
        Expression::Literal(_) | Expression::Variable(_) | Expression::FieldAccess { .. } => {}
    }
}

fn join_path(prefix: &str, segment: &str) -> String {
    if prefix.is_empty() {
        segment.to_string()
    } else {
        format!("{}.{}", prefix, segment)
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

fn should_assume_main_argc_non_negative(site: &ObligationSite, checker: &qbe::Function) -> bool {
    if site.caller != "main" {
        return false;
    }
    if checker.arguments.len() != 2 {
        return false;
    }
    matches!(checker.arguments[0].0, qbe::Type::Word)
        && matches!(checker.arguments[1].0, qbe::Type::Long)
}

fn solve_obligations_qbe(
    _program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    sites: &[ObligationSite],
    target_dir: &Path,
) -> anyhow::Result<()> {
    let verification_dir = target_dir.join("struct_invariants");
    std::fs::create_dir_all(&verification_dir).with_context(|| {
        format!(
            "failed to create struct invariant verification directory {}",
            verification_dir.display()
        )
    })?;

    let function_map = qbe_module
        .functions
        .iter()
        .map(|function| (function.name.clone(), function.clone()))
        .collect::<HashMap<_, _>>();

    let mut failures = Vec::new();

    for site in sites {
        let checker_function = build_site_checker_function(&function_map, site)?;
        let checker_qbe = checker_function.to_string();
        let site_stem = format!("site_{}", sanitize_ident(&site.id));
        let qbe_filename = format!("{}.qbe", site_stem);
        let smt_filename = format!("{}.smt2", site_stem);

        let qbe_path = verification_dir.join(&qbe_filename);
        std::fs::write(&qbe_path, &checker_qbe).with_context(|| {
            format!("failed to write checker QBE program {}", qbe_path.display())
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
        .with_context(|| format!("failed to encode checker QBE for {}", site.id))?;

        let smt_path = verification_dir.join(&smt_filename);
        std::fs::write(&smt_path, &smt)
            .with_context(|| format!("failed to write SMT obligation {}", smt_path.display()))?;

        match qbe_smt::solve_chc_script_with_diagnostics(&smt, Z3_TIMEOUT_SECONDS) {
            Ok(run) if run.result == qbe_smt::SolverResult::Unsat => {}
            Ok(run) if run.result == qbe_smt::SolverResult::Sat => {
                let witness = sat_cfg_witness_summary(&checker_function)
                    .unwrap_or_else(|| "unavailable".to_string());
                let solver_excerpt = summarize_solver_output(&run.stdout, &run.stderr)
                    .map(|excerpt| format!(", solver_excerpt={excerpt}"))
                    .unwrap_or_default();
                let program_input = try_find_program_input_counterexample(site, &checker_function)
                    .map(|input| format!(", program_input=\"{}\"", escape_diagnostic_value(&input)))
                    .unwrap_or_default();
                let invariant_label = if let Some(identifier) = &site.invariant_identifier {
                    format!("{} (id={})", site.invariant_display_name, identifier)
                } else {
                    site.invariant_display_name.clone()
                };
                failures.push(format!(
                    "{} (caller={}, callee={}, struct={}, invariant=\"{}\", witness={}, qbe_artifact={}, smt_artifact={}{}{})",
                    site.id,
                    site.caller,
                    site.callee,
                    site.struct_name,
                    invariant_label,
                    witness,
                    qbe_filename,
                    smt_filename,
                    program_input,
                    solver_excerpt
                ));
            }
            Ok(_run) => {
                return Err(anyhow::anyhow!("solver returned unknown for {}", site.id));
            }
            Err(err) => {
                return Err(anyhow::anyhow!(
                    "failed to solve struct invariant obligation {}: {}",
                    site.id,
                    err
                ))
            }
        }
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(anyhow::anyhow!(
            "struct invariant verification failed (SAT counterexamples found):\n{}",
            failures.join("\n")
        ))
    }
}

fn try_find_program_input_counterexample(
    site: &ObligationSite,
    checker: &qbe::Function,
) -> Option<String> {
    if site.caller != "main" {
        return None;
    }

    match checker.arguments.as_slice() {
        [] => Some("main() has no inputs (counterexample is input-independent)".to_string()),
        [(qbe::Type::Word, _), (qbe::Type::Long, _)] => None,
        _ => None,
    }
}

fn escape_diagnostic_value(value: &str) -> String {
    value.replace('"', "\\\"")
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

fn sat_cfg_witness_summary(function: &qbe::Function) -> Option<String> {
    if function.blocks.is_empty() {
        return None;
    }

    let target = find_bad_return_block(function)?;
    let path = shortest_block_path(function, 0, target.block_index)?;
    if path.is_empty() {
        return None;
    }

    let labels = path
        .iter()
        .map(|idx| format!("b{}", idx))
        .collect::<Vec<_>>()
        .join(" -> ");

    let edges = describe_path_edges(function, &path)?;
    if edges.is_empty() {
        Some(format!(
            "cfg_path={labels}, bad_ret_temp=%{}",
            target.bad_temp
        ))
    } else {
        Some(format!(
            "cfg_path={labels}, branch_steps=[{}], bad_ret_temp=%{}",
            edges.join("; "),
            target.bad_temp
        ))
    }
}

struct BadReturnSite {
    block_index: usize,
    bad_temp: String,
}

fn find_bad_return_block(function: &qbe::Function) -> Option<BadReturnSite> {
    for (block_index, block) in function.blocks.iter().enumerate() {
        for item in &block.items {
            let qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Ret(Some(
                qbe::Value::Temporary(temp),
            )))) = item
            else {
                continue;
            };
            if temp.starts_with("si_bad") {
                return Some(BadReturnSite {
                    block_index,
                    bad_temp: temp.clone(),
                });
            }
        }
    }
    None
}

fn shortest_block_path(function: &qbe::Function, start: usize, goal: usize) -> Option<Vec<usize>> {
    let label_to_index = function
        .blocks
        .iter()
        .enumerate()
        .map(|(idx, block)| (block.label.clone(), idx))
        .collect::<HashMap<_, _>>();

    let mut queue = VecDeque::new();
    let mut visited = HashSet::new();
    let mut parent = HashMap::<usize, usize>::new();

    queue.push_back(start);
    visited.insert(start);

    while let Some(current) = queue.pop_front() {
        if current == goal {
            break;
        }
        for next in block_successors(function, &label_to_index, current).into_iter() {
            if visited.insert(next) {
                parent.insert(next, current);
                queue.push_back(next);
            }
        }
    }

    if !visited.contains(&goal) {
        return None;
    }

    let mut path = vec![goal];
    let mut cursor = goal;
    while cursor != start {
        let prev = *parent.get(&cursor)?;
        path.push(prev);
        cursor = prev;
    }
    path.reverse();
    Some(path)
}

fn block_successors(
    function: &qbe::Function,
    label_to_index: &HashMap<String, usize>,
    block_index: usize,
) -> Vec<usize> {
    let block = &function.blocks[block_index];
    let terminator = block.items.iter().rev().find_map(|item| {
        if let qbe::BlockItem::Statement(qbe::Statement::Volatile(instr)) = item {
            Some(instr)
        } else {
            None
        }
    });

    match terminator {
        Some(qbe::Instr::Jmp(target)) => label_to_index.get(target).copied().into_iter().collect(),
        Some(qbe::Instr::Jnz(_, on_true, on_false)) => {
            let mut out = Vec::new();
            if let Some(idx) = label_to_index.get(on_true).copied() {
                out.push(idx);
            }
            if let Some(idx) = label_to_index.get(on_false).copied() {
                out.push(idx);
            }
            out
        }
        Some(qbe::Instr::Ret(_)) | Some(qbe::Instr::Hlt) => Vec::new(),
        _ => {
            if block_index + 1 < function.blocks.len() {
                vec![block_index + 1]
            } else {
                Vec::new()
            }
        }
    }
}

fn describe_path_edges(function: &qbe::Function, path: &[usize]) -> Option<Vec<String>> {
    if path.len() < 2 {
        return Some(Vec::new());
    }

    let label_to_index = function
        .blocks
        .iter()
        .enumerate()
        .map(|(idx, block)| (block.label.clone(), idx))
        .collect::<HashMap<_, _>>();

    let mut edges = Vec::new();
    for window in path.windows(2) {
        let from = window[0];
        let to = window[1];
        let from_block = &function.blocks[from];
        let edge = describe_edge(from, to, &from_block.items, &label_to_index)?;
        edges.push(edge);
    }
    Some(edges)
}

fn describe_edge(
    from_index: usize,
    to_index: usize,
    from_items: &[qbe::BlockItem],
    label_to_index: &HashMap<String, usize>,
) -> Option<String> {
    let terminator = from_items.iter().rev().find_map(|item| {
        if let qbe::BlockItem::Statement(qbe::Statement::Volatile(instr)) = item {
            Some(instr)
        } else {
            None
        }
    });

    match terminator {
        Some(qbe::Instr::Jmp(_)) => Some(format!("b{from_index} -> b{to_index} (jmp)")),
        Some(qbe::Instr::Jnz(_cond, on_true, on_false)) => {
            let true_idx = label_to_index.get(on_true).copied();
            let false_idx = label_to_index.get(on_false).copied();
            if Some(to_index) == true_idx {
                Some(format!("b{from_index} -> b{to_index} (jnz true)"))
            } else if Some(to_index) == false_idx {
                Some(format!("b{from_index} -> b{to_index} (jnz false)"))
            } else {
                None
            }
        }
        Some(qbe::Instr::Ret(_)) | Some(qbe::Instr::Hlt) => None,
        _ => Some(format!("b{from_index} -> b{to_index} (fallthrough)")),
    }
}

fn build_site_checker_function(
    function_map: &HashMap<String, qbe::Function>,
    site: &ObligationSite,
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
    inline_reachable_user_calls(&mut checker, function_map)?;

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
    site: &ObligationSite,
) -> anyhow::Result<()> {
    let mut call_count = 0usize;
    let mut found = false;
    let mut used_temps = collect_temps_in_function(function);

    for block in &mut function.blocks {
        for item_index in 0..block.items.len() {
            let call_info = match &block.items[item_index] {
                qbe::BlockItem::Statement(qbe::Statement::Assign(
                    dest,
                    ty,
                    qbe::Instr::Call(name, args, variadic_index),
                )) => {
                    if name == &site.callee {
                        Some((dest.clone(), ty.clone(), args.clone(), *variadic_index))
                    } else {
                        None
                    }
                }
                qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Call(
                    name,
                    _args,
                    variadic_index,
                ))) => {
                    if name == &site.callee {
                        Some((
                            qbe::Value::Const(0),
                            qbe::Type::Word,
                            vec![],
                            *variadic_index,
                        ))
                    } else {
                        None
                    }
                }
                _ => None,
            };

            let Some((dest, dest_ty, _args, variadic_index)) = call_info else {
                continue;
            };

            if call_count == site.callee_call_ordinal {
                if variadic_index.is_some() {
                    return Err(anyhow::anyhow!(
                        "unsupported variadic call at struct invariant site {}",
                        site.id
                    ));
                }

                let qbe::Value::Temporary(_) = dest else {
                    return Err(anyhow::anyhow!(
                        "unsupported non-temporary call destination at struct invariant site {}",
                        site.id
                    ));
                };

                let inv_temp = fresh_unique_temp("si_inv", &mut used_temps);
                let bad_temp = fresh_unique_temp("si_bad", &mut used_temps);

                let mut new_items = block.items[..=item_index].to_vec();
                new_items.push(qbe::BlockItem::Statement(qbe::Statement::Assign(
                    qbe::Value::Temporary(inv_temp.clone()),
                    qbe::Type::Word,
                    qbe::Instr::Call(
                        site.invariant_fn.clone(),
                        vec![(dest_ty.clone(), dest.clone())],
                        None,
                    ),
                )));
                new_items.push(qbe::BlockItem::Statement(qbe::Statement::Assign(
                    qbe::Value::Temporary(bad_temp.clone()),
                    qbe::Type::Word,
                    qbe::Instr::Cmp(
                        qbe::Type::Word,
                        qbe::Cmp::Eq,
                        qbe::Value::Temporary(inv_temp),
                        qbe::Value::Const(0),
                    ),
                )));
                new_items.push(qbe::BlockItem::Statement(qbe::Statement::Volatile(
                    qbe::Instr::Ret(Some(qbe::Value::Temporary(bad_temp))),
                )));
                block.items = new_items;
                found = true;
                break;
            }

            call_count += 1;
        }

        if found {
            break;
        }
    }

    if found {
        Ok(())
    } else {
        Err(anyhow::anyhow!(
            "failed to locate QBE call for struct invariant site {} (callee={}, ordinal={})",
            site.id,
            site.callee,
            site.callee_call_ordinal
        ))
    }
}

pub(crate) fn inline_reachable_user_calls(
    function: &mut qbe::Function,
    function_map: &HashMap<String, qbe::Function>,
) -> anyhow::Result<()> {
    let mut inline_counter = 0usize;
    let max_inlines = 20_000usize;

    loop {
        if inline_counter > max_inlines {
            return Err(anyhow::anyhow!(
                "inline limit exceeded while building checker for {}",
                function.name
            ));
        }

        let Some((block_idx, item_idx, callee_name)) =
            find_next_reachable_inline_call(function, function_map)
        else {
            break;
        };

        if callee_name == function.name {
            return Err(anyhow::anyhow!(
                "recursion cycles are unsupported by struct invariant verification: {} -> {}",
                function.name,
                callee_name
            ));
        }

        let callee = function_map
            .get(&callee_name)
            .ok_or_else(|| anyhow::anyhow!("missing callee function {}", callee_name))?
            .clone();
        inline_single_call(function, block_idx, item_idx, &callee, inline_counter)?;
        inline_counter += 1;
    }

    Ok(())
}

fn find_next_reachable_inline_call(
    function: &qbe::Function,
    function_map: &HashMap<String, qbe::Function>,
) -> Option<(usize, usize, String)> {
    let reachable = reachable_block_indices(function);

    for (block_idx, block) in function.blocks.iter().enumerate() {
        if !reachable.contains(&block_idx) {
            continue;
        }
        for (item_idx, item) in block.items.iter().enumerate() {
            let maybe_name = match item {
                qbe::BlockItem::Statement(qbe::Statement::Assign(
                    _,
                    _,
                    qbe::Instr::Call(name, _, variadic_index),
                )) => {
                    if variadic_index.is_none() {
                        Some(name)
                    } else {
                        None
                    }
                }
                qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Call(
                    name,
                    _,
                    variadic_index,
                ))) => {
                    if variadic_index.is_none() {
                        Some(name)
                    } else {
                        None
                    }
                }
                _ => None,
            };

            let Some(name) = maybe_name else {
                continue;
            };
            if function_map.contains_key(name) {
                return Some((block_idx, item_idx, name.clone()));
            }
        }
    }

    None
}

fn inline_single_call(
    function: &mut qbe::Function,
    block_idx: usize,
    item_idx: usize,
    callee: &qbe::Function,
    inline_counter: usize,
) -> anyhow::Result<()> {
    if callee.blocks.is_empty() {
        return Err(anyhow::anyhow!(
            "cannot inline empty callee {}",
            callee.name
        ));
    }

    let call_item = function.blocks[block_idx]
        .items
        .get(item_idx)
        .cloned()
        .ok_or_else(|| anyhow::anyhow!("invalid call location for inlining"))?;

    enum CallKind {
        Assign {
            dest: qbe::Value,
            dest_ty: qbe::Type,
            args: Vec<(qbe::Type, qbe::Value)>,
        },
        Volatile {
            args: Vec<(qbe::Type, qbe::Value)>,
        },
    }

    let call_kind = match &call_item {
        qbe::BlockItem::Statement(qbe::Statement::Assign(
            dest,
            dest_ty,
            qbe::Instr::Call(name, args, variadic_index),
        )) => {
            if name != &callee.name {
                return Err(anyhow::anyhow!(
                    "call target mismatch while inlining: expected {}, got {}",
                    callee.name,
                    name
                ));
            }
            if variadic_index.is_some() {
                return Err(anyhow::anyhow!(
                    "variadic call to {} is unsupported in struct invariant checker inlining",
                    name
                ));
            }
            CallKind::Assign {
                dest: dest.clone(),
                dest_ty: dest_ty.clone(),
                args: args.clone(),
            }
        }
        qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Call(
            name,
            args,
            variadic_index,
        ))) => {
            if name != &callee.name {
                return Err(anyhow::anyhow!(
                    "call target mismatch while inlining: expected {}, got {}",
                    callee.name,
                    name
                ));
            }
            if variadic_index.is_some() {
                return Err(anyhow::anyhow!(
                    "variadic call to {} is unsupported in struct invariant checker inlining",
                    name
                ));
            }
            CallKind::Volatile { args: args.clone() }
        }
        _ => {
            return Err(anyhow::anyhow!(
                "inline_single_call expected a call statement"
            ))
        }
    };

    let mut used_temps = collect_temps_in_function(function);
    let mut used_labels = collect_labels_in_function(function);

    let inline_prefix = format!("si_inl_{}_{}", inline_counter, sanitize_ident(&callee.name));
    let continuation_label =
        fresh_unique_label(&format!("{}_cont", inline_prefix), &mut used_labels);

    let mut temp_map = HashMap::new();
    for temp in collect_temps_in_function(callee) {
        let renamed = fresh_unique_temp(
            &format!("{}_{}", inline_prefix, sanitize_ident(&temp)),
            &mut used_temps,
        );
        temp_map.insert(temp, renamed);
    }

    let mut label_map = HashMap::new();
    for block in &callee.blocks {
        let renamed = fresh_unique_label(
            &format!("{}_{}", inline_prefix, sanitize_ident(&block.label)),
            &mut used_labels,
        );
        label_map.insert(block.label.clone(), renamed);
    }

    let entry_label = label_map
        .get(&callee.blocks[0].label)
        .cloned()
        .ok_or_else(|| anyhow::anyhow!("missing callee entry label mapping"))?;

    let caller_items = function.blocks[block_idx].items.clone();
    let caller_prefix_items = caller_items[..item_idx].to_vec();
    let caller_suffix_items = caller_items[item_idx + 1..].to_vec();

    let mut new_current_items = caller_prefix_items;
    new_current_items.push(qbe::BlockItem::Statement(qbe::Statement::Volatile(
        qbe::Instr::Jmp(entry_label.clone()),
    )));
    function.blocks[block_idx].items = new_current_items;

    let actual_args = match &call_kind {
        CallKind::Assign { args, .. } => args.clone(),
        CallKind::Volatile { args } => args.clone(),
    };
    if actual_args.len() != callee.arguments.len() {
        return Err(anyhow::anyhow!(
            "argument count mismatch while inlining {}: expected {}, got {}",
            callee.name,
            callee.arguments.len(),
            actual_args.len()
        ));
    }

    let mut inlined_blocks = Vec::new();
    for (callee_block_index, callee_block) in callee.blocks.iter().enumerate() {
        let mut new_block = qbe::Block {
            label: label_map
                .get(&callee_block.label)
                .cloned()
                .ok_or_else(|| anyhow::anyhow!("missing mapped callee block label"))?,
            items: Vec::new(),
        };

        if callee_block_index == 0 {
            for ((param_ty, param_value), (_, actual_value)) in
                callee.arguments.iter().zip(actual_args.iter())
            {
                let renamed_param = rename_value(param_value, &temp_map);
                new_block
                    .items
                    .push(qbe::BlockItem::Statement(qbe::Statement::Assign(
                        renamed_param,
                        param_ty.clone(),
                        qbe::Instr::Copy(actual_value.clone()),
                    )));
            }
        }

        for item in &callee_block.items {
            match item {
                qbe::BlockItem::Comment(comment) => {
                    new_block
                        .items
                        .push(qbe::BlockItem::Comment(comment.clone()));
                }
                qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Ret(ret_value))) => {
                    if let CallKind::Assign { dest, dest_ty, .. } = &call_kind {
                        let copied_value = ret_value
                            .as_ref()
                            .map(|value| rename_value(value, &temp_map))
                            .unwrap_or(qbe::Value::Const(0));
                        new_block
                            .items
                            .push(qbe::BlockItem::Statement(qbe::Statement::Assign(
                                dest.clone(),
                                dest_ty.clone(),
                                qbe::Instr::Copy(copied_value),
                            )));
                    }
                    new_block
                        .items
                        .push(qbe::BlockItem::Statement(qbe::Statement::Volatile(
                            qbe::Instr::Jmp(continuation_label.clone()),
                        )));
                }
                qbe::BlockItem::Statement(statement) => {
                    new_block
                        .items
                        .push(qbe::BlockItem::Statement(rename_statement(
                            statement, &temp_map, &label_map,
                        )));
                }
            }
        }

        inlined_blocks.push(new_block);
    }

    inlined_blocks.push(qbe::Block {
        label: continuation_label,
        items: caller_suffix_items,
    });

    function
        .blocks
        .splice(block_idx + 1..block_idx + 1, inlined_blocks);

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

fn collect_labels_in_function(function: &qbe::Function) -> HashSet<String> {
    function
        .blocks
        .iter()
        .map(|block| block.label.clone())
        .collect::<HashSet<_>>()
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

fn fresh_unique_label(base: &str, used: &mut HashSet<String>) -> String {
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

fn rename_statement(
    statement: &qbe::Statement,
    temp_map: &HashMap<String, String>,
    label_map: &HashMap<String, String>,
) -> qbe::Statement {
    match statement {
        qbe::Statement::Assign(dest, ty, instr) => qbe::Statement::Assign(
            rename_value(dest, temp_map),
            ty.clone(),
            rename_instr(instr, temp_map, label_map),
        ),
        qbe::Statement::Volatile(instr) => {
            qbe::Statement::Volatile(rename_instr(instr, temp_map, label_map))
        }
    }
}

fn rename_value(value: &qbe::Value, temp_map: &HashMap<String, String>) -> qbe::Value {
    match value {
        qbe::Value::Temporary(name) => {
            if let Some(mapped) = temp_map.get(name) {
                qbe::Value::Temporary(mapped.clone())
            } else {
                qbe::Value::Temporary(name.clone())
            }
        }
        qbe::Value::Const(value) => qbe::Value::Const(*value),
        qbe::Value::SingleConst(value) => qbe::Value::SingleConst(value.clone()),
        qbe::Value::DoubleConst(value) => qbe::Value::DoubleConst(value.clone()),
        qbe::Value::Global(name) => qbe::Value::Global(name.clone()),
    }
}

fn rename_label(label: &str, label_map: &HashMap<String, String>) -> String {
    label_map
        .get(label)
        .cloned()
        .unwrap_or_else(|| label.to_string())
}

fn rename_instr(
    instr: &qbe::Instr,
    temp_map: &HashMap<String, String>,
    label_map: &HashMap<String, String>,
) -> qbe::Instr {
    use qbe::Instr;

    match instr {
        Instr::Add(lhs, rhs) => {
            Instr::Add(rename_value(lhs, temp_map), rename_value(rhs, temp_map))
        }
        Instr::Sub(lhs, rhs) => {
            Instr::Sub(rename_value(lhs, temp_map), rename_value(rhs, temp_map))
        }
        Instr::Mul(lhs, rhs) => {
            Instr::Mul(rename_value(lhs, temp_map), rename_value(rhs, temp_map))
        }
        Instr::Div(lhs, rhs) => {
            Instr::Div(rename_value(lhs, temp_map), rename_value(rhs, temp_map))
        }
        Instr::Rem(lhs, rhs) => {
            Instr::Rem(rename_value(lhs, temp_map), rename_value(rhs, temp_map))
        }
        Instr::Cmp(ty, cmp, lhs, rhs) => Instr::Cmp(
            ty.clone(),
            *cmp,
            rename_value(lhs, temp_map),
            rename_value(rhs, temp_map),
        ),
        Instr::And(lhs, rhs) => {
            Instr::And(rename_value(lhs, temp_map), rename_value(rhs, temp_map))
        }
        Instr::Or(lhs, rhs) => Instr::Or(rename_value(lhs, temp_map), rename_value(rhs, temp_map)),
        Instr::Copy(value) => Instr::Copy(rename_value(value, temp_map)),
        Instr::Ret(value) => Instr::Ret(value.as_ref().map(|value| rename_value(value, temp_map))),
        Instr::Jnz(value, if_true, if_false) => Instr::Jnz(
            rename_value(value, temp_map),
            rename_label(if_true, label_map),
            rename_label(if_false, label_map),
        ),
        Instr::Jmp(label) => Instr::Jmp(rename_label(label, label_map)),
        Instr::Call(name, args, variadic_index) => Instr::Call(
            name.clone(),
            args.iter()
                .map(|(ty, value)| (ty.clone(), rename_value(value, temp_map)))
                .collect(),
            *variadic_index,
        ),
        Instr::Alloc4(size) => Instr::Alloc4(*size),
        Instr::Alloc8(size) => Instr::Alloc8(*size),
        Instr::Alloc16(size) => Instr::Alloc16(*size),
        Instr::Store(ty, destination, value) => Instr::Store(
            ty.clone(),
            rename_value(destination, temp_map),
            rename_value(value, temp_map),
        ),
        Instr::Load(ty, source) => Instr::Load(ty.clone(), rename_value(source, temp_map)),
        Instr::Blit(source, destination, len) => Instr::Blit(
            rename_value(source, temp_map),
            rename_value(destination, temp_map),
            *len,
        ),
        Instr::DbgFile(file) => Instr::DbgFile(file.clone()),
        Instr::DbgLoc(line, column) => Instr::DbgLoc(*line, *column),
        Instr::Udiv(lhs, rhs) => {
            Instr::Udiv(rename_value(lhs, temp_map), rename_value(rhs, temp_map))
        }
        Instr::Urem(lhs, rhs) => {
            Instr::Urem(rename_value(lhs, temp_map), rename_value(rhs, temp_map))
        }
        Instr::Sar(lhs, rhs) => {
            Instr::Sar(rename_value(lhs, temp_map), rename_value(rhs, temp_map))
        }
        Instr::Shr(lhs, rhs) => {
            Instr::Shr(rename_value(lhs, temp_map), rename_value(rhs, temp_map))
        }
        Instr::Shl(lhs, rhs) => {
            Instr::Shl(rename_value(lhs, temp_map), rename_value(rhs, temp_map))
        }
        Instr::Cast(value) => Instr::Cast(rename_value(value, temp_map)),
        Instr::Extsw(value) => Instr::Extsw(rename_value(value, temp_map)),
        Instr::Extuw(value) => Instr::Extuw(rename_value(value, temp_map)),
        Instr::Extsh(value) => Instr::Extsh(rename_value(value, temp_map)),
        Instr::Extuh(value) => Instr::Extuh(rename_value(value, temp_map)),
        Instr::Extsb(value) => Instr::Extsb(rename_value(value, temp_map)),
        Instr::Extub(value) => Instr::Extub(rename_value(value, temp_map)),
        Instr::Exts(value) => Instr::Exts(rename_value(value, temp_map)),
        Instr::Truncd(value) => Instr::Truncd(rename_value(value, temp_map)),
        Instr::Stosi(value) => Instr::Stosi(rename_value(value, temp_map)),
        Instr::Stoui(value) => Instr::Stoui(rename_value(value, temp_map)),
        Instr::Dtosi(value) => Instr::Dtosi(rename_value(value, temp_map)),
        Instr::Dtoui(value) => Instr::Dtoui(rename_value(value, temp_map)),
        Instr::Swtof(value) => Instr::Swtof(rename_value(value, temp_map)),
        Instr::Uwtof(value) => Instr::Uwtof(rename_value(value, temp_map)),
        Instr::Sltof(value) => Instr::Sltof(rename_value(value, temp_map)),
        Instr::Ultof(value) => Instr::Ultof(rename_value(value, temp_map)),
        Instr::Vastart(value) => Instr::Vastart(rename_value(value, temp_map)),
        Instr::Vaarg(ty, value) => Instr::Vaarg(ty.clone(), rename_value(value, temp_map)),
        Instr::Phi(label_a, value_a, label_b, value_b) => Instr::Phi(
            rename_label(label_a, label_map),
            rename_value(value_a, temp_map),
            rename_label(label_b, label_map),
            rename_value(value_b, temp_map),
        ),
        Instr::Hlt => Instr::Hlt,
    }
}

fn reachable_block_indices(function: &qbe::Function) -> HashSet<usize> {
    let mut label_to_index = HashMap::new();
    for (idx, block) in function.blocks.iter().enumerate() {
        label_to_index.insert(block.label.clone(), idx);
    }

    let mut reachable = HashSet::new();
    let mut worklist = vec![0usize];

    while let Some(block_idx) = worklist.pop() {
        if block_idx >= function.blocks.len() || !reachable.insert(block_idx) {
            continue;
        }

        let block = &function.blocks[block_idx];
        let terminator = block.items.iter().rev().find_map(|item| {
            if let qbe::BlockItem::Statement(qbe::Statement::Volatile(instr)) = item {
                Some(instr)
            } else {
                None
            }
        });

        match terminator {
            Some(qbe::Instr::Jmp(target)) => {
                if let Some(next_idx) = label_to_index.get(target) {
                    worklist.push(*next_idx);
                }
            }
            Some(qbe::Instr::Jnz(_, on_true, on_false)) => {
                if let Some(next_idx) = label_to_index.get(on_true) {
                    worklist.push(*next_idx);
                }
                if let Some(next_idx) = label_to_index.get(on_false) {
                    worklist.push(*next_idx);
                }
            }
            Some(qbe::Instr::Ret(_)) | Some(qbe::Instr::Hlt) => {}
            _ => {
                if block_idx + 1 < function.blocks.len() {
                    worklist.push(block_idx + 1);
                }
            }
        }
    }

    reachable
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ir, parser, tokenizer};
    use std::collections::HashMap;

    fn resolve_program(source: &str) -> ResolvedProgram {
        let tokens = tokenizer::tokenize(source.to_string()).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        ir::resolve(ast).expect("resolve source")
    }

    fn compile_qbe(program: &ResolvedProgram) -> qbe::Module {
        crate::qbe_backend::compile(program.clone())
    }

    fn site_function_map(
        program: &ResolvedProgram,
    ) -> anyhow::Result<(Vec<ObligationSite>, HashMap<String, qbe::Function>)> {
        let invariants = discover_invariants(program)?;
        let reachable = reachable_user_functions(program, "main")?;
        let sites = collect_obligation_sites(program, &reachable, &invariants)?;
        let module = compile_qbe(program);
        let function_map = module
            .functions
            .iter()
            .map(|function| (function.name.clone(), function.clone()))
            .collect::<HashMap<_, _>>();
        Ok((sites, function_map))
    }

    #[test]
    fn discovers_valid_struct_invariant() {
        let program = resolve_program(
            r#"
struct Foo {
	x: I32,
}

invariant positive_x "positive .x" for (v: Foo) {
	return v.x >= 0
}

fun make_foo() -> Foo {
	return Foo struct { x: 0, }
}

fun main() -> I32 {
	f = make_foo()
	return 0
}
	"#,
        );

        let invariants = discover_invariants(&program).expect("discover invariants");
        let binding = invariants.get("Foo").expect("missing Foo invariant");
        assert_eq!(binding.function_name, "__struct__Foo__invariant");
        assert_eq!(binding.display_name, "positive .x");
        assert_eq!(binding.identifier.as_deref(), Some("positive_x"));
    }

    #[test]
    fn supports_legacy_invariant_function_name_pattern() {
        let program = resolve_program(
            r#"
struct LegacyFoo {
	x: I32,
}

fun __struct__LegacyFoo__invariant(v: LegacyFoo) -> Bool {
	return v.x >= 0
}

fun main() -> I32 {
	return 0
}
"#,
        );

        let invariants = discover_invariants(&program).expect("discover invariants");
        let binding = invariants
            .get("LegacyFoo")
            .expect("missing legacy Foo invariant");
        assert_eq!(binding.function_name, "__struct__LegacyFoo__invariant");
        assert_eq!(binding.display_name, "__struct__LegacyFoo__invariant");
        assert_eq!(binding.identifier, None);
    }

    #[test]
    fn rejects_malformed_invariant_signature() {
        let source = r#"
struct Foo {
	x: I32,
}

fun __struct__Foo__invariant(v: Foo) -> I32 {
	return 1
}

fun main() -> I32 {
	return 0
}
		"#
        .to_string();
        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = ir::resolve(ast).expect_err("invariant should be rejected");
        assert!(err
            .to_string()
            .contains("must have signature fun __struct__Foo__invariant(v: Foo) -> Bool"));
    }

    #[test]
    fn supports_generic_concrete_invariant_names() {
        let program = resolve_program(
            r#"
generic Box[T] {
	struct Box {
		value: T,
	}
}

specialize BoxI32 = Box[I32]

invariant non_negative_value "value must be non-negative" for (v: BoxI32) {
	return v.value >= 0
}

fun make_box(v: I32) -> BoxI32 {
	return BoxI32 struct { value: v, }
}

fun main() -> I32 {
	b = make_box(1)
	return 0
}
	"#,
        );

        let invariants = discover_invariants(&program).expect("discover invariants");
        let binding = invariants.get("BoxI32").expect("missing BoxI32 invariant");
        assert_eq!(binding.function_name, "__struct__BoxI32__invariant");
        assert_eq!(binding.display_name, "value must be non-negative");
        assert_eq!(binding.identifier.as_deref(), Some("non_negative_value"));
    }

    #[test]
    fn excludes_invariant_function_bodies_from_site_collection() {
        let program = resolve_program(
            r#"
struct Foo {
	x: I32,
}

fun make_foo(v: I32) -> Foo {
	return Foo struct { x: v, }
}

invariant "x must be non-negative" for (v: Foo) {
	tmp = make_foo(0)
	return v.x >= 0
}

fun main() -> I32 {
	f = make_foo(1)
	return 0
}
"#,
        );

        let invariants = discover_invariants(&program).expect("discover invariants");
        let reachable = reachable_user_functions(&program, "main").expect("reachable functions");
        let sites = collect_obligation_sites(&program, &reachable, &invariants).expect("sites");

        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].caller, "main");
        assert_eq!(sites[0].callee, "make_foo");
        assert_eq!(sites[0].callee_call_ordinal, 0);
    }

    #[test]
    fn assigns_deterministic_callee_ordinals_per_caller() {
        let program = resolve_program(
            r#"
struct Foo {
	x: I32,
}

invariant "x must be non-negative" for (v: Foo) {
	return v.x >= 0
}

fun make_foo(v: I32) -> Foo {
	return Foo struct { x: v, }
}

fun main() -> I32 {
	a = make_foo(1)
	b = make_foo(2)
	return 0
}
"#,
        );

        let invariants = discover_invariants(&program).expect("discover invariants");
        let reachable = reachable_user_functions(&program, "main").expect("reachable functions");
        let sites = collect_obligation_sites(&program, &reachable, &invariants).expect("sites");

        assert_eq!(sites.len(), 2);
        assert_eq!(sites[0].callee_call_ordinal, 0);
        assert_eq!(sites[1].callee_call_ordinal, 1);
    }

    #[test]
    fn supports_while_without_invariant_obligation_sites() {
        let program = resolve_program(
            r#"
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
	i = 4
	while i > 0 {
		i = sub(i, 1)
	}
	c = make_counter(1)
	return 0
}
"#,
        );

        let (sites, function_map) = site_function_map(&program).expect("build sites and qbe");
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].callee, "make_counter");
        let checker =
            build_site_checker_function(&function_map, &sites[0]).expect("build site checker");
        let smt = qbe_smt::qbe_to_smt(
            &checker,
            &qbe_smt::EncodeOptions {
                assume_main_argc_non_negative: should_assume_main_argc_non_negative(
                    &sites[0], &checker,
                ),
                first_arg_i32_range: None,
            },
        )
        .expect("encode checker to CHC");
        assert!(smt.contains("(query bad)"));
    }

    #[test]
    fn supports_while_with_invariant_obligation_sites_inside_loop_in_qbe_native_flow() {
        let program = resolve_program(
            r#"
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
	i = 1
	while i > 0 {
		c = make_counter(0)
		i = 0
	}
	return 0
}
"#,
        );

        let (sites, function_map) = site_function_map(&program).expect("build sites and qbe");
        assert_eq!(sites.len(), 1);
        let checker =
            build_site_checker_function(&function_map, &sites[0]).expect("build site checker");
        qbe_smt::qbe_to_smt(
            &checker,
            &qbe_smt::EncodeOptions {
                assume_main_argc_non_negative: should_assume_main_argc_non_negative(
                    &sites[0], &checker,
                ),
                first_arg_i32_range: None,
            },
        )
        .expect("while-with-site checker should encode in qbe-native flow");
    }

    #[test]
    fn rejects_recursion_in_verified_paths() {
        let program = resolve_program(
            r#"
struct Foo {
	x: I32,
}

invariant "x must be non-negative" for (v: Foo) {
	return v.x >= 0
}

fun loop_make(n: I32) -> Foo {
	if n == 0 {
		return Foo struct { x: 0, }
	} else {
		return loop_make(sub(n, 1))
	}
}

fun main() -> I32 {
	v = loop_make(2)
	return 0
}
"#,
        );

        let reachable =
            reachable_user_functions(&program, "main").expect("collect reachable functions");
        let err = reject_recursion_cycles(&program, "main", &reachable)
            .expect_err("recursion should be rejected");
        assert!(err
            .to_string()
            .contains("recursion cycles are unsupported by struct invariant verification"));
    }

    #[test]
    fn modeled_clib_memcpy_encodes_in_qbe_native_flow() {
        let program = resolve_program(
            r#"
struct Packet {
	ptr: PtrInt,
	len: PtrInt,
}

invariant "packet pointer is reflexive" for (v: Packet) {
	return v.ptr == v.ptr
}

fun make_packet(dst: PtrInt, src: PtrInt, n: PtrInt) -> Packet {
	copied = Clib.memcpy(dst, src, n)
	return Packet struct { ptr: copied, len: n, }
}

fun main(argc: I32, argv: PtrInt) -> I32 {
	p = make_packet(argv, argv, argv)
	return argc
}
"#,
        );

        let (sites, function_map) = site_function_map(&program).expect("build sites and qbe");
        assert_eq!(sites.len(), 1);
        let checker =
            build_site_checker_function(&function_map, &sites[0]).expect("build site checker");
        let smt = qbe_smt::qbe_to_smt(
            &checker,
            &qbe_smt::EncodeOptions {
                assume_main_argc_non_negative: should_assume_main_argc_non_negative(
                    &sites[0], &checker,
                ),
                first_arg_i32_range: None,
            },
        )
        .expect("memcpy-backed checker should encode");
        assert!(
            smt.contains("(ite (bvule"),
            "expected bounded branch in SMT: {smt}"
        );
    }

    #[test]
    fn unknown_external_calls_fail_closed_in_qbe_native_flow() {
        let program = resolve_program(
            r#"
struct Foo {
	x: I32,
}

invariant "x must be one" for (v: Foo) {
	return v.x == 1
}

extern fun unknown(v: I32) -> I32

fun make_foo() -> Foo {
	x = unknown(1)
	return Foo struct { x: x, }
}

fun main() -> I32 {
	f = make_foo()
	return 0
}
"#,
        );

        let (sites, function_map) = site_function_map(&program).expect("build sites and qbe");
        assert_eq!(sites.len(), 1);
        let checker =
            build_site_checker_function(&function_map, &sites[0]).expect("build site checker");
        let err = qbe_smt::qbe_to_smt(
            &checker,
            &qbe_smt::EncodeOptions {
                assume_main_argc_non_negative: should_assume_main_argc_non_negative(
                    &sites[0], &checker,
                ),
                first_arg_i32_range: None,
            },
        )
        .expect_err("unsupported external call must fail closed");
        assert!(
            err.to_string().contains("unsupported"),
            "expected fail-closed unsupported error, got: {err}"
        );
    }

    #[test]
    fn main_argc_gets_non_negative_constraint() {
        let program = resolve_program(
            r#"
struct Counter {
	value: I32,
}

invariant "counter non-negative" for (v: Counter) {
	return v.value >= 0
}

fun make_counter(v: I32) -> Counter {
	return Counter struct { value: v, }
}

fun main(argc: I32, argv: I64) -> I32 {
	c = make_counter(argc)
	return 0
}
"#,
        );

        let (sites, function_map) = site_function_map(&program).expect("build sites and qbe");
        assert_eq!(sites.len(), 1);
        let checker =
            build_site_checker_function(&function_map, &sites[0]).expect("build site checker");
        let smt = qbe_smt::qbe_to_smt(
            &checker,
            &qbe_smt::EncodeOptions {
                assume_main_argc_non_negative: should_assume_main_argc_non_negative(
                    &sites[0], &checker,
                ),
                first_arg_i32_range: None,
            },
        )
        .expect("encode checker to CHC");
        assert!(
            smt.contains("(bvsge (select regs (_ bv") && smt.contains("(_ bv0 64))"),
            "SMT should include argc >= 0 constraint: {smt}"
        );
    }
}
