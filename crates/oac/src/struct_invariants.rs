use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use anyhow::Context;

use crate::ir::{ResolvedProgram, TypeDef};
use crate::parser::{Expression, Literal, Op, Statement, UnaryOp};

const INVARIANT_PREFIX: &str = "__struct__";
const INVARIANT_SUFFIX: &str = "__invariant";
const Z3_TIMEOUT_SECONDS: u64 = 10;

pub fn verify_struct_invariants(
    program: &ResolvedProgram,
    target_dir: &Path,
) -> anyhow::Result<()> {
    let (sites, formulas) = build_obligations(program)?;
    if sites.is_empty() {
        return Ok(());
    }
    solve_obligations(&sites, &formulas, target_dir)
}

fn build_obligations(
    program: &ResolvedProgram,
) -> anyhow::Result<(Vec<ObligationSite>, HashMap<String, SymExpr>)> {
    let invariant_by_struct = discover_invariants(program)?;
    let reachable = reachable_user_functions(program, "main")?;
    let sites = collect_obligation_sites(program, &reachable, &invariant_by_struct)?;
    if sites.is_empty() {
        return Ok((sites, HashMap::new()));
    }

    let mut analyzer = Analyzer::new(program, invariant_by_struct, &sites);
    let main_def = program
        .function_definitions
        .get("main")
        .context("main function not found during struct invariant verification")?;

    let mut main_args = Vec::with_capacity(main_def.sig.parameters.len());
    let mut entry_constraints = vec![];
    for parameter in &main_def.sig.parameters {
        main_args.push(analyzer.havoc_value(&parameter.ty, &mut vec![])?);
    }
    if main_def.sig.parameters.len() == 2 {
        let Some(SymValue::Scalar {
            expr: argc_expr, ..
        }) = main_args.first()
        else {
            return Err(anyhow::anyhow!(
                "internal verifier error: expected scalar argc as first main argument"
            ));
        };
        if argc_expr.sort() != Sort::Int {
            return Err(anyhow::anyhow!(
                "internal verifier error: expected integer-like argc symbolic sort"
            ));
        }
        entry_constraints.push(SymExpr::Ge(
            Box::new(argc_expr.clone()),
            Box::new(SymExpr::IntConst(0)),
        ));
    }
    analyzer.set_entry_constraint(and_all(entry_constraints));

    analyzer.execute_function("main", main_args, &mut vec![])?;
    let formulas = analyzer.finish_site_formulas(&sites);
    Ok((sites, formulas))
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct SiteKey {
    function: String,
    top_statement_index: usize,
    expr_path: String,
}

#[derive(Clone, Debug)]
struct ObligationSite {
    id: String,
    caller: String,
    callee: String,
    struct_name: String,
    invariant_fn: String,
    key: SiteKey,
}

fn discover_invariants(program: &ResolvedProgram) -> anyhow::Result<HashMap<String, String>> {
    let mut invariant_by_struct = HashMap::new();

    for (name, func_def) in &program.function_definitions {
        let Some(struct_name) = parse_invariant_name(name) else {
            continue;
        };

        let ty = program.type_definitions.get(struct_name).ok_or_else(|| {
            anyhow::anyhow!("invariant {} targets unknown type {}", name, struct_name)
        })?;
        if !matches!(ty, TypeDef::Struct(_)) {
            return Err(anyhow::anyhow!(
                "invariant {} must target a struct type, but {} is not a struct",
                name,
                struct_name
            ));
        }

        let sig = &func_def.sig;
        if sig.parameters.len() != 1 {
            return Err(anyhow::anyhow!(
                "invariant {} must have exactly one parameter of type {}",
                name,
                struct_name
            ));
        }
        if sig.parameters[0].ty != struct_name {
            return Err(anyhow::anyhow!(
                "invariant {} must have signature fun {}(v: {}) -> Bool",
                name,
                name,
                struct_name
            ));
        }
        if sig.return_type != "Bool" {
            return Err(anyhow::anyhow!(
                "invariant {} must return Bool, got {}",
                name,
                sig.return_type
            ));
        }

        if let Some(existing) = invariant_by_struct.insert(struct_name.to_string(), name.clone()) {
            return Err(anyhow::anyhow!(
                "struct {} has multiple invariants: {} and {}",
                struct_name,
                existing,
                name
            ));
        }
    }

    Ok(invariant_by_struct)
}

fn parse_invariant_name(name: &str) -> Option<&str> {
    if !name.starts_with(INVARIANT_PREFIX) || !name.ends_with(INVARIANT_SUFFIX) {
        return None;
    }

    let middle = &name[INVARIANT_PREFIX.len()..name.len() - INVARIANT_SUFFIX.len()];
    if middle.is_empty() {
        None
    } else {
        Some(middle)
    }
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

fn collect_obligation_sites(
    program: &ResolvedProgram,
    reachable: &HashSet<String>,
    invariant_by_struct: &HashMap<String, String>,
) -> anyhow::Result<Vec<ObligationSite>> {
    let mut sites = Vec::new();
    let mut functions = reachable.iter().cloned().collect::<Vec<_>>();
    functions.sort();

    for function_name in functions {
        if parse_invariant_name(&function_name).is_some() {
            continue;
        }

        let function = program
            .function_definitions
            .get(&function_name)
            .ok_or_else(|| anyhow::anyhow!("missing function definition for {}", function_name))?;

        for (top_statement_index, statement) in function.body.iter().enumerate() {
            let mut expr_index_map = HashMap::new();
            let mut expr_index = 0usize;
            index_statement_expressions(statement, "", &mut expr_index, &mut expr_index_map);

            let mut call_nodes = Vec::new();
            collect_call_nodes_from_statement(statement, "", &mut call_nodes);

            for (expr_path, callee_name) in call_nodes {
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

                let Some(invariant_fn) = invariant_by_struct.get(return_type) else {
                    continue;
                };

                let expr_index = *expr_index_map.get(&expr_path).ok_or_else(|| {
                    anyhow::anyhow!("missing expression index for path {}", expr_path)
                })?;

                let id = format!("{}#{}#{}", function_name, top_statement_index, expr_index);
                let key = SiteKey {
                    function: function_name.clone(),
                    top_statement_index,
                    expr_path: expr_path.clone(),
                };

                sites.push(ObligationSite {
                    id,
                    caller: function_name.clone(),
                    callee: callee_name,
                    struct_name: return_type.clone(),
                    invariant_fn: invariant_fn.clone(),
                    key,
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

#[derive(Clone, Debug, PartialEq, Eq)]
enum Sort {
    Bool,
    Int,
}

#[derive(Clone, Debug)]
enum SymExpr {
    BoolConst(bool),
    IntConst(i64),
    Var {
        name: String,
        sort: Sort,
    },
    Not(Box<SymExpr>),
    And(Vec<SymExpr>),
    Or(Vec<SymExpr>),
    Add(Box<SymExpr>, Box<SymExpr>),
    Sub(Box<SymExpr>, Box<SymExpr>),
    Mul(Box<SymExpr>, Box<SymExpr>),
    Div(Box<SymExpr>, Box<SymExpr>),
    Eq(Box<SymExpr>, Box<SymExpr>),
    Ne(Box<SymExpr>, Box<SymExpr>),
    Lt(Box<SymExpr>, Box<SymExpr>),
    Gt(Box<SymExpr>, Box<SymExpr>),
    Le(Box<SymExpr>, Box<SymExpr>),
    Ge(Box<SymExpr>, Box<SymExpr>),
    Ite {
        cond: Box<SymExpr>,
        then_expr: Box<SymExpr>,
        else_expr: Box<SymExpr>,
        sort: Sort,
    },
}

impl SymExpr {
    fn sort(&self) -> Sort {
        match self {
            SymExpr::BoolConst(_) => Sort::Bool,
            SymExpr::IntConst(_) => Sort::Int,
            SymExpr::Var { sort, .. } => sort.clone(),
            SymExpr::Not(_) => Sort::Bool,
            SymExpr::And(_) => Sort::Bool,
            SymExpr::Or(_) => Sort::Bool,
            SymExpr::Add(_, _) => Sort::Int,
            SymExpr::Sub(_, _) => Sort::Int,
            SymExpr::Mul(_, _) => Sort::Int,
            SymExpr::Div(_, _) => Sort::Int,
            SymExpr::Eq(_, _) => Sort::Bool,
            SymExpr::Ne(_, _) => Sort::Bool,
            SymExpr::Lt(_, _) => Sort::Bool,
            SymExpr::Gt(_, _) => Sort::Bool,
            SymExpr::Le(_, _) => Sort::Bool,
            SymExpr::Ge(_, _) => Sort::Bool,
            SymExpr::Ite { sort, .. } => sort.clone(),
        }
    }
}

#[derive(Clone, Debug)]
enum SymValue {
    Scalar {
        ty: String,
        expr: SymExpr,
    },
    Struct {
        ty: String,
        fields: HashMap<String, SymValue>,
    },
}

impl SymValue {
    fn type_name(&self) -> &str {
        match self {
            SymValue::Scalar { ty, .. } => ty,
            SymValue::Struct { ty, .. } => ty,
        }
    }
}

#[derive(Clone)]
struct ExecState {
    env: HashMap<String, SymValue>,
    path: SymExpr,
}

#[derive(Clone)]
struct ReturnState {
    path: SymExpr,
    value: SymValue,
}

struct Analyzer<'a> {
    program: &'a ResolvedProgram,
    site_by_key: HashMap<SiteKey, ObligationSite>,
    disjuncts_by_site: HashMap<String, Vec<SymExpr>>,
    entry_constraint: SymExpr,
    fresh_counter: u64,
}

impl<'a> Analyzer<'a> {
    fn new(
        program: &'a ResolvedProgram,
        _invariant_by_struct: HashMap<String, String>,
        sites: &[ObligationSite],
    ) -> Self {
        let mut site_by_key = HashMap::new();
        for site in sites {
            site_by_key.insert(site.key.clone(), site.clone());
        }

        Self {
            program,
            site_by_key,
            disjuncts_by_site: HashMap::new(),
            entry_constraint: SymExpr::BoolConst(true),
            fresh_counter: 0,
        }
    }

    fn set_entry_constraint(&mut self, constraint: SymExpr) {
        self.entry_constraint = constraint;
    }

    fn finish_site_formulas(&self, sites: &[ObligationSite]) -> HashMap<String, SymExpr> {
        let mut out = HashMap::new();
        for site in sites {
            let disjuncts = self
                .disjuncts_by_site
                .get(&site.id)
                .cloned()
                .unwrap_or_default();
            out.insert(site.id.clone(), or_all(disjuncts));
        }
        out
    }

    fn next_name(&mut self, prefix: &str) -> String {
        let name = format!("{}_{}", sanitize_ident(prefix), self.fresh_counter);
        self.fresh_counter += 1;
        name
    }

    fn fresh_int_expr(&mut self, prefix: &str) -> SymExpr {
        SymExpr::Var {
            name: self.next_name(prefix),
            sort: Sort::Int,
        }
    }

    fn fresh_bool_expr(&mut self, prefix: &str) -> SymExpr {
        SymExpr::Var {
            name: self.next_name(prefix),
            sort: Sort::Bool,
        }
    }

    fn havoc_value(&mut self, ty: &str, stack: &mut Vec<String>) -> anyhow::Result<SymValue> {
        if ty == "Bool" {
            return Ok(SymValue::Scalar {
                ty: ty.to_string(),
                expr: self.fresh_bool_expr("havoc_bool"),
            });
        }

        if let Some(TypeDef::Struct(struct_def)) = self.program.type_definitions.get(ty) {
            if stack.contains(&struct_def.name) {
                return Err(anyhow::anyhow!(
                    "unsupported recursive struct symbolic havoc for type {}",
                    struct_def.name
                ));
            }
            stack.push(struct_def.name.clone());
            let mut fields = HashMap::new();
            for field in &struct_def.struct_fields {
                let value = self.havoc_value(&field.ty, stack)?;
                fields.insert(field.name.clone(), value);
            }
            stack.pop();
            return Ok(SymValue::Struct {
                ty: struct_def.name.clone(),
                fields,
            });
        }

        Ok(SymValue::Scalar {
            ty: ty.to_string(),
            expr: self.fresh_int_expr(&format!("havoc_{}", ty)),
        })
    }

    fn execute_function(
        &mut self,
        function_name: &str,
        args: Vec<SymValue>,
        call_stack: &mut Vec<String>,
    ) -> anyhow::Result<SymValue> {
        if call_stack.iter().any(|name| name == function_name) {
            let mut cycle = call_stack.join(" -> ");
            if !cycle.is_empty() {
                cycle.push_str(" -> ");
            }
            cycle.push_str(function_name);
            return Err(anyhow::anyhow!(
                "recursion cycles are unsupported by struct invariant verification: {}",
                cycle
            ));
        }

        call_stack.push(function_name.to_string());

        let function = self
            .program
            .function_definitions
            .get(function_name)
            .ok_or_else(|| anyhow::anyhow!("missing function definition for {}", function_name))?
            .clone();

        if function.sig.parameters.len() != args.len() {
            call_stack.pop();
            return Err(anyhow::anyhow!(
                "mismatched argument count for {}: expected {}, got {}",
                function_name,
                function.sig.parameters.len(),
                args.len()
            ));
        }

        let mut env = HashMap::new();
        for (param, arg) in function.sig.parameters.iter().zip(args) {
            env.insert(param.name.clone(), arg);
        }

        let mut active_states = vec![ExecState {
            env,
            path: SymExpr::BoolConst(true),
        }];
        let mut returns = Vec::new();

        for (top_statement_index, statement) in function.body.iter().enumerate() {
            active_states = self.execute_statement_batch(
                function_name,
                top_statement_index,
                "",
                statement,
                active_states,
                &mut returns,
                call_stack,
            )?;
        }

        let mut missing_return = false;
        for state in &active_states {
            if !is_false(&state.path) {
                missing_return = true;
                break;
            }
        }

        call_stack.pop();

        if missing_return {
            return Err(anyhow::anyhow!(
                "unsupported function {}: missing return on a reachable path",
                function_name
            ));
        }
        if returns.is_empty() {
            return Err(anyhow::anyhow!(
                "unsupported function {}: no return values were collected",
                function_name
            ));
        }

        merge_return_states(returns)
    }

    fn execute_statement_batch(
        &mut self,
        function_name: &str,
        top_statement_index: usize,
        statement_path: &str,
        statement: &Statement,
        states: Vec<ExecState>,
        returns: &mut Vec<ReturnState>,
        call_stack: &mut Vec<String>,
    ) -> anyhow::Result<Vec<ExecState>> {
        let mut next_states = Vec::new();

        for state in states {
            if is_false(&state.path) {
                continue;
            }

            let produced = self.execute_statement_single(
                function_name,
                top_statement_index,
                statement_path,
                statement,
                state,
                returns,
                call_stack,
            )?;
            next_states.extend(produced.into_iter().filter(|s| !is_false(&s.path)));
        }

        Ok(next_states)
    }

    fn execute_statement_single(
        &mut self,
        function_name: &str,
        top_statement_index: usize,
        statement_path: &str,
        statement: &Statement,
        mut state: ExecState,
        returns: &mut Vec<ReturnState>,
        call_stack: &mut Vec<String>,
    ) -> anyhow::Result<Vec<ExecState>> {
        match statement {
            Statement::StructDef { .. } => Err(anyhow::anyhow!(
                "unsupported statement in verification: inline struct definitions"
            )),
            Statement::Assign { variable, value } => {
                let expr_path = join_path(statement_path, "assign.value");
                let value = self.eval_expression(
                    function_name,
                    top_statement_index,
                    &expr_path,
                    value,
                    &state,
                    call_stack,
                )?;
                state.env.insert(variable.clone(), value);
                Ok(vec![state])
            }
            Statement::Return { expr } => {
                let expr_path = join_path(statement_path, "return.expr");
                let value = self.eval_expression(
                    function_name,
                    top_statement_index,
                    &expr_path,
                    expr,
                    &state,
                    call_stack,
                )?;
                returns.push(ReturnState {
                    path: state.path,
                    value,
                });
                Ok(vec![])
            }
            Statement::Expression { expr } => {
                let expr_path = join_path(statement_path, "expr.expr");
                self.eval_expression(
                    function_name,
                    top_statement_index,
                    &expr_path,
                    expr,
                    &state,
                    call_stack,
                )?;
                Ok(vec![state])
            }
            Statement::Conditional {
                condition,
                body,
                else_body,
            } => {
                let cond_path = join_path(statement_path, "if.cond");
                let cond_value = self.eval_expression(
                    function_name,
                    top_statement_index,
                    &cond_path,
                    condition,
                    &state,
                    call_stack,
                )?;
                let cond = expect_bool_expr(cond_value, "if condition")?;

                let mut then_state = state.clone();
                then_state.path = and_all(vec![then_state.path, cond.clone()]);

                let mut else_state = state;
                else_state.path = and_all(vec![else_state.path, not_expr(cond)]);

                let then_states = self.execute_block(
                    function_name,
                    top_statement_index,
                    &join_path(statement_path, "if.then"),
                    body,
                    vec![then_state],
                    returns,
                    call_stack,
                )?;

                let else_states = if let Some(else_body) = else_body {
                    self.execute_block(
                        function_name,
                        top_statement_index,
                        &join_path(statement_path, "if.else"),
                        else_body,
                        vec![else_state],
                        returns,
                        call_stack,
                    )?
                } else {
                    vec![else_state]
                };

                let mut out = then_states;
                out.extend(else_states);
                Ok(out)
            }
            Statement::While { body, .. } => {
                let cond_prefix = join_path(statement_path, "while.cond");
                let body_prefix = join_path(statement_path, "while.body");
                if self.loop_region_has_obligation_sites(
                    function_name,
                    top_statement_index,
                    &cond_prefix,
                    &body_prefix,
                ) {
                    return Err(anyhow::anyhow!(
                        "unsupported statement in struct invariant verification: while loops containing struct invariant obligation call sites"
                    ));
                }

                if block_contains_return(body) {
                    return Err(anyhow::anyhow!(
                        "unsupported statement in struct invariant verification: while loops containing return statements"
                    ));
                }

                let mut assigned = HashSet::new();
                collect_assigned_variables(body, &mut assigned);

                let mut assigned_types = Vec::new();
                for variable in assigned {
                    if let Some(current) = state.env.get(&variable) {
                        assigned_types.push((variable, current.type_name().to_string()));
                    }
                }

                for (variable, ty) in assigned_types {
                    let havoc = self.havoc_value(&ty, &mut vec![])?;
                    state.env.insert(variable, havoc);
                }

                Ok(vec![state])
            }
            Statement::Match { .. } => Err(anyhow::anyhow!(
                "unsupported statement in struct invariant verification: match"
            )),
        }
    }

    fn execute_block(
        &mut self,
        function_name: &str,
        top_statement_index: usize,
        base_path: &str,
        statements: &[Statement],
        mut states: Vec<ExecState>,
        returns: &mut Vec<ReturnState>,
        call_stack: &mut Vec<String>,
    ) -> anyhow::Result<Vec<ExecState>> {
        for (i, statement) in statements.iter().enumerate() {
            states = self.execute_statement_batch(
                function_name,
                top_statement_index,
                &join_path(base_path, &i.to_string()),
                statement,
                states,
                returns,
                call_stack,
            )?;
        }
        Ok(states)
    }

    fn eval_expression(
        &mut self,
        function_name: &str,
        top_statement_index: usize,
        expr_path: &str,
        expr: &Expression,
        state: &ExecState,
        call_stack: &mut Vec<String>,
    ) -> anyhow::Result<SymValue> {
        match expr {
            Expression::Literal(Literal::Int(value)) => Ok(SymValue::Scalar {
                ty: "I32".to_string(),
                expr: SymExpr::IntConst(*value as i64),
            }),
            Expression::Literal(Literal::Bool(value)) => Ok(SymValue::Scalar {
                ty: "Bool".to_string(),
                expr: SymExpr::BoolConst(*value),
            }),
            Expression::Literal(Literal::String(value)) => Ok(SymValue::Scalar {
                ty: "String".to_string(),
                expr: SymExpr::IntConst(stable_string_const(value)),
            }),
            Expression::Variable(name) => {
                state.env.get(name).cloned().ok_or_else(|| {
                    anyhow::anyhow!("unknown variable {} in symbolic execution", name)
                })
            }
            Expression::FieldAccess {
                struct_variable,
                field,
            } => {
                let struct_value = state.env.get(struct_variable).ok_or_else(|| {
                    anyhow::anyhow!(
                        "unsupported field access base {} during verification",
                        struct_variable
                    )
                })?;
                let SymValue::Struct { fields, .. } = struct_value else {
                    return Err(anyhow::anyhow!(
                        "field access {}.{} requires struct value",
                        struct_variable,
                        field
                    ));
                };
                fields.get(field).cloned().ok_or_else(|| {
                    anyhow::anyhow!("unknown field {} on {}", field, struct_variable)
                })
            }
            Expression::StructValue {
                struct_name,
                field_values,
            } => {
                let TypeDef::Struct(struct_def) = self
                    .program
                    .type_definitions
                    .get(struct_name)
                    .ok_or_else(|| anyhow::anyhow!("unknown struct type {}", struct_name))?
                else {
                    return Err(anyhow::anyhow!("{} is not a struct", struct_name));
                };

                let mut values_by_name = HashMap::new();
                for (name, value_expr) in field_values {
                    let value = self.eval_expression(
                        function_name,
                        top_statement_index,
                        &join_path(expr_path, &format!("struct.field.{}", name)),
                        value_expr,
                        state,
                        call_stack,
                    )?;
                    values_by_name.insert(name.clone(), value);
                }

                let mut fields = HashMap::new();
                for field in &struct_def.struct_fields {
                    let value = values_by_name.remove(&field.name).ok_or_else(|| {
                        anyhow::anyhow!(
                            "missing field {} in struct literal {}",
                            field.name,
                            struct_name
                        )
                    })?;
                    fields.insert(field.name.clone(), value);
                }

                if !values_by_name.is_empty() {
                    let extras = values_by_name
                        .keys()
                        .cloned()
                        .collect::<Vec<_>>()
                        .join(", ");
                    return Err(anyhow::anyhow!(
                        "unknown fields in struct literal {}: {}",
                        struct_name,
                        extras
                    ));
                }

                Ok(SymValue::Struct {
                    ty: struct_name.clone(),
                    fields,
                })
            }
            Expression::UnaryOp(op, expr) => {
                let inner = self.eval_expression(
                    function_name,
                    top_statement_index,
                    &join_path(expr_path, "unary.expr"),
                    expr,
                    state,
                    call_stack,
                )?;
                match op {
                    UnaryOp::Not => {
                        let bool_expr = expect_bool_expr(inner, "unary !")?;
                        Ok(SymValue::Scalar {
                            ty: "Bool".to_string(),
                            expr: not_expr(bool_expr),
                        })
                    }
                }
            }
            Expression::BinOp(op, lhs, rhs) => {
                let lhs = self.eval_expression(
                    function_name,
                    top_statement_index,
                    &join_path(expr_path, "bin.lhs"),
                    lhs,
                    state,
                    call_stack,
                )?;
                let rhs = self.eval_expression(
                    function_name,
                    top_statement_index,
                    &join_path(expr_path, "bin.rhs"),
                    rhs,
                    state,
                    call_stack,
                )?;
                apply_binop(*op, lhs, rhs)
            }
            Expression::Call(name, args) => {
                let mut arg_values = Vec::with_capacity(args.len());
                for (i, arg) in args.iter().enumerate() {
                    arg_values.push(self.eval_expression(
                        function_name,
                        top_statement_index,
                        &join_path(expr_path, &format!("call.arg.{}", i)),
                        arg,
                        state,
                        call_stack,
                    )?);
                }

                let sig = self
                    .program
                    .function_sigs
                    .get(name)
                    .ok_or_else(|| {
                        anyhow::anyhow!("unknown function {} in symbolic execution", name)
                    })?
                    .clone();

                let value = if self.program.function_definitions.contains_key(name) {
                    self.execute_function(name, arg_values, call_stack)?
                } else {
                    self.havoc_value(&sig.return_type, &mut vec![])?
                };

                let key = SiteKey {
                    function: function_name.to_string(),
                    top_statement_index,
                    expr_path: expr_path.to_string(),
                };
                if let Some(site) = self.site_by_key.get(&key).cloned() {
                    let invariant_value =
                        self.execute_function(&site.invariant_fn, vec![value.clone()], call_stack)?;
                    let invariant_bool = expect_bool_expr(invariant_value, "invariant return")?;
                    let violation = and_all(vec![
                        self.entry_constraint.clone(),
                        state.path.clone(),
                        not_expr(invariant_bool),
                    ]);
                    self.disjuncts_by_site
                        .entry(site.id)
                        .or_default()
                        .push(violation);
                }

                Ok(value)
            }
            Expression::PostfixCall { .. } => Err(anyhow::anyhow!(
                "unsupported expression in struct invariant verification: postfix call"
            )),
            Expression::Match { .. } => Err(anyhow::anyhow!(
                "unsupported expression in struct invariant verification: match"
            )),
        }
    }

    fn loop_region_has_obligation_sites(
        &self,
        function_name: &str,
        top_statement_index: usize,
        cond_prefix: &str,
        body_prefix: &str,
    ) -> bool {
        self.site_by_key.keys().any(|key| {
            key.function == function_name
                && key.top_statement_index == top_statement_index
                && (path_has_prefix(&key.expr_path, cond_prefix)
                    || path_has_prefix(&key.expr_path, body_prefix))
        })
    }
}

fn path_has_prefix(path: &str, prefix: &str) -> bool {
    path == prefix || path.starts_with(&format!("{}.", prefix))
}

fn block_contains_return(statements: &[Statement]) -> bool {
    statements.iter().any(statement_contains_return)
}

fn statement_contains_return(statement: &Statement) -> bool {
    match statement {
        Statement::Return { .. } => true,
        Statement::Conditional {
            body, else_body, ..
        } => {
            block_contains_return(body)
                || else_body
                    .as_ref()
                    .map(|else_body| block_contains_return(else_body))
                    .unwrap_or(false)
        }
        Statement::While { body, .. } => block_contains_return(body),
        Statement::Match { arms, .. } => arms.iter().any(|arm| block_contains_return(&arm.body)),
        Statement::StructDef { .. } | Statement::Assign { .. } | Statement::Expression { .. } => {
            false
        }
    }
}

fn collect_assigned_variables(statements: &[Statement], out: &mut HashSet<String>) {
    for statement in statements {
        match statement {
            Statement::Assign { variable, .. } => {
                out.insert(variable.clone());
            }
            Statement::Conditional {
                body, else_body, ..
            } => {
                collect_assigned_variables(body, out);
                if let Some(else_body) = else_body {
                    collect_assigned_variables(else_body, out);
                }
            }
            Statement::While { body, .. } => {
                collect_assigned_variables(body, out);
            }
            Statement::Match { arms, .. } => {
                for arm in arms {
                    collect_assigned_variables(&arm.body, out);
                }
            }
            Statement::StructDef { .. }
            | Statement::Return { .. }
            | Statement::Expression { .. } => {}
        }
    }
}

fn apply_binop(op: Op, lhs: SymValue, rhs: SymValue) -> anyhow::Result<SymValue> {
    match op {
        Op::And | Op::Or => {
            let left = expect_bool_expr(lhs, "boolean operation lhs")?;
            let right = expect_bool_expr(rhs, "boolean operation rhs")?;
            let expr = match op {
                Op::And => and_all(vec![left, right]),
                Op::Or => or_all(vec![left, right]),
                _ => unreachable!(),
            };
            Ok(SymValue::Scalar {
                ty: "Bool".to_string(),
                expr,
            })
        }
        Op::Add | Op::Sub | Op::Mul | Op::Div => {
            let (left_ty, left) = expect_int_expr(lhs, "arithmetic lhs")?;
            let (_right_ty, right) = expect_int_expr(rhs, "arithmetic rhs")?;
            let expr = match op {
                Op::Add => SymExpr::Add(Box::new(left), Box::new(right)),
                Op::Sub => SymExpr::Sub(Box::new(left), Box::new(right)),
                Op::Mul => SymExpr::Mul(Box::new(left), Box::new(right)),
                Op::Div => SymExpr::Div(Box::new(left), Box::new(right)),
                _ => unreachable!(),
            };
            Ok(SymValue::Scalar { ty: left_ty, expr })
        }
        Op::Eq | Op::Neq => {
            let (left_ty, left_expr) = expect_scalar_expr(lhs, "comparison lhs")?;
            let (right_ty, right_expr) = expect_scalar_expr(rhs, "comparison rhs")?;
            if left_ty != right_ty {
                return Err(anyhow::anyhow!(
                    "unsupported comparison between {} and {}",
                    left_ty,
                    right_ty
                ));
            }
            let expr = match op {
                Op::Eq => SymExpr::Eq(Box::new(left_expr), Box::new(right_expr)),
                Op::Neq => SymExpr::Ne(Box::new(left_expr), Box::new(right_expr)),
                _ => unreachable!(),
            };
            Ok(SymValue::Scalar {
                ty: "Bool".to_string(),
                expr,
            })
        }
        Op::Lt | Op::Gt | Op::Le | Op::Ge => {
            let (_left_ty, left) = expect_int_expr(lhs, "ordering lhs")?;
            let (_right_ty, right) = expect_int_expr(rhs, "ordering rhs")?;
            let expr = match op {
                Op::Lt => SymExpr::Lt(Box::new(left), Box::new(right)),
                Op::Gt => SymExpr::Gt(Box::new(left), Box::new(right)),
                Op::Le => SymExpr::Le(Box::new(left), Box::new(right)),
                Op::Ge => SymExpr::Ge(Box::new(left), Box::new(right)),
                _ => unreachable!(),
            };
            Ok(SymValue::Scalar {
                ty: "Bool".to_string(),
                expr,
            })
        }
    }
}

fn expect_scalar_expr(value: SymValue, context: &str) -> anyhow::Result<(String, SymExpr)> {
    match value {
        SymValue::Scalar { ty, expr } => Ok((ty, expr)),
        SymValue::Struct { ty, .. } => Err(anyhow::anyhow!(
            "unsupported {}: struct type {} is not scalar",
            context,
            ty
        )),
    }
}

fn expect_bool_expr(value: SymValue, context: &str) -> anyhow::Result<SymExpr> {
    let (ty, expr) = expect_scalar_expr(value, context)?;
    if ty != "Bool" || expr.sort() != Sort::Bool {
        return Err(anyhow::anyhow!("{} must be Bool, got {}", context, ty));
    }
    Ok(expr)
}

fn expect_int_expr(value: SymValue, context: &str) -> anyhow::Result<(String, SymExpr)> {
    let (ty, expr) = expect_scalar_expr(value, context)?;
    if expr.sort() != Sort::Int {
        return Err(anyhow::anyhow!(
            "{} must be integer-like, got {}",
            context,
            ty
        ));
    }
    Ok((ty, expr))
}

fn merge_return_states(returns: Vec<ReturnState>) -> anyhow::Result<SymValue> {
    let mut iter = returns.into_iter().rev();
    let last = iter
        .next()
        .ok_or_else(|| anyhow::anyhow!("cannot merge empty return states"))?;
    let mut acc = last.value;

    for branch in iter {
        acc = ite_value(branch.path, branch.value, acc)?;
    }

    Ok(acc)
}

fn ite_value(
    cond: SymExpr,
    then_value: SymValue,
    else_value: SymValue,
) -> anyhow::Result<SymValue> {
    match (then_value, else_value) {
        (
            SymValue::Scalar {
                ty: then_ty,
                expr: then_expr,
            },
            SymValue::Scalar {
                ty: else_ty,
                expr: else_expr,
            },
        ) => {
            if then_ty != else_ty {
                return Err(anyhow::anyhow!(
                    "mismatched scalar types in return merge: {} vs {}",
                    then_ty,
                    else_ty
                ));
            }
            if then_expr.sort() != else_expr.sort() {
                return Err(anyhow::anyhow!(
                    "mismatched scalar sorts in return merge for {}",
                    then_ty
                ));
            }
            let sort = then_expr.sort();
            Ok(SymValue::Scalar {
                ty: then_ty,
                expr: SymExpr::Ite {
                    cond: Box::new(cond),
                    then_expr: Box::new(then_expr),
                    else_expr: Box::new(else_expr),
                    sort,
                },
            })
        }
        (
            SymValue::Struct {
                ty: then_ty,
                fields: then_fields,
            },
            SymValue::Struct {
                ty: else_ty,
                fields: else_fields,
            },
        ) => {
            if then_ty != else_ty {
                return Err(anyhow::anyhow!(
                    "mismatched struct types in return merge: {} vs {}",
                    then_ty,
                    else_ty
                ));
            }

            let mut field_names = then_fields.keys().cloned().collect::<Vec<_>>();
            field_names.sort();
            if field_names.len() != else_fields.len() {
                return Err(anyhow::anyhow!(
                    "mismatched struct shape in return merge for {}",
                    then_ty
                ));
            }

            let mut fields = HashMap::new();
            for field_name in field_names {
                let then_field = then_fields.get(&field_name).cloned().ok_or_else(|| {
                    anyhow::anyhow!(
                        "missing field {} in then branch for {}",
                        field_name,
                        then_ty
                    )
                })?;
                let else_field = else_fields.get(&field_name).cloned().ok_or_else(|| {
                    anyhow::anyhow!(
                        "missing field {} in else branch for {}",
                        field_name,
                        then_ty
                    )
                })?;
                let merged = ite_value(cond.clone(), then_field, else_field)?;
                fields.insert(field_name, merged);
            }

            Ok(SymValue::Struct {
                ty: then_ty,
                fields,
            })
        }
        (then_value, else_value) => Err(anyhow::anyhow!(
            "mismatched return kinds in merge: {} vs {}",
            then_value.type_name(),
            else_value.type_name()
        )),
    }
}

fn not_expr(expr: SymExpr) -> SymExpr {
    match expr {
        SymExpr::BoolConst(value) => SymExpr::BoolConst(!value),
        SymExpr::Not(inner) => *inner,
        other => SymExpr::Not(Box::new(other)),
    }
}

fn and_all(exprs: Vec<SymExpr>) -> SymExpr {
    let mut flat = Vec::new();
    for expr in exprs {
        match expr {
            SymExpr::BoolConst(true) => {}
            SymExpr::BoolConst(false) => return SymExpr::BoolConst(false),
            SymExpr::And(items) => flat.extend(items),
            other => flat.push(other),
        }
    }

    if flat.is_empty() {
        SymExpr::BoolConst(true)
    } else if flat.len() == 1 {
        flat.pop().unwrap()
    } else {
        SymExpr::And(flat)
    }
}

fn or_all(exprs: Vec<SymExpr>) -> SymExpr {
    let mut flat = Vec::new();
    for expr in exprs {
        match expr {
            SymExpr::BoolConst(false) => {}
            SymExpr::BoolConst(true) => return SymExpr::BoolConst(true),
            SymExpr::Or(items) => flat.extend(items),
            other => flat.push(other),
        }
    }

    if flat.is_empty() {
        SymExpr::BoolConst(false)
    } else if flat.len() == 1 {
        flat.pop().unwrap()
    } else {
        SymExpr::Or(flat)
    }
}

fn is_false(expr: &SymExpr) -> bool {
    matches!(expr, SymExpr::BoolConst(false))
}

fn stable_string_const(value: &str) -> i64 {
    let mut hash: i64 = 1469598103934665603_i64;
    for byte in value.as_bytes() {
        hash ^= *byte as i64;
        hash = hash.wrapping_mul(1099511628211_i64);
    }
    hash
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CheckerTy {
    Word,
    Long,
}

impl CheckerTy {
    fn qbe_type(self) -> qbe::Type {
        match self {
            CheckerTy::Word => qbe::Type::Word,
            CheckerTy::Long => qbe::Type::Long,
        }
    }

    fn from_sort(sort: &Sort) -> Self {
        match sort {
            Sort::Bool => CheckerTy::Word,
            Sort::Int => CheckerTy::Long,
        }
    }
}

#[derive(Clone, Debug)]
struct CheckerValue {
    ty: CheckerTy,
    value: qbe::Value,
}

#[derive(Default)]
struct CheckerBuilder {
    statements: Vec<qbe::Statement>,
    temp_counter: usize,
    vars: HashMap<String, CheckerValue>,
}

impl CheckerBuilder {
    fn next_temp(&mut self, prefix: &str) -> String {
        let name = format!("t{}_{}", sanitize_ident(prefix), self.temp_counter);
        self.temp_counter += 1;
        name
    }

    fn emit_assign(&mut self, ty: CheckerTy, dest: &str, instr: qbe::Instr) {
        self.statements.push(qbe::Statement::Assign(
            qbe::Value::Temporary(dest.to_string()),
            ty.qbe_type(),
            instr,
        ));
    }

    fn emit_instr(&mut self, instr: qbe::Instr) {
        self.statements.push(qbe::Statement::Volatile(instr));
    }

    fn value_const_word(v: u64) -> CheckerValue {
        CheckerValue {
            ty: CheckerTy::Word,
            value: qbe::Value::Const(v),
        }
    }

    fn value_const_long(v: u64) -> CheckerValue {
        CheckerValue {
            ty: CheckerTy::Long,
            value: qbe::Value::Const(v),
        }
    }

    fn normalize_bool(&mut self, value: CheckerValue) -> CheckerValue {
        let dest = self.next_temp("bool");
        let instr = match value.ty {
            CheckerTy::Word => qbe::Instr::Cmp(
                qbe::Type::Word,
                qbe::Cmp::Ne,
                value.value,
                qbe::Value::Const(0),
            ),
            CheckerTy::Long => qbe::Instr::Cmp(
                qbe::Type::Long,
                qbe::Cmp::Ne,
                value.value,
                qbe::Value::Const(0),
            ),
        };
        self.emit_assign(CheckerTy::Word, &dest, instr);
        CheckerValue {
            ty: CheckerTy::Word,
            value: qbe::Value::Temporary(dest),
        }
    }

    fn expect_long(&mut self, value: CheckerValue, context: &str) -> anyhow::Result<CheckerValue> {
        match value.ty {
            CheckerTy::Long => Ok(value),
            CheckerTy::Word => {
                let dest = self.next_temp(context);
                self.emit_assign(CheckerTy::Long, &dest, qbe::Instr::Extsw(value.value));
                Ok(CheckerValue {
                    ty: CheckerTy::Long,
                    value: qbe::Value::Temporary(dest),
                })
            }
        }
    }

    fn coerce_to(
        &mut self,
        value: CheckerValue,
        target: CheckerTy,
        context: &str,
    ) -> anyhow::Result<CheckerValue> {
        if value.ty == target {
            return Ok(value);
        }

        let dest = self.next_temp(context);
        match (value.ty, target) {
            (CheckerTy::Word, CheckerTy::Long) => {
                self.emit_assign(CheckerTy::Long, &dest, qbe::Instr::Extsw(value.value));
            }
            (CheckerTy::Long, CheckerTy::Word) => {
                self.emit_assign(CheckerTy::Word, &dest, qbe::Instr::Copy(value.value));
            }
            (CheckerTy::Word, CheckerTy::Word) | (CheckerTy::Long, CheckerTy::Long) => {}
        }
        Ok(CheckerValue {
            ty: target,
            value: qbe::Value::Temporary(dest),
        })
    }

    fn lower_expr(&mut self, expr: &SymExpr) -> anyhow::Result<CheckerValue> {
        match expr {
            SymExpr::BoolConst(true) => Ok(Self::value_const_word(1)),
            SymExpr::BoolConst(false) => Ok(Self::value_const_word(0)),
            SymExpr::IntConst(v) => Ok(Self::value_const_long(*v as u64)),
            SymExpr::Var { name, sort } => self.vars.get(name).cloned().ok_or_else(|| {
                anyhow::anyhow!("missing checker variable binding for {} ({:?})", name, sort)
            }),
            SymExpr::Not(inner) => {
                let inner = self.lower_expr(inner)?;
                let inner = self.normalize_bool(inner);
                let dest = self.next_temp("not");
                self.emit_assign(
                    CheckerTy::Word,
                    &dest,
                    qbe::Instr::Cmp(
                        qbe::Type::Word,
                        qbe::Cmp::Eq,
                        inner.value,
                        qbe::Value::Const(0),
                    ),
                );
                Ok(CheckerValue {
                    ty: CheckerTy::Word,
                    value: qbe::Value::Temporary(dest),
                })
            }
            SymExpr::And(items) => {
                if items.is_empty() {
                    return Ok(Self::value_const_word(1));
                }
                let mut iter = items.iter();
                let first = self.lower_expr(iter.next().expect("non-empty and"))?;
                let mut acc = self.normalize_bool(first);
                for item in iter {
                    let rhs = self.lower_expr(item)?;
                    let rhs = self.normalize_bool(rhs);
                    let dest = self.next_temp("and");
                    self.emit_assign(
                        CheckerTy::Word,
                        &dest,
                        qbe::Instr::And(acc.value, rhs.value),
                    );
                    acc = CheckerValue {
                        ty: CheckerTy::Word,
                        value: qbe::Value::Temporary(dest),
                    };
                }
                Ok(acc)
            }
            SymExpr::Or(items) => {
                if items.is_empty() {
                    return Ok(Self::value_const_word(0));
                }
                let mut iter = items.iter();
                let first = self.lower_expr(iter.next().expect("non-empty or"))?;
                let mut acc = self.normalize_bool(first);
                for item in iter {
                    let rhs = self.lower_expr(item)?;
                    let rhs = self.normalize_bool(rhs);
                    let dest = self.next_temp("or");
                    self.emit_assign(CheckerTy::Word, &dest, qbe::Instr::Or(acc.value, rhs.value));
                    acc = CheckerValue {
                        ty: CheckerTy::Word,
                        value: qbe::Value::Temporary(dest),
                    };
                }
                Ok(acc)
            }
            SymExpr::Add(lhs, rhs)
            | SymExpr::Sub(lhs, rhs)
            | SymExpr::Mul(lhs, rhs)
            | SymExpr::Div(lhs, rhs) => {
                let lhs_raw = self.lower_expr(lhs)?;
                let lhs = self.expect_long(lhs_raw, "lhs")?;
                let rhs_raw = self.lower_expr(rhs)?;
                let rhs = self.expect_long(rhs_raw, "rhs")?;
                let op = match expr {
                    SymExpr::Add(_, _) => qbe::Instr::Add(lhs.value, rhs.value),
                    SymExpr::Sub(_, _) => qbe::Instr::Sub(lhs.value, rhs.value),
                    SymExpr::Mul(_, _) => qbe::Instr::Mul(lhs.value, rhs.value),
                    SymExpr::Div(_, _) => qbe::Instr::Div(lhs.value, rhs.value),
                    _ => unreachable!(),
                };
                let dest = self.next_temp("arith");
                self.emit_assign(CheckerTy::Long, &dest, op);
                Ok(CheckerValue {
                    ty: CheckerTy::Long,
                    value: qbe::Value::Temporary(dest),
                })
            }
            SymExpr::Eq(lhs, rhs) | SymExpr::Ne(lhs, rhs) => {
                let eq = matches!(expr, SymExpr::Eq(_, _));
                let lhs_sort = lhs.sort();
                let rhs_sort = rhs.sort();
                if lhs_sort != rhs_sort {
                    return Err(anyhow::anyhow!(
                        "mismatched equality operand sorts: {:?} vs {:?}",
                        lhs_sort,
                        rhs_sort
                    ));
                }

                let (cmp_ty, lhs, rhs) = match lhs_sort {
                    Sort::Bool => {
                        let lhs_raw = self.lower_expr(lhs)?;
                        let lhs = self.normalize_bool(lhs_raw);
                        let rhs_raw = self.lower_expr(rhs)?;
                        let rhs = self.normalize_bool(rhs_raw);
                        (qbe::Type::Word, lhs, rhs)
                    }
                    Sort::Int => {
                        let lhs_raw = self.lower_expr(lhs)?;
                        let lhs = self.expect_long(lhs_raw, "eq_lhs")?;
                        let rhs_raw = self.lower_expr(rhs)?;
                        let rhs = self.expect_long(rhs_raw, "eq_rhs")?;
                        (qbe::Type::Long, lhs, rhs)
                    }
                };
                let dest = self.next_temp("cmp");
                self.emit_assign(
                    CheckerTy::Word,
                    &dest,
                    qbe::Instr::Cmp(
                        cmp_ty,
                        if eq { qbe::Cmp::Eq } else { qbe::Cmp::Ne },
                        lhs.value,
                        rhs.value,
                    ),
                );
                Ok(CheckerValue {
                    ty: CheckerTy::Word,
                    value: qbe::Value::Temporary(dest),
                })
            }
            SymExpr::Lt(lhs, rhs)
            | SymExpr::Gt(lhs, rhs)
            | SymExpr::Le(lhs, rhs)
            | SymExpr::Ge(lhs, rhs) => {
                let lhs_raw = self.lower_expr(lhs)?;
                let lhs = self.expect_long(lhs_raw, "ord_lhs")?;
                let rhs_raw = self.lower_expr(rhs)?;
                let rhs = self.expect_long(rhs_raw, "ord_rhs")?;
                let cmp = match expr {
                    SymExpr::Lt(_, _) => qbe::Cmp::Slt,
                    SymExpr::Gt(_, _) => qbe::Cmp::Sgt,
                    SymExpr::Le(_, _) => qbe::Cmp::Sle,
                    SymExpr::Ge(_, _) => qbe::Cmp::Sge,
                    _ => unreachable!(),
                };
                let dest = self.next_temp("ord");
                self.emit_assign(
                    CheckerTy::Word,
                    &dest,
                    qbe::Instr::Cmp(qbe::Type::Long, cmp, lhs.value, rhs.value),
                );
                Ok(CheckerValue {
                    ty: CheckerTy::Word,
                    value: qbe::Value::Temporary(dest),
                })
            }
            SymExpr::Ite {
                cond,
                then_expr,
                else_expr,
                sort,
            } => {
                let cond_raw = self.lower_expr(cond)?;
                let cond = self.normalize_bool(cond_raw);
                let out_ty = CheckerTy::from_sort(sort);
                let then_value = self.lower_expr(then_expr)?;
                let else_value = self.lower_expr(else_expr)?;
                let then_value = self.coerce_to(then_value, out_ty, "ite_then")?;
                let else_value = self.coerce_to(else_value, out_ty, "ite_else")?;
                let cond_typed = self.coerce_to(cond, out_ty, "ite_cond")?;

                let mask = self.next_temp("ite_mask");
                self.emit_assign(
                    out_ty,
                    &mask,
                    qbe::Instr::Sub(qbe::Value::Const(0), cond_typed.value),
                );
                let mask_value = qbe::Value::Temporary(mask);

                let all_ones = match out_ty {
                    CheckerTy::Word => u32::MAX as u64,
                    CheckerTy::Long => u64::MAX,
                };
                let inv_mask = self.next_temp("ite_inv_mask");
                self.emit_assign(
                    out_ty,
                    &inv_mask,
                    qbe::Instr::Sub(qbe::Value::Const(all_ones), mask_value.clone()),
                );
                let inv_mask_value = qbe::Value::Temporary(inv_mask);

                let then_masked = self.next_temp("ite_then_masked");
                self.emit_assign(
                    out_ty,
                    &then_masked,
                    qbe::Instr::And(then_value.value, mask_value),
                );
                let then_masked_value = qbe::Value::Temporary(then_masked);

                let else_masked = self.next_temp("ite_else_masked");
                self.emit_assign(
                    out_ty,
                    &else_masked,
                    qbe::Instr::And(else_value.value, inv_mask_value),
                );
                let else_masked_value = qbe::Value::Temporary(else_masked);

                let out_name = self.next_temp("ite_out");
                self.emit_assign(
                    out_ty,
                    &out_name,
                    qbe::Instr::Or(then_masked_value, else_masked_value),
                );
                Ok(CheckerValue {
                    ty: out_ty,
                    value: qbe::Value::Temporary(out_name),
                })
            }
        }
    }
}

fn render_obligation_checker_function(formula: &SymExpr) -> anyhow::Result<qbe::Function> {
    let mut vars = BTreeMap::new();
    collect_vars(formula, &mut vars);

    let mut builder = CheckerBuilder::default();
    let mut arguments = Vec::new();

    for (idx, (name, sort)) in vars.iter().enumerate() {
        let arg_name = format!("a{}_{}", idx, sanitize_ident(name));
        let arg_ty = match sort {
            Sort::Bool => CheckerTy::Word,
            Sort::Int => CheckerTy::Word,
        };
        arguments.push((arg_ty.qbe_type(), qbe::Value::Temporary(arg_name.clone())));

        let base = CheckerValue {
            ty: arg_ty,
            value: qbe::Value::Temporary(arg_name),
        };
        let value = match sort {
            Sort::Bool => builder.normalize_bool(base),
            Sort::Int => builder.expect_long(base, "arg_int")?,
        };
        builder.vars.insert(name.clone(), value);
    }

    let violation_raw = builder.lower_expr(formula)?;
    let violation = builder.normalize_bool(violation_raw);
    builder.emit_instr(qbe::Instr::Ret(Some(violation.value)));

    let mut function = qbe::Function::new(
        qbe::Linkage::private(),
        "main",
        arguments,
        Some(qbe::Type::Word),
    );
    let block = function.add_block("start");
    block.items.extend(
        builder
            .statements
            .into_iter()
            .map(qbe::BlockItem::Statement),
    );

    Ok(function)
}

fn solve_obligations(
    sites: &[ObligationSite],
    formulas: &HashMap<String, SymExpr>,
    target_dir: &Path,
) -> anyhow::Result<()> {
    let verification_dir = target_dir.join("struct_invariants");
    std::fs::create_dir_all(&verification_dir).with_context(|| {
        format!(
            "failed to create struct invariant verification directory {}",
            verification_dir.display()
        )
    })?;

    let mut failures = Vec::new();

    for site in sites {
        let formula = formulas
            .get(&site.id)
            .cloned()
            .unwrap_or(SymExpr::BoolConst(false));

        let checker_function = render_obligation_checker_function(&formula)?;
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
                assume_main_argc_non_negative: false,
            },
        )
        .with_context(|| format!("failed to encode checker QBE for {}", site.id))?;

        let smt_path = verification_dir.join(&smt_filename);
        std::fs::write(&smt_path, &smt)
            .with_context(|| format!("failed to write SMT obligation {}", smt_path.display()))?;

        match run_z3(&smt) {
            Ok(SolverResult::Unsat) => {}
            Ok(SolverResult::Sat) => failures.push(format!(
                "{} (caller={}, callee={}, struct={}, qbe_artifact={}, smt_artifact={})",
                site.id, site.caller, site.callee, site.struct_name, qbe_filename, smt_filename
            )),
            Ok(SolverResult::Unknown) => {
                return Err(anyhow::anyhow!("solver returned unknown for {}", site.id))
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SolverResult {
    Sat,
    Unsat,
    Unknown,
}

fn run_z3(smt: &str) -> anyhow::Result<SolverResult> {
    let mut command = Command::new("z3");
    command
        .arg(format!("-T:{}", Z3_TIMEOUT_SECONDS))
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    let mut child = command.spawn().map_err(|err| {
        if err.kind() == std::io::ErrorKind::NotFound {
            anyhow::anyhow!(
                "z3 executable not found. Install z3 to verify struct invariants during build"
            )
        } else {
            anyhow::anyhow!("failed to spawn z3: {}", err)
        }
    })?;

    let write_result = {
        let stdin = child.stdin.as_mut().context("failed to open z3 stdin")?;
        stdin.write_all(smt.as_bytes())
    };
    if let Err(write_err) = write_result {
        let output = child
            .wait_with_output()
            .context("failed to wait for z3 process after write failure")?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(anyhow::anyhow!(
            "failed to send SMT query to z3: {} (status={}, stdout='{}', stderr='{}')",
            write_err,
            output.status,
            stdout.trim(),
            stderr.trim()
        ));
    }

    let output = child
        .wait_with_output()
        .context("failed to wait for z3 process")?;

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    let first = stdout
        .lines()
        .map(str::trim)
        .find(|line| !line.is_empty())
        .unwrap_or("");

    match first {
        "sat" => Ok(SolverResult::Sat),
        "unsat" => Ok(SolverResult::Unsat),
        "unknown" | "timeout" => Ok(SolverResult::Unknown),
        _ => Err(anyhow::anyhow!(
            "unexpected z3 output (status={}): stdout='{}' stderr='{}'",
            output.status,
            stdout.trim(),
            stderr.trim()
        )),
    }
}

#[cfg(test)]
fn render_obligation_smt(formula: &SymExpr) -> String {
    let mut vars = BTreeMap::new();
    collect_vars(formula, &mut vars);

    let mut smt = String::new();
    smt.push_str("(set-logic QF_UFLIA)\n");
    for (name, sort) in vars {
        let sort_str = match sort {
            Sort::Bool => "Bool",
            Sort::Int => "Int",
        };
        smt.push_str(&format!("(declare-const {} {})\n", name, sort_str));
    }
    smt.push_str(&format!("(assert {})\n", expr_to_smt(formula)));
    smt.push_str("(check-sat)\n");
    smt.push_str("(exit)\n");
    smt
}

fn collect_vars(expr: &SymExpr, vars: &mut BTreeMap<String, Sort>) {
    match expr {
        SymExpr::Var { name, sort } => {
            vars.insert(name.clone(), sort.clone());
        }
        SymExpr::Not(inner) => collect_vars(inner, vars),
        SymExpr::And(items) | SymExpr::Or(items) => {
            for item in items {
                collect_vars(item, vars);
            }
        }
        SymExpr::Add(lhs, rhs)
        | SymExpr::Sub(lhs, rhs)
        | SymExpr::Mul(lhs, rhs)
        | SymExpr::Div(lhs, rhs)
        | SymExpr::Eq(lhs, rhs)
        | SymExpr::Ne(lhs, rhs)
        | SymExpr::Lt(lhs, rhs)
        | SymExpr::Gt(lhs, rhs)
        | SymExpr::Le(lhs, rhs)
        | SymExpr::Ge(lhs, rhs) => {
            collect_vars(lhs, vars);
            collect_vars(rhs, vars);
        }
        SymExpr::Ite {
            cond,
            then_expr,
            else_expr,
            ..
        } => {
            collect_vars(cond, vars);
            collect_vars(then_expr, vars);
            collect_vars(else_expr, vars);
        }
        SymExpr::BoolConst(_) | SymExpr::IntConst(_) => {}
    }
}

#[cfg(test)]
fn expr_to_smt(expr: &SymExpr) -> String {
    match expr {
        SymExpr::BoolConst(true) => "true".to_string(),
        SymExpr::BoolConst(false) => "false".to_string(),
        SymExpr::IntConst(value) => value.to_string(),
        SymExpr::Var { name, .. } => name.clone(),
        SymExpr::Not(inner) => format!("(not {})", expr_to_smt(inner)),
        SymExpr::And(items) => {
            if items.is_empty() {
                "true".to_string()
            } else {
                format!(
                    "(and {})",
                    items.iter().map(expr_to_smt).collect::<Vec<_>>().join(" ")
                )
            }
        }
        SymExpr::Or(items) => {
            if items.is_empty() {
                "false".to_string()
            } else {
                format!(
                    "(or {})",
                    items.iter().map(expr_to_smt).collect::<Vec<_>>().join(" ")
                )
            }
        }
        SymExpr::Add(lhs, rhs) => format!("(+ {} {})", expr_to_smt(lhs), expr_to_smt(rhs)),
        SymExpr::Sub(lhs, rhs) => format!("(- {} {})", expr_to_smt(lhs), expr_to_smt(rhs)),
        SymExpr::Mul(lhs, rhs) => format!("(* {} {})", expr_to_smt(lhs), expr_to_smt(rhs)),
        SymExpr::Div(lhs, rhs) => format!("(div {} {})", expr_to_smt(lhs), expr_to_smt(rhs)),
        SymExpr::Eq(lhs, rhs) => format!("(= {} {})", expr_to_smt(lhs), expr_to_smt(rhs)),
        SymExpr::Ne(lhs, rhs) => format!("(not (= {} {}))", expr_to_smt(lhs), expr_to_smt(rhs)),
        SymExpr::Lt(lhs, rhs) => format!("(< {} {})", expr_to_smt(lhs), expr_to_smt(rhs)),
        SymExpr::Gt(lhs, rhs) => format!("(> {} {})", expr_to_smt(lhs), expr_to_smt(rhs)),
        SymExpr::Le(lhs, rhs) => format!("(<= {} {})", expr_to_smt(lhs), expr_to_smt(rhs)),
        SymExpr::Ge(lhs, rhs) => format!("(>= {} {})", expr_to_smt(lhs), expr_to_smt(rhs)),
        SymExpr::Ite {
            cond,
            then_expr,
            else_expr,
            ..
        } => format!(
            "(ite {} {} {})",
            expr_to_smt(cond),
            expr_to_smt(then_expr),
            expr_to_smt(else_expr)
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ir, parser, tokenizer};

    fn resolve_program(source: &str) -> ResolvedProgram {
        let tokens = tokenizer::tokenize(source.to_string()).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        ir::resolve(ast).expect("resolve source")
    }

    #[test]
    fn discovers_valid_struct_invariant() {
        let program = resolve_program(
            r#"
struct Foo {
	x: I32,
}

fun __struct__Foo__invariant(v: Foo) -> Bool {
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
        assert_eq!(
            invariants.get("Foo").map(String::as_str),
            Some("__struct__Foo__invariant")
        );
    }

    #[test]
    fn rejects_malformed_invariant_signature() {
        let program = resolve_program(
            r#"
struct Foo {
	x: I32,
}

fun __struct__Foo__invariant(v: Foo) -> I32 {
	return 1
}

fun main() -> I32 {
	return 0
}
"#,
        );

        let err = discover_invariants(&program).expect_err("invariant should be rejected");
        assert!(err.to_string().contains("must return Bool"));
    }

    #[test]
    fn supports_template_concrete_invariant_names() {
        let program = resolve_program(
            r#"
template Box[T] {
	struct Box {
		value: T,
	}
}

instantiate BoxI32 = Box[I32]

fun __struct__BoxI32__invariant(v: BoxI32) -> Bool {
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
        assert_eq!(
            invariants.get("BoxI32").map(String::as_str),
            Some("__struct__BoxI32__invariant")
        );
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

fun __struct__Foo__invariant(v: Foo) -> Bool {
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
    }

    #[test]
    fn supports_while_without_invariant_obligation_sites() {
        let program = resolve_program(
            r#"
struct Counter {
	value: I32,
}

fun __struct__Counter__invariant(v: Counter) -> Bool {
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

        let (sites, formulas) = build_obligations(&program).expect("while should be supported");
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].callee, "make_counter");
        assert!(formulas.contains_key(&sites[0].id));
    }

    #[test]
    fn rejects_while_with_invariant_obligation_sites_inside_loop() {
        let program = resolve_program(
            r#"
struct Counter {
	value: I32,
}

fun __struct__Counter__invariant(v: Counter) -> Bool {
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

        let err = build_obligations(&program).expect_err("loop call site should be rejected");
        assert!(err
            .to_string()
            .contains("while loops containing struct invariant obligation call sites"));
    }

    #[test]
    fn rejects_recursion_in_verified_paths() {
        let program = resolve_program(
            r#"
struct Foo {
	x: I32,
}

fun __struct__Foo__invariant(v: Foo) -> Bool {
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

        let err = build_obligations(&program).expect_err("recursion should be rejected");
        assert!(err
            .to_string()
            .contains("recursion cycles are unsupported by struct invariant verification"));
    }

    #[test]
    fn external_calls_introduce_havoc_symbols_in_smt() {
        let program = resolve_program(
            r#"
struct Foo {
	x: I32,
}

fun __struct__Foo__invariant(v: Foo) -> Bool {
	return v.x == 1
}

fun make_foo() -> Foo {
	x = print(1)
	return Foo struct { x: x, }
}

fun main() -> I32 {
	f = make_foo()
	return 0
}
"#,
        );

        let (sites, formulas) = build_obligations(&program).expect("build obligations");
        assert_eq!(sites.len(), 1);

        let formula = formulas.get(&sites[0].id).expect("site formula");
        let smt = render_obligation_smt(formula);
        assert!(
            smt.contains("havoc"),
            "SMT should contain havoc symbol: {smt}"
        );
    }

    #[test]
    fn main_argc_gets_non_negative_constraint() {
        let program = resolve_program(
            r#"
struct Counter {
	value: I32,
}

fun __struct__Counter__invariant(v: Counter) -> Bool {
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

        let (sites, formulas) = build_obligations(&program).expect("build obligations");
        assert_eq!(sites.len(), 1);
        let formula = formulas.get(&sites[0].id).expect("site formula");
        let smt = render_obligation_smt(formula);
        assert!(
            smt.contains("(>= havoc_I32_0 0)"),
            "SMT should include argc non-negative constraint: {smt}"
        );
    }
}
