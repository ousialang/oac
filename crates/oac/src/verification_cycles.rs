use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use crate::ir::ResolvedProgram;
use crate::parser::{Expression, Statement};

#[derive(Clone, Debug, Eq, PartialEq)]
enum VerificationEdgeKind {
    Call,
    ArgInvariant { arg_index: usize },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct VerificationEdge {
    to: String,
    kind: VerificationEdgeKind,
}

pub fn reachable_user_functions(
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

pub fn reject_recursion_cycles_with_arg_invariants(
    program: &ResolvedProgram,
    root: &str,
    reachable: &HashSet<String>,
    arg_invariant_assumptions: &[qbe_smt::FunctionArgInvariantAssumption],
    verification_label: &str,
) -> anyhow::Result<()> {
    if !reachable.contains(root) {
        return Ok(());
    }

    let assumption_edges = build_assumption_edges(arg_invariant_assumptions);
    let adjacency = build_combined_graph(program, root, reachable, &assumption_edges)?;

    if adjacency.is_empty() {
        return Ok(());
    }

    let mut nodes = adjacency.keys().cloned().collect::<Vec<_>>();
    nodes.sort();
    let mut sccs = tarjan_scc(&adjacency, &nodes);
    for scc in &mut sccs {
        scc.sort();
    }
    sccs.sort_by(|lhs, rhs| {
        lhs.first()
            .cmp(&rhs.first())
            .then(lhs.len().cmp(&rhs.len()))
            .then(lhs.cmp(rhs))
    });

    for scc in sccs {
        let node_set = scc.iter().cloned().collect::<HashSet<_>>();
        let internal_edges = internal_edges_for_scc(&adjacency, &node_set);
        let internal_arg_edges = internal_edges
            .iter()
            .filter(|(_, edge)| matches!(edge.kind, VerificationEdgeKind::ArgInvariant { .. }))
            .cloned()
            .collect::<Vec<_>>();
        if internal_arg_edges.is_empty() {
            continue;
        }

        let (arg_source, arg_edge) = internal_arg_edges
            .first()
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("internal error: missing arg edge in offending SCC"))?;
        let path = find_path_within_scc(&adjacency, &node_set, &arg_edge.to, &arg_source)
            .ok_or_else(|| {
                anyhow::anyhow!(
                    "internal error: failed to reconstruct cycle witness for arg-invariant edge"
                )
            })?;

        let mut cycle_edges = path;
        cycle_edges.push((arg_source, arg_edge));

        let cycle = cycle_edges
            .iter()
            .map(render_cycle_edge)
            .collect::<Vec<_>>()
            .join(" ; ");

        let mut arg_edge_summaries = internal_arg_edges
            .iter()
            .map(|(from, edge)| match edge.kind {
                VerificationEdgeKind::ArgInvariant { arg_index } => {
                    format!("{from}[arg#{arg_index}] -> {}", edge.to)
                }
                VerificationEdgeKind::Call => unreachable!("filtered to arg edges"),
            })
            .collect::<Vec<_>>();
        arg_edge_summaries.sort();
        arg_edge_summaries.dedup();

        return Err(anyhow::anyhow!(
            "recursion cycles are unsupported by {}: {} (includes arg-invariant precondition edges: {})",
            verification_label,
            cycle,
            arg_edge_summaries.join(", ")
        ));
    }

    Ok(())
}

fn build_assumption_edges(
    arg_invariant_assumptions: &[qbe_smt::FunctionArgInvariantAssumption],
) -> HashMap<String, Vec<(String, usize)>> {
    let mut assumption_edges = HashMap::<String, Vec<(String, usize)>>::new();
    for assumption in arg_invariant_assumptions {
        assumption_edges
            .entry(assumption.function_name.clone())
            .or_default()
            .push((
                assumption.invariant_function_name.clone(),
                assumption.arg_index,
            ));
    }
    for edges in assumption_edges.values_mut() {
        edges.sort_by(|lhs, rhs| lhs.0.cmp(&rhs.0).then(lhs.1.cmp(&rhs.1)));
        edges.dedup();
    }
    assumption_edges
}

fn build_combined_graph(
    program: &ResolvedProgram,
    root: &str,
    reachable: &HashSet<String>,
    assumption_edges: &HashMap<String, Vec<(String, usize)>>,
) -> anyhow::Result<HashMap<String, Vec<VerificationEdge>>> {
    let mut visited = HashSet::<String>::new();
    let mut queue = VecDeque::<String>::from([root.to_string()]);
    let mut adjacency = HashMap::<String, Vec<VerificationEdge>>::new();

    while let Some(function_name) = queue.pop_front() {
        if !reachable.contains(&function_name) && function_name == root {
            continue;
        }
        if !visited.insert(function_name.clone()) {
            continue;
        }

        let function = program
            .function_definitions
            .get(&function_name)
            .ok_or_else(|| anyhow::anyhow!("missing function definition for {}", function_name))?;

        let mut edges = Vec::<VerificationEdge>::new();

        let mut call_callees = BTreeSet::new();
        for statement in &function.body {
            collect_called_user_functions_in_statement(statement, program, &mut call_callees);
        }
        for callee in call_callees {
            if !program.function_definitions.contains_key(&callee) {
                continue;
            }
            edges.push(VerificationEdge {
                to: callee.clone(),
                kind: VerificationEdgeKind::Call,
            });
            if !visited.contains(&callee) {
                queue.push_back(callee);
            }
        }

        if let Some(assumptions) = assumption_edges.get(&function_name) {
            for (invariant_function, arg_index) in assumptions {
                if !program.function_definitions.contains_key(invariant_function) {
                    return Err(anyhow::anyhow!(
                        "missing function definition for invariant precondition target {}",
                        invariant_function
                    ));
                }
                edges.push(VerificationEdge {
                    to: invariant_function.clone(),
                    kind: VerificationEdgeKind::ArgInvariant {
                        arg_index: *arg_index,
                    },
                });
                if !visited.contains(invariant_function) {
                    queue.push_back(invariant_function.clone());
                }
            }
        }

        sort_and_dedup_edges(&mut edges);
        adjacency.insert(function_name, edges);
    }

    Ok(adjacency)
}

fn collect_called_user_functions_in_statement(
    statement: &Statement,
    program: &ResolvedProgram,
    out: &mut BTreeSet<String>,
) {
    match statement {
        Statement::StructDef { .. } => {}
        Statement::Assign { value, .. } => collect_called_user_functions_in_expr(value, program, out),
        Statement::Return { expr } => collect_called_user_functions_in_expr(expr, program, out),
        Statement::Expression { expr } => collect_called_user_functions_in_expr(expr, program, out),
        Statement::Prove { condition } => collect_called_user_functions_in_expr(condition, program, out),
        Statement::Assert { condition } => collect_called_user_functions_in_expr(condition, program, out),
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

fn sort_and_dedup_edges(edges: &mut Vec<VerificationEdge>) {
    edges.sort_by(|lhs, rhs| edge_sort_key(lhs).cmp(&edge_sort_key(rhs)));
    edges.dedup_by(|lhs, rhs| edge_sort_key(lhs) == edge_sort_key(rhs));
}

fn edge_sort_key(edge: &VerificationEdge) -> (String, u8, usize) {
    let (kind_order, arg_index) = match edge.kind {
        VerificationEdgeKind::Call => (0, 0),
        VerificationEdgeKind::ArgInvariant { arg_index } => (1, arg_index),
    };
    (edge.to.clone(), kind_order, arg_index)
}

fn internal_edges_for_scc(
    adjacency: &HashMap<String, Vec<VerificationEdge>>,
    node_set: &HashSet<String>,
) -> Vec<(String, VerificationEdge)> {
    let mut nodes = node_set.iter().cloned().collect::<Vec<_>>();
    nodes.sort();

    let mut edges = Vec::new();
    for from in nodes {
        let outgoing = adjacency.get(&from).map(Vec::as_slice).unwrap_or(&[]);
        for edge in outgoing {
            if node_set.contains(&edge.to) {
                edges.push((from.clone(), edge.clone()));
            }
        }
    }
    edges.sort_by(|lhs, rhs| {
        lhs.0
            .cmp(&rhs.0)
            .then(edge_sort_key(&lhs.1).cmp(&edge_sort_key(&rhs.1)))
    });
    edges
}

fn find_path_within_scc(
    adjacency: &HashMap<String, Vec<VerificationEdge>>,
    node_set: &HashSet<String>,
    start: &str,
    goal: &str,
) -> Option<Vec<(String, VerificationEdge)>> {
    if start == goal {
        return Some(Vec::new());
    }

    let mut queue = VecDeque::from([start.to_string()]);
    let mut visited = HashSet::<String>::from([start.to_string()]);
    let mut parent = HashMap::<String, (String, VerificationEdge)>::new();

    while let Some(node) = queue.pop_front() {
        if node == goal {
            break;
        }
        let outgoing = adjacency.get(&node).map(Vec::as_slice).unwrap_or(&[]);
        for edge in outgoing {
            if !node_set.contains(&edge.to) {
                continue;
            }
            if visited.insert(edge.to.clone()) {
                parent.insert(edge.to.clone(), (node.clone(), edge.clone()));
                queue.push_back(edge.to.clone());
            }
        }
    }

    if !visited.contains(goal) {
        return None;
    }

    let mut rev_path = Vec::<(String, VerificationEdge)>::new();
    let mut cursor = goal.to_string();
    while cursor != start {
        let (prev, edge) = parent.get(&cursor)?.clone();
        rev_path.push((prev.clone(), edge));
        cursor = prev;
    }
    rev_path.reverse();
    Some(rev_path)
}

fn render_cycle_edge((from, edge): &(String, VerificationEdge)) -> String {
    match edge.kind {
        VerificationEdgeKind::Call => format!("{from} -> {}", edge.to),
        VerificationEdgeKind::ArgInvariant { arg_index } => {
            format!("{from} -[arg#{arg_index} invariant]-> {}", edge.to)
        }
    }
}

fn tarjan_scc(adjacency: &HashMap<String, Vec<VerificationEdge>>, nodes: &[String]) -> Vec<Vec<String>> {
    struct TarjanState<'a> {
        adjacency: &'a HashMap<String, Vec<VerificationEdge>>,
        index: usize,
        index_of: HashMap<String, usize>,
        lowlink: HashMap<String, usize>,
        stack: Vec<String>,
        on_stack: HashSet<String>,
        sccs: Vec<Vec<String>>,
    }

    impl<'a> TarjanState<'a> {
        fn new(adjacency: &'a HashMap<String, Vec<VerificationEdge>>) -> Self {
            Self {
                adjacency,
                index: 0,
                index_of: HashMap::new(),
                lowlink: HashMap::new(),
                stack: Vec::new(),
                on_stack: HashSet::new(),
                sccs: Vec::new(),
            }
        }

        fn strong_connect(&mut self, node: &str) {
            self.index_of.insert(node.to_string(), self.index);
            self.lowlink.insert(node.to_string(), self.index);
            self.index += 1;
            self.stack.push(node.to_string());
            self.on_stack.insert(node.to_string());

            let outgoing = self
                .adjacency
                .get(node)
                .map(Vec::as_slice)
                .unwrap_or(&[]);
            for edge in outgoing {
                let target = edge.to.as_str();
                if !self.index_of.contains_key(target) {
                    self.strong_connect(target);
                    let node_low = *self.lowlink.get(node).unwrap_or(&usize::MAX);
                    let target_low = *self.lowlink.get(target).unwrap_or(&usize::MAX);
                    self.lowlink
                        .insert(node.to_string(), node_low.min(target_low));
                } else if self.on_stack.contains(target) {
                    let node_low = *self.lowlink.get(node).unwrap_or(&usize::MAX);
                    let target_idx = *self.index_of.get(target).unwrap_or(&usize::MAX);
                    self.lowlink
                        .insert(node.to_string(), node_low.min(target_idx));
                }
            }

            let node_low = *self.lowlink.get(node).unwrap_or(&usize::MAX);
            let node_index = *self.index_of.get(node).unwrap_or(&usize::MAX);
            if node_low == node_index {
                let mut scc = Vec::<String>::new();
                while let Some(popped) = self.stack.pop() {
                    self.on_stack.remove(&popped);
                    scc.push(popped.clone());
                    if popped == node {
                        break;
                    }
                }
                self.sccs.push(scc);
            }
        }
    }

    let mut state = TarjanState::new(adjacency);
    for node in nodes {
        if !state.index_of.contains_key(node) {
            state.strong_connect(node);
        }
    }
    state.sccs
}
