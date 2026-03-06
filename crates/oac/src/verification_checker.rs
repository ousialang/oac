use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use crate::invariant_metadata::{
    build_function_arg_invariant_assumptions,
    build_function_arg_invariant_assumptions_with_name_overrides,
    build_function_arg_range_assumptions, build_function_arg_range_assumptions_with_name_overrides,
    InvariantBinding,
};
use crate::ir::ResolvedProgram;
use crate::qbe_backend::ASSERT_FAILURE_EXIT_CODE;

pub(crate) fn checker_module_with_reachable_callees(
    program: &ResolvedProgram,
    invariant_by_struct: &HashMap<String, Vec<InvariantBinding>>,
    function_map: &HashMap<String, qbe::Function>,
    checker: &qbe::Function,
    checker_to_program_name: &HashMap<String, String>,
) -> anyhow::Result<(qbe::Module, qbe_smt::ModuleAssumptions)> {
    let mut additional_roots = BTreeSet::<String>::new();
    loop {
        let mut module = qbe::Module::default();
        module.functions.push(checker.clone());

        let mut visited = HashSet::<String>::new();
        let mut queue = VecDeque::<String>::new();
        for callee in direct_user_callees(checker, function_map) {
            queue.push_back(callee);
        }
        for root in &additional_roots {
            if root != &checker.name {
                queue.push_back(root.clone());
            }
        }

        while let Some(callee_name) = queue.pop_front() {
            if !visited.insert(callee_name.clone()) {
                continue;
            }
            let callee = function_map.get(&callee_name).ok_or_else(|| {
                anyhow::anyhow!("missing QBE function for callee {}", callee_name)
            })?;
            module.functions.push(callee.clone());
            for nested in direct_user_callees(callee, function_map) {
                if !visited.contains(&nested) {
                    queue.push_back(nested);
                }
            }
        }

        let assumptions = if checker_to_program_name.is_empty() {
            let arg_invariant_assumptions = build_function_arg_invariant_assumptions(
                program,
                &module.functions,
                invariant_by_struct,
            )?;
            let arg_range_assumptions =
                build_function_arg_range_assumptions(program, &module.functions)?;
            qbe_smt::ModuleAssumptions {
                arg_invariant_assumptions,
                arg_range_assumptions,
            }
        } else {
            let arg_invariant_assumptions =
                build_function_arg_invariant_assumptions_with_name_overrides(
                    program,
                    &module.functions,
                    invariant_by_struct,
                    checker_to_program_name,
                )?;
            let arg_range_assumptions = build_function_arg_range_assumptions_with_name_overrides(
                program,
                &module.functions,
                checker_to_program_name,
            )?;
            qbe_smt::ModuleAssumptions {
                arg_invariant_assumptions,
                arg_range_assumptions,
            }
        };
        let required_invariant_functions = assumptions
            .arg_invariant_assumptions
            .iter()
            .map(|assumption| assumption.invariant_function_name.clone())
            .collect::<BTreeSet<_>>();

        let mut next_roots = additional_roots.clone();
        next_roots.extend(required_invariant_functions);
        if next_roots == additional_roots {
            rewrite_checker_assert_failure_exits(&mut module);
            return Ok((module, assumptions));
        }
        additional_roots = next_roots;
    }
}

pub(crate) fn direct_user_callees(
    function: &qbe::Function,
    function_map: &HashMap<String, qbe::Function>,
) -> BTreeSet<String> {
    let mut callees = BTreeSet::new();
    for block_index in entry_reachable_block_indices(function) {
        let block = &function.blocks[block_index];
        for item in &block.items {
            let qbe::BlockItem::Statement(statement) = item else {
                continue;
            };
            let maybe_name = match statement {
                qbe::Statement::Assign(_, _, qbe::Instr::Call(name, _, _))
                | qbe::Statement::Volatile(qbe::Instr::Call(name, _, _)) => Some(name),
                _ => None,
            };
            if let Some(name) = maybe_name {
                if function_map.contains_key(name) {
                    callees.insert(name.clone());
                }
            }

            if let qbe::Statement::Volatile(instr) = statement {
                if matches!(
                    instr,
                    qbe::Instr::Ret(_)
                        | qbe::Instr::Jmp(_)
                        | qbe::Instr::Jnz(_, _, _)
                        | qbe::Instr::Hlt
                ) {
                    break;
                }
            }
        }
    }
    callees
}

fn entry_reachable_block_indices(function: &qbe::Function) -> BTreeSet<usize> {
    if function.blocks.is_empty() {
        return BTreeSet::new();
    }

    let mut label_to_index = HashMap::<String, usize>::new();
    for (idx, block) in function.blocks.iter().enumerate() {
        label_to_index.insert(block.label.clone(), idx);
    }

    let mut reachable = BTreeSet::<usize>::new();
    let mut queue = VecDeque::<usize>::new();
    queue.push_back(0);

    while let Some(index) = queue.pop_front() {
        if !reachable.insert(index) {
            continue;
        }

        let block = &function.blocks[index];
        match block_terminator(block) {
            Some(qbe::Instr::Jmp(label)) => {
                if let Some(next_index) = label_to_index.get(label) {
                    queue.push_back(*next_index);
                }
            }
            Some(qbe::Instr::Jnz(_, then_label, else_label)) => {
                if let Some(next_index) = label_to_index.get(then_label) {
                    queue.push_back(*next_index);
                }
                if let Some(next_index) = label_to_index.get(else_label) {
                    queue.push_back(*next_index);
                }
            }
            Some(qbe::Instr::Ret(_) | qbe::Instr::Hlt) => {}
            _ => {
                let fallthrough = index + 1;
                if fallthrough < function.blocks.len() {
                    queue.push_back(fallthrough);
                }
            }
        }
    }

    reachable
}

fn block_terminator(block: &qbe::Block) -> Option<&qbe::Instr> {
    for item in block.items.iter().rev() {
        if let qbe::BlockItem::Statement(qbe::Statement::Volatile(instr)) = item {
            return Some(instr);
        }
    }
    None
}

pub(crate) fn rewrite_returns_to_zero(function: &mut qbe::Function) {
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

pub(crate) fn prune_function_to_target(function: &mut qbe::Function, target_block_index: usize) {
    let keep = blocks_that_can_reach_target(function, target_block_index);
    let mut used_labels = collect_labels_in_function(function);
    let mut prune_label = None::<String>;

    for block_index in 0..function.blocks.len() {
        if !keep.contains(&block_index) || block_index == target_block_index {
            continue;
        }

        let successors = block_successors(function, block_index);
        let fallthrough = block_index + 1;
        let terminator_index = find_terminator_index(&function.blocks[block_index]);

        match terminator_index {
            Some(term_index) => {
                let block = &mut function.blocks[block_index];
                let qbe::BlockItem::Statement(qbe::Statement::Volatile(instr)) =
                    &mut block.items[term_index]
                else {
                    continue;
                };
                match instr {
                    qbe::Instr::Jmp(_label) => {
                        let keep_jump = successors
                            .first()
                            .copied()
                            .map(|successor| keep.contains(&successor))
                            .unwrap_or(false);
                        if !keep_jump {
                            *instr = qbe::Instr::Ret(Some(qbe::Value::Const(0)));
                        }
                    }
                    qbe::Instr::Jnz(_, then_label, else_label) => {
                        let then_kept = successors
                            .first()
                            .copied()
                            .map(|successor| keep.contains(&successor))
                            .unwrap_or(false);
                        let else_kept = successors
                            .get(1)
                            .copied()
                            .map(|successor| keep.contains(&successor))
                            .unwrap_or(false);
                        match (then_kept, else_kept) {
                            (true, true) => {}
                            (false, false) => {
                                *instr = qbe::Instr::Ret(Some(qbe::Value::Const(0)));
                            }
                            (true, false) => {
                                let label = prune_label.get_or_insert_with(|| {
                                    fresh_unique_label("checker_prune", &mut used_labels)
                                });
                                *else_label = label.clone();
                            }
                            (false, true) => {
                                let label = prune_label.get_or_insert_with(|| {
                                    fresh_unique_label("checker_prune", &mut used_labels)
                                });
                                *then_label = label.clone();
                            }
                        }
                    }
                    qbe::Instr::Ret(_) | qbe::Instr::Hlt => {}
                    _ => {}
                }
            }
            None => {
                let block_count = function.blocks.len();
                let block = &mut function.blocks[block_index];
                let falls_to_target = successors
                    .first()
                    .copied()
                    .map(|successor| keep.contains(&successor))
                    .unwrap_or(false);
                if fallthrough >= block_count || !falls_to_target {
                    block
                        .items
                        .push(qbe::BlockItem::Statement(qbe::Statement::Volatile(
                            qbe::Instr::Ret(Some(qbe::Value::Const(0))),
                        )));
                }
            }
        }
    }

    if let Some(label) = prune_label {
        function.blocks.push(qbe::Block {
            label,
            items: vec![qbe::BlockItem::Statement(qbe::Statement::Volatile(
                qbe::Instr::Ret(Some(qbe::Value::Const(0))),
            ))],
        });
    }
}

pub(crate) fn rewrite_checker_assert_failure_exits(module: &mut qbe::Module) {
    if let Some(function) = module.functions.first_mut() {
        rewrite_function_assert_failure_exits(function);
    }
}

fn rewrite_function_assert_failure_exits(function: &mut qbe::Function) {
    for block in &mut function.blocks {
        let mut rewritten = Vec::with_capacity(block.items.len());
        let mut index = 0usize;
        while index < block.items.len() {
            if index + 1 < block.items.len()
                && is_assert_failure_exit_call(&block.items[index])
                && matches!(
                    block.items[index + 1],
                    qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Hlt))
                )
            {
                rewritten.push(qbe::BlockItem::Statement(qbe::Statement::Volatile(
                    qbe::Instr::Ret(Some(qbe::Value::Const(0))),
                )));
                index += 2;
                continue;
            }
            rewritten.push(block.items[index].clone());
            index += 1;
        }
        block.items = rewritten;
    }
}

fn is_assert_failure_exit_call(item: &qbe::BlockItem) -> bool {
    matches!(
        item,
        qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Call(
            function_name,
            args,
            None,
        ))) if function_name == "exit"
            && args.len() == 1
            && matches!(args[0], (qbe::Type::Word, qbe::Value::Const(value)) if value == ASSERT_FAILURE_EXIT_CODE)
    )
}

fn blocks_that_can_reach_target(
    function: &qbe::Function,
    target_block_index: usize,
) -> HashSet<usize> {
    let mut predecessors = vec![Vec::<usize>::new(); function.blocks.len()];
    for block_index in 0..function.blocks.len() {
        for successor in block_successors(function, block_index) {
            predecessors[successor].push(block_index);
        }
    }

    let mut keep = HashSet::<usize>::new();
    let mut queue = vec![target_block_index];
    while let Some(block_index) = queue.pop() {
        if !keep.insert(block_index) {
            continue;
        }
        queue.extend(predecessors[block_index].iter().copied());
    }
    keep
}

fn block_successors(function: &qbe::Function, block_index: usize) -> Vec<usize> {
    let mut label_to_index = HashMap::<String, usize>::new();
    for (index, block) in function.blocks.iter().enumerate() {
        label_to_index.insert(block.label.clone(), index);
    }

    if let Some(term_index) = find_terminator_index(&function.blocks[block_index]) {
        let qbe::BlockItem::Statement(qbe::Statement::Volatile(instr)) =
            &function.blocks[block_index].items[term_index]
        else {
            return Vec::new();
        };
        match instr {
            qbe::Instr::Jmp(label) => label_to_index.get(label).copied().into_iter().collect(),
            qbe::Instr::Jnz(_, then_label, else_label) => {
                let mut out = Vec::new();
                if let Some(index) = label_to_index.get(then_label) {
                    out.push(*index);
                }
                if let Some(index) = label_to_index.get(else_label) {
                    out.push(*index);
                }
                out
            }
            qbe::Instr::Ret(_) | qbe::Instr::Hlt => Vec::new(),
            _ => Vec::new(),
        }
    } else if block_index + 1 < function.blocks.len() {
        vec![block_index + 1]
    } else {
        Vec::new()
    }
}

fn find_terminator_index(block: &qbe::Block) -> Option<usize> {
    block.items.iter().rposition(|item| {
        matches!(
            item,
            qbe::BlockItem::Statement(qbe::Statement::Volatile(
                qbe::Instr::Ret(_)
                    | qbe::Instr::Jmp(_)
                    | qbe::Instr::Jnz(_, _, _)
                    | qbe::Instr::Hlt
            ))
        )
    })
}

fn collect_labels_in_function(function: &qbe::Function) -> HashSet<String> {
    function
        .blocks
        .iter()
        .map(|block| block.label.clone())
        .collect()
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

pub(crate) fn should_assume_main_argc_non_negative(caller: &str, checker: &qbe::Function) -> bool {
    if caller != "main" {
        return false;
    }
    if checker.arguments.len() != 2 {
        return false;
    }
    matches!(checker.arguments[0].0, qbe::Type::Word)
        && matches!(checker.arguments[1].0, qbe::Type::Long)
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

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::{
        direct_user_callees, prune_function_to_target, rewrite_checker_assert_failure_exits,
    };

    fn function(name: &str, blocks: Vec<qbe::Block>) -> qbe::Function {
        qbe::Function {
            linkage: qbe::Linkage::private(),
            name: name.to_string(),
            arguments: vec![],
            return_ty: Some(qbe::Type::Word),
            blocks,
        }
    }

    #[test]
    fn direct_user_callees_ignores_unreachable_blocks() {
        let live = function(
            "live",
            vec![qbe::Block {
                label: "start".to_string(),
                items: vec![qbe::BlockItem::Statement(qbe::Statement::Volatile(
                    qbe::Instr::Ret(Some(qbe::Value::Const(0))),
                ))],
            }],
        );
        let dead = function(
            "dead",
            vec![qbe::Block {
                label: "start".to_string(),
                items: vec![qbe::BlockItem::Statement(qbe::Statement::Volatile(
                    qbe::Instr::Ret(Some(qbe::Value::Const(0))),
                ))],
            }],
        );

        let caller = function(
            "caller",
            vec![
                qbe::Block {
                    label: "start".to_string(),
                    items: vec![qbe::BlockItem::Statement(qbe::Statement::Volatile(
                        qbe::Instr::Jmp("live_block".to_string()),
                    ))],
                },
                qbe::Block {
                    label: "live_block".to_string(),
                    items: vec![
                        qbe::BlockItem::Statement(qbe::Statement::Assign(
                            qbe::Value::Temporary("tmp_live".to_string()),
                            qbe::Type::Word,
                            qbe::Instr::Call("live".to_string(), vec![], None),
                        )),
                        qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Ret(Some(
                            qbe::Value::Const(0),
                        )))),
                    ],
                },
                qbe::Block {
                    label: "dead_block".to_string(),
                    items: vec![
                        qbe::BlockItem::Statement(qbe::Statement::Assign(
                            qbe::Value::Temporary("tmp_dead".to_string()),
                            qbe::Type::Word,
                            qbe::Instr::Call("dead".to_string(), vec![], None),
                        )),
                        qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Ret(Some(
                            qbe::Value::Const(0),
                        )))),
                    ],
                },
            ],
        );

        let mut function_map = HashMap::new();
        function_map.insert("live".to_string(), live);
        function_map.insert("dead".to_string(), dead);

        let callees = direct_user_callees(&caller, &function_map);
        assert!(callees.contains("live"));
        assert!(!callees.contains("dead"));
    }

    #[test]
    fn prune_function_to_target_rewrites_off_target_edges() {
        let mut function = function(
            "main",
            vec![
                qbe::Block {
                    label: "entry".to_string(),
                    items: vec![qbe::BlockItem::Statement(qbe::Statement::Volatile(
                        qbe::Instr::Jnz(
                            qbe::Value::Temporary("cond".to_string()),
                            "target".to_string(),
                            "dead".to_string(),
                        ),
                    ))],
                },
                qbe::Block {
                    label: "target".to_string(),
                    items: vec![qbe::BlockItem::Statement(qbe::Statement::Volatile(
                        qbe::Instr::Ret(Some(qbe::Value::Const(1))),
                    ))],
                },
                qbe::Block {
                    label: "dead".to_string(),
                    items: vec![qbe::BlockItem::Statement(qbe::Statement::Volatile(
                        qbe::Instr::Ret(Some(qbe::Value::Const(2))),
                    ))],
                },
            ],
        );

        prune_function_to_target(&mut function, 1);

        let qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Jnz(
            _,
            then_label,
            else_label,
        ))) = &function.blocks[0].items[0]
        else {
            panic!("expected pruned entry branch");
        };
        assert_eq!(then_label, "target");
        assert!(else_label.starts_with("checker_prune"));
        let prune_block = function
            .blocks
            .iter()
            .find(|block| block.label == *else_label)
            .expect("prune block exists");
        assert!(matches!(
            prune_block.items.as_slice(),
            [qbe::BlockItem::Statement(qbe::Statement::Volatile(
                qbe::Instr::Ret(Some(qbe::Value::Const(0),))
            ))]
        ));
    }

    #[test]
    fn rewrite_checker_assert_failure_exits_only_rewrites_entry_exit_242_hlt_pairs() {
        let mut module = qbe::Module {
            functions: vec![
                function(
                    "main",
                    vec![qbe::Block {
                        label: "entry".to_string(),
                        items: vec![
                            qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Call(
                                "exit".to_string(),
                                vec![(qbe::Type::Word, qbe::Value::Const(242))],
                                None,
                            ))),
                            qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Hlt)),
                        ],
                    }],
                ),
                function(
                    "helper",
                    vec![qbe::Block {
                        label: "entry".to_string(),
                        items: vec![
                            qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Call(
                                "exit".to_string(),
                                vec![(qbe::Type::Word, qbe::Value::Const(242))],
                                None,
                            ))),
                            qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Hlt)),
                        ],
                    }],
                ),
                function(
                    "helper_non_assert_exit",
                    vec![qbe::Block {
                        label: "entry".to_string(),
                        items: vec![
                            qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Call(
                                "exit".to_string(),
                                vec![(qbe::Type::Word, qbe::Value::Const(1))],
                                None,
                            ))),
                            qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Hlt)),
                        ],
                    }],
                ),
            ],
            types: vec![],
            data: vec![],
        };

        rewrite_checker_assert_failure_exits(&mut module);

        assert!(matches!(
            module.functions[0].blocks[0].items.as_slice(),
            [qbe::BlockItem::Statement(qbe::Statement::Volatile(
                qbe::Instr::Ret(Some(qbe::Value::Const(0),))
            ))]
        ));
        assert!(matches!(
            module.functions[1].blocks[0].items.as_slice(),
            [
                qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Call(
                    function_name,
                    _,
                    None
                ))),
                qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Hlt))
            ] if function_name == "exit"
        ));
        assert!(matches!(
            module.functions[2].blocks[0].items.as_slice(),
            [
                qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Call(
                    function_name,
                    _,
                    None
                ))),
                qbe::BlockItem::Statement(qbe::Statement::Volatile(qbe::Instr::Hlt))
            ] if function_name == "exit"
        ));
    }
}
