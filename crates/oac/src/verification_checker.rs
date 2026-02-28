use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use crate::invariant_metadata::{
    build_function_arg_invariant_assumptions,
    build_function_arg_invariant_assumptions_with_name_overrides, InvariantBinding,
};
use crate::ir::ResolvedProgram;

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
            build_function_arg_invariant_assumptions(
                program,
                &module.functions,
                invariant_by_struct,
            )?
        } else {
            build_function_arg_invariant_assumptions_with_name_overrides(
                program,
                &module.functions,
                invariant_by_struct,
                checker_to_program_name,
            )?
        };
        let required_invariant_functions = assumptions
            .iter()
            .map(|assumption| assumption.invariant_function_name.clone())
            .collect::<BTreeSet<_>>();

        let mut next_roots = additional_roots.clone();
        next_roots.extend(required_invariant_functions);
        if next_roots == additional_roots {
            return Ok((
                module,
                qbe_smt::ModuleAssumptions {
                    arg_invariant_assumptions: assumptions,
                },
            ));
        }
        additional_roots = next_roots;
    }
}

pub(crate) fn direct_user_callees(
    function: &qbe::Function,
    function_map: &HashMap<String, qbe::Function>,
) -> BTreeSet<String> {
    let mut callees = BTreeSet::new();
    for block in &function.blocks {
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
        }
    }
    callees
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
