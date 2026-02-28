use std::collections::{BTreeSet, HashMap, HashSet};

use crate::ir::{ResolvedProgram, TypeDef};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct InvariantBinding {
    pub(crate) function_name: String,
    pub(crate) display_name: String,
    pub(crate) identifier: Option<String>,
}

pub(crate) fn discover_struct_invariant_bindings(
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

pub(crate) fn build_function_arg_invariant_assumptions(
    program: &ResolvedProgram,
    checker_module_functions: &[qbe::Function],
    invariant_bindings: &HashMap<String, InvariantBinding>,
) -> anyhow::Result<Vec<qbe_smt::FunctionArgInvariantAssumption>> {
    build_function_arg_invariant_assumptions_with_name_overrides(
        program,
        checker_module_functions,
        invariant_bindings,
        &HashMap::new(),
    )
}

pub(crate) fn build_function_arg_invariant_assumptions_with_name_overrides(
    program: &ResolvedProgram,
    checker_module_functions: &[qbe::Function],
    invariant_bindings: &HashMap<String, InvariantBinding>,
    checker_to_program_name: &HashMap<String, String>,
) -> anyhow::Result<Vec<qbe_smt::FunctionArgInvariantAssumption>> {
    let mut pairs = checker_module_functions
        .iter()
        .map(|function| {
            let semantic = checker_to_program_name
                .get(&function.name)
                .cloned()
                .unwrap_or_else(|| function.name.clone());
            (function.name.clone(), semantic)
        })
        .collect::<Vec<_>>();
    pairs.sort_by(|lhs, rhs| lhs.0.cmp(&rhs.0).then(lhs.1.cmp(&rhs.1)));
    build_assumptions_from_function_name_pairs(program, &pairs, invariant_bindings)
}

pub(crate) fn build_function_arg_invariant_assumptions_for_names(
    program: &ResolvedProgram,
    function_names: &BTreeSet<String>,
    invariant_bindings: &HashMap<String, InvariantBinding>,
) -> anyhow::Result<Vec<qbe_smt::FunctionArgInvariantAssumption>> {
    let pairs = function_names
        .iter()
        .map(|name| (name.clone(), name.clone()))
        .collect::<Vec<_>>();
    build_assumptions_from_function_name_pairs(program, &pairs, invariant_bindings)
}

fn build_assumptions_from_function_name_pairs(
    program: &ResolvedProgram,
    function_name_pairs: &[(String, String)],
    invariant_bindings: &HashMap<String, InvariantBinding>,
) -> anyhow::Result<Vec<qbe_smt::FunctionArgInvariantAssumption>> {
    let invariant_function_names = invariant_bindings
        .values()
        .map(|binding| binding.function_name.as_str())
        .collect::<HashSet<_>>();

    let mut out = Vec::new();
    for (checker_name, semantic_name) in function_name_pairs {
        if invariant_function_names.contains(semantic_name.as_str()) {
            continue;
        }

        let Some(sig) = program.function_sigs.get(semantic_name) else {
            return Err(anyhow::anyhow!(
                "missing signature for function {} while building argument-invariant assumptions",
                semantic_name
            ));
        };
        if sig.extern_symbol_name.is_some() {
            continue;
        }
        if !program.function_definitions.contains_key(semantic_name) {
            continue;
        }

        for (arg_index, parameter) in sig.parameters.iter().enumerate() {
            let Some(invariant) = invariant_bindings.get(&parameter.ty) else {
                continue;
            };
            out.push(qbe_smt::FunctionArgInvariantAssumption {
                function_name: checker_name.clone(),
                arg_index,
                invariant_function_name: invariant.function_name.clone(),
            });
        }
    }

    out.sort_by(|lhs, rhs| {
        lhs.function_name
            .cmp(&rhs.function_name)
            .then(lhs.arg_index.cmp(&rhs.arg_index))
            .then(
                lhs.invariant_function_name
                    .cmp(&rhs.invariant_function_name),
            )
    });
    out.dedup_by(|lhs, rhs| {
        lhs.function_name == rhs.function_name
            && lhs.arg_index == rhs.arg_index
            && lhs.invariant_function_name == rhs.invariant_function_name
    });
    Ok(out)
}
