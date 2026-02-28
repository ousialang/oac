use std::collections::{BTreeSet, HashMap, HashSet};

use crate::ir::{ResolvedProgram, TypeDef};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct InvariantBinding {
    pub(crate) function_name: String,
    pub(crate) key: String,
    pub(crate) display_name: String,
    pub(crate) identifier: Option<String>,
}

pub(crate) fn discover_struct_invariant_bindings(
    program: &ResolvedProgram,
) -> anyhow::Result<HashMap<String, Vec<InvariantBinding>>> {
    let mut invariant_by_struct = HashMap::<String, Vec<InvariantBinding>>::new();

    for (struct_name, invariants) in &program.struct_invariants {
        let ty = program
            .type_definitions
            .get(struct_name)
            .ok_or_else(|| anyhow::anyhow!("invariant targets unknown type {}", struct_name))?;
        if !matches!(ty, TypeDef::Struct(_)) {
            return Err(anyhow::anyhow!(
                "invariants for {} must target a struct type, but {} is not a struct",
                struct_name,
                struct_name
            ));
        }

        let bindings = invariant_by_struct
            .entry(struct_name.to_string())
            .or_insert_with(Vec::new);
        for invariant in invariants {
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

            if let Some(existing) = bindings
                .iter()
                .find(|existing| existing.key == invariant.key)
            {
                return Err(anyhow::anyhow!(
                    "struct {} has duplicate invariant key `{}`: \"{}\" and \"{}\"",
                    struct_name,
                    invariant.key,
                    existing.display_name,
                    invariant.display_name
                ));
            }

            bindings.push(InvariantBinding {
                function_name: invariant.function_name.clone(),
                key: invariant.key.clone(),
                display_name: invariant.display_name.clone(),
                identifier: invariant.identifier.clone(),
            });
        }
    }

    Ok(invariant_by_struct)
}

pub(crate) fn build_function_arg_invariant_assumptions(
    program: &ResolvedProgram,
    checker_module_functions: &[qbe::Function],
    invariant_bindings: &HashMap<String, Vec<InvariantBinding>>,
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
    invariant_bindings: &HashMap<String, Vec<InvariantBinding>>,
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
    invariant_bindings: &HashMap<String, Vec<InvariantBinding>>,
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
    invariant_bindings: &HashMap<String, Vec<InvariantBinding>>,
) -> anyhow::Result<Vec<qbe_smt::FunctionArgInvariantAssumption>> {
    let invariant_function_names = invariant_bindings
        .values()
        .flat_map(|bindings| {
            bindings
                .iter()
                .map(|binding| binding.function_name.as_str())
        })
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
            let Some(invariants) = invariant_bindings.get(&parameter.ty) else {
                continue;
            };
            for invariant in invariants {
                out.push(qbe_smt::FunctionArgInvariantAssumption {
                    function_name: checker_name.clone(),
                    arg_index,
                    invariant_function_name: invariant.function_name.clone(),
                });
            }
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

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{
        build_function_arg_invariant_assumptions_for_names, discover_struct_invariant_bindings,
    };
    use crate::{ir, parser, tokenizer};

    fn resolve_program(source: &str) -> ir::ResolvedProgram {
        let tokens = tokenizer::tokenize(source.to_string()).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        ir::resolve(ast).expect("resolve source")
    }

    #[test]
    fn discovers_multiple_bindings_for_one_struct() {
        let program = resolve_program(
            r#"
struct Counter {
	value: I32,
	max: I32,
}

invariant for (v: Counter) {
	non_negative_value "counter value must be non-negative" {
		return v.value >= 0
	}
	"counter max must be non-negative" {
		return v.max >= 0
	}
}

fun main() -> I32 {
	return 0
}
"#,
        );

        let bindings = discover_struct_invariant_bindings(&program).expect("discover bindings");
        let counter = bindings.get("Counter").expect("Counter bindings");
        assert_eq!(counter.len(), 2);
        assert_eq!(counter[0].key, "non_negative_value");
        assert_eq!(counter[1].key, "anon_0");
    }

    #[test]
    fn builds_argument_assumptions_as_cross_product_over_struct_invariants() {
        let program = resolve_program(
            r#"
struct Counter {
	value: I32,
	max: I32,
}

invariant value_non_negative "counter value must be non-negative" for (v: Counter) {
	return v.value >= 0
}

invariant max_non_negative "counter max must be non-negative" for (v: Counter) {
	return v.max >= 0
}

fun combine(lhs: Counter, rhs: Counter) -> I32 {
	return lhs.value + rhs.max
}

fun main() -> I32 {
	c = Counter struct { value: 1, max: 1, }
	return combine(c, c)
}
"#,
        );

        let bindings = discover_struct_invariant_bindings(&program).expect("discover bindings");
        let assumptions = build_function_arg_invariant_assumptions_for_names(
            &program,
            &BTreeSet::from(["combine".to_string()]),
            &bindings,
        )
        .expect("build argument assumptions");

        assert_eq!(assumptions.len(), 4);
        assert_eq!(assumptions[0].function_name, "combine");
        assert_eq!(assumptions[0].arg_index, 0);
        assert_eq!(
            assumptions[0].invariant_function_name,
            "__struct__Counter__invariant__max_non_negative"
        );
        assert_eq!(assumptions[1].function_name, "combine");
        assert_eq!(assumptions[1].arg_index, 0);
        assert_eq!(
            assumptions[1].invariant_function_name,
            "__struct__Counter__invariant__value_non_negative"
        );
        assert_eq!(assumptions[2].function_name, "combine");
        assert_eq!(assumptions[2].arg_index, 1);
        assert_eq!(
            assumptions[2].invariant_function_name,
            "__struct__Counter__invariant__max_non_negative"
        );
        assert_eq!(assumptions[3].function_name, "combine");
        assert_eq!(assumptions[3].arg_index, 1);
        assert_eq!(
            assumptions[3].invariant_function_name,
            "__struct__Counter__invariant__value_non_negative"
        );
    }
}
