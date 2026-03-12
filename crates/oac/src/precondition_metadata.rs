use std::collections::{BTreeSet, HashMap};

use crate::ir::ResolvedProgram;

pub(crate) fn build_function_precondition_assumptions(
    program: &ResolvedProgram,
    checker_module_functions: &[qbe::Function],
) -> anyhow::Result<Vec<qbe_smt::FunctionEntryPreconditionAssumption>> {
    build_function_precondition_assumptions_with_name_overrides(
        program,
        checker_module_functions,
        &HashMap::new(),
    )
}

pub(crate) fn build_function_precondition_assumptions_with_name_overrides(
    program: &ResolvedProgram,
    checker_module_functions: &[qbe::Function],
    checker_to_program_name: &HashMap<String, String>,
) -> anyhow::Result<Vec<qbe_smt::FunctionEntryPreconditionAssumption>> {
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
    build_assumptions_from_function_name_pairs(program, &pairs)
}

pub(crate) fn build_function_precondition_assumptions_for_names(
    program: &ResolvedProgram,
    function_names: &BTreeSet<String>,
) -> anyhow::Result<Vec<qbe_smt::FunctionEntryPreconditionAssumption>> {
    let pairs = function_names
        .iter()
        .map(|name| (name.clone(), name.clone()))
        .collect::<Vec<_>>();
    build_assumptions_from_function_name_pairs(program, &pairs)
}

fn build_assumptions_from_function_name_pairs(
    program: &ResolvedProgram,
    function_name_pairs: &[(String, String)],
) -> anyhow::Result<Vec<qbe_smt::FunctionEntryPreconditionAssumption>> {
    let mut out = Vec::new();
    for (checker_name, semantic_name) in function_name_pairs {
        if !program.function_definitions.contains_key(semantic_name) {
            continue;
        }

        let Some(sig) = program.function_sigs.get(semantic_name) else {
            return Err(anyhow::anyhow!(
                "missing signature for function {} while building function-precondition assumptions",
                semantic_name
            ));
        };
        if sig.extern_symbol_name.is_some() {
            continue;
        }

        let Some(definitions) = program.function_preconditions.get(semantic_name) else {
            continue;
        };
        for definition in definitions {
            out.push(qbe_smt::FunctionEntryPreconditionAssumption {
                function_name: checker_name.clone(),
                precondition_function_name: definition.helper_function_name.clone(),
            });
        }
    }

    out.sort_by(|lhs, rhs| {
        lhs.function_name.cmp(&rhs.function_name).then(
            lhs.precondition_function_name
                .cmp(&rhs.precondition_function_name),
        )
    });
    out.dedup_by(|lhs, rhs| {
        lhs.function_name == rhs.function_name
            && lhs.precondition_function_name == rhs.precondition_function_name
    });
    Ok(out)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{
        build_function_precondition_assumptions, build_function_precondition_assumptions_for_names,
    };
    use crate::{ir, parser, tokenizer};

    fn resolve_program(source: &str) -> ir::ResolvedProgram {
        let tokens = tokenizer::tokenize(source.to_string()).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        ir::resolve(ast).expect("resolve source")
    }

    fn qbe_function(name: &str) -> qbe::Function {
        qbe::Function::new(
            qbe::Linkage::private(),
            name.to_string(),
            vec![],
            Some(qbe::Type::Word),
        )
    }

    #[test]
    fn builds_function_precondition_assumptions_for_named_functions() {
        let program = resolve_program(
            r#"
fun guarded(x: I32) -> I32 pre {
	x > 5
	x < 20
} {
	return x
}

fun main() -> I32 {
	return guarded(7)
}
"#,
        );

        let assumptions = build_function_precondition_assumptions_for_names(
            &program,
            &BTreeSet::from(["guarded".to_string(), "main".to_string()]),
        )
        .expect("build assumptions");

        assert_eq!(assumptions.len(), 2);
        assert_eq!(assumptions[0].function_name, "guarded");
        assert_eq!(
            assumptions[0].precondition_function_name,
            "__pre__guarded__clause_0"
        );
        assert_eq!(assumptions[1].function_name, "guarded");
        assert_eq!(
            assumptions[1].precondition_function_name,
            "__pre__guarded__clause_1"
        );
    }

    #[test]
    fn skips_backend_only_helpers_when_building_precondition_assumptions() {
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

        let assumptions = build_function_precondition_assumptions(
            &program,
            &[qbe_function("__string_data_ptr"), qbe_function("guarded")],
        )
        .expect("build assumptions");

        assert_eq!(assumptions.len(), 1);
        assert_eq!(assumptions[0].function_name, "guarded");
        assert_eq!(
            assumptions[0].precondition_function_name,
            "__pre__guarded__clause_0"
        );
    }
}
