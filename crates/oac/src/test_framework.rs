use std::collections::HashSet;

use crate::parser::{Ast, Expression, Function, Literal, Statement};

pub const GENERATED_TEST_FUNCTION_PREFIX: &str = "__oac_test_case_";

#[derive(Clone, Debug)]
pub struct LoweredTestProgram {
    pub ast: Ast,
    pub test_names: Vec<String>,
}

pub fn lower_tests_to_program(mut ast: Ast) -> anyhow::Result<LoweredTestProgram> {
    if ast.tests.is_empty() {
        return Err(anyhow::anyhow!(
            "no test declarations found; expected at least one `test \"...\" {{ ... }}` block"
        ));
    }

    if ast.top_level_functions.iter().any(|f| f.name == "main") {
        return Err(anyhow::anyhow!(
            "`oac test` sources cannot define `main`; tests synthesize `main` automatically"
        ));
    }

    let mut function_names = ast
        .top_level_functions
        .iter()
        .map(|f| f.name.clone())
        .collect::<HashSet<_>>();

    let tests = std::mem::take(&mut ast.tests);
    let mut test_names = Vec::with_capacity(tests.len());

    for (index, test) in tests.into_iter().enumerate() {
        let function_name = format!("{GENERATED_TEST_FUNCTION_PREFIX}{index}");
        if !function_names.insert(function_name.clone()) {
            return Err(anyhow::anyhow!(
                "generated test function name collision: {}",
                function_name
            ));
        }

        let mut body = test.body;
        body.push(Statement::Return {
            expr: Expression::Literal(Literal::Int(0)),
        });

        ast.top_level_functions.push(Function {
            name: function_name,
            extern_symbol_name: None,
            parameters: vec![],
            body,
            return_type: "I32".to_string(),
            is_comptime: false,
            is_extern: false,
        });
        test_names.push(test.name);
    }

    let mut main_body = vec![print_str_stmt(format!(
        "running {} test(s)",
        test_names.len()
    ))];
    for (index, test_name) in test_names.iter().enumerate() {
        main_body.push(print_str_stmt(format!("test {}: {}", index + 1, test_name)));
        main_body.push(Statement::Expression {
            expr: Expression::Call(
                format!("{GENERATED_TEST_FUNCTION_PREFIX}{index}"),
                Vec::new(),
            ),
        });
    }
    main_body.push(print_str_stmt(format!(
        "ok: {} test(s) passed",
        test_names.len()
    )));
    main_body.push(Statement::Return {
        expr: Expression::Literal(Literal::Int(0)),
    });

    ast.top_level_functions.push(Function {
        name: "main".to_string(),
        extern_symbol_name: None,
        parameters: vec![],
        body: main_body,
        return_type: "I32".to_string(),
        is_comptime: false,
        is_extern: false,
    });

    Ok(LoweredTestProgram { ast, test_names })
}

fn print_str_stmt(message: String) -> Statement {
    Statement::Expression {
        expr: Expression::Call(
            "print_str".to_string(),
            vec![Expression::Literal(Literal::String(message))],
        ),
    }
}

#[cfg(test)]
mod tests {
    use crate::{parser, tokenizer};

    use super::{lower_tests_to_program, GENERATED_TEST_FUNCTION_PREFIX};

    fn parse_source(source: &str) -> parser::Ast {
        let tokens = tokenizer::tokenize(source.to_string()).expect("tokenize source");
        parser::parse(tokens).expect("parse source")
    }

    #[test]
    fn lowers_tests_to_generated_functions_and_main() {
        let ast = parse_source(
            r#"
test "first" {
	assert(true)
}

test "second" {
	assert(true)
}
"#,
        );

        let lowered = lower_tests_to_program(ast).expect("lower test declarations");

        assert_eq!(lowered.test_names, vec!["first", "second"]);
        assert!(
            lowered.ast.tests.is_empty(),
            "tests should be fully lowered"
        );

        assert!(lowered
            .ast
            .top_level_functions
            .iter()
            .any(|f| f.name == format!("{GENERATED_TEST_FUNCTION_PREFIX}0")));
        assert!(lowered
            .ast
            .top_level_functions
            .iter()
            .any(|f| f.name == format!("{GENERATED_TEST_FUNCTION_PREFIX}1")));

        let main = lowered
            .ast
            .top_level_functions
            .iter()
            .find(|f| f.name == "main")
            .expect("generated main");
        assert_eq!(main.return_type, "I32");
        assert!(matches!(
            main.body.last(),
            Some(parser::Statement::Return {
                expr: parser::Expression::Literal(parser::Literal::Int(0))
            })
        ));
    }

    #[test]
    fn rejects_empty_test_set() {
        let ast = parse_source(
            r#"
fun helper() -> I32 {
	return 1
}
"#,
        );
        let err = lower_tests_to_program(ast).expect_err("must reject missing tests");
        assert!(err.to_string().contains("no test declarations found"));
    }

    #[test]
    fn rejects_user_defined_main() {
        let ast = parse_source(
            r#"
test "first" {
	assert(true)
}

fun main() -> I32 {
	return 0
}
"#,
        );
        let err = lower_tests_to_program(ast).expect_err("must reject user-defined main");
        assert!(err.to_string().contains("cannot define `main`"));
    }
}
