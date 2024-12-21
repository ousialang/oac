use std::{collections::HashMap, env::var};

use qbe::*;
use tracing::trace;

type QbeAssignName = String;

use crate::{
    ir::{self, ResolvedProgram},
    parser,
};

fn add_builtins(module: &mut qbe::Module<'static>) {
    let mut sum = qbe::Function::new(
        qbe::Linkage::public(),
        "sum".to_string(),
        vec![
            (qbe::Type::Word, qbe::Value::Temporary("a".to_string())),
            (qbe::Type::Word, qbe::Value::Temporary("b".to_string())),
        ],
        Some(qbe::Type::Word),
    );

    sum.add_block("start".to_string());

    sum.assign_instr(
        Value::Temporary("c".to_string()),
        Type::Word,
        Instr::Add(
            Value::Temporary("a".to_string()),
            Value::Temporary("b".to_string()),
        ),
    );
    sum.add_instr(Instr::Ret(Some(Value::Temporary("c".to_string()))));

    module.add_function(sum);
}

pub fn compile(ir: ResolvedProgram) -> qbe::Module<'static> {
    let mut module = qbe::Module::default();

    add_builtins(&mut module);

    for func_def in ir.function_definitions.values() {
        compile_function(&mut module, func_def);
    }

    module
}

fn compile_function(module: &mut qbe::Module<'static>, func_def: &ir::FunctionDefinition) {
    let qbe_args = func_def
        .sig
        .parameters
        .iter()
        // TODO: string arguments
        .map(|param| (qbe::Type::Word, qbe::Value::Temporary(param.name.clone())))
        .collect::<Vec<_>>();

    let mut qbe_func = qbe::Function::new(
        qbe::Linkage::public(),
        func_def.name.clone(),
        qbe_args,
        // TODO: handle return type
        Some(qbe::Type::Word),
    );

    qbe_func.add_block("start".to_string());

    let mut variables = HashMap::new();

    for param in &func_def.sig.parameters {
        variables.insert(param.name.clone(), param.name.clone());
    }

    for statement in &func_def.body {
        match statement {
            parser::Statement::Return { expr } => {
                let expr_var = compile_expr(&mut qbe_func, &expr, &mut variables);
                trace!(%expr_var, "Emitting return instruction");
                qbe_func.add_instr(qbe::Instr::Ret(Some(qbe::Value::Temporary(expr_var))));
            }
            parser::Statement::Assign { variable, value } => {
                trace!(%variable, "Compiling assignment");

                let value_var = compile_expr(&mut qbe_func, &value, &mut variables);
                variables.insert(variable.clone(), value_var);
            }
            parser::Statement::Expression { expr } => {
                compile_expr(&mut qbe_func, &expr, &mut variables);
            }
        }
    }

    module.add_function(qbe_func);
}

fn new_id() -> String {
    format!("id{}", uuid::Uuid::now_v7().as_simple())
}

fn compile_expr(
    func: &mut qbe::Function,
    expr: &parser::Expression,
    variables: &mut HashMap<String, QbeAssignName>,
) -> QbeAssignName {
    trace!(?expr, "Compiling expression");

    let id = new_id();
    match expr {
        parser::Expression::Literal(parser::Literal::Int(value)) => {
            func.assign_instr(
                Value::Temporary(id.clone()),
                Type::Word,
                qbe::Instr::Copy(qbe::Value::Const(*value as u64)),
            );
        }
        parser::Expression::Literal(parser::Literal::String(_value)) => {
            func.assign_instr(
                Value::Temporary(id.clone()),
                Type::Word,
                qbe::Instr::Copy(qbe::Value::Const(0)), // TODO
            );
        }
        parser::Expression::Variable(name) => {
            return variables.get(name).unwrap().clone();
        }
        parser::Expression::Call(name, args) => {
            let mut arg_vars = vec![];
            for arg in args {
                let arg_var = compile_expr(func, arg, variables);
                arg_vars.push(arg_var);
            }

            let instr = qbe::Instr::Call(
                name.clone(),
                arg_vars
                    .iter()
                    .map(|v| (qbe::Type::Word, qbe::Value::Temporary(v.clone())))
                    .collect::<Vec<_>>(),
            );

            func.assign_instr(Value::Temporary(id.clone()), Type::Word, instr);
        }
    }

    id
}

#[cfg(test)]
mod tests {
    use std::fs;

    use crate::{ir, parser, qbe_backend, tokenizer};
    use std::io::Write;

    #[test]
    fn execution_tests() {
        let test_files = fs::read_dir("execution_tests").unwrap();

        for path in test_files {
            let tmp = tempfile::tempdir().unwrap();

            let path = path.unwrap().path();

            let source = std::fs::read_to_string(&path).unwrap();
            let tokens = tokenizer::tokenize(source).unwrap();
            let ast = parser::parse(tokens).unwrap();
            let ir = ir::resolve(ast).unwrap();
            let qbe_ir = qbe_backend::compile(ir);

            let qbe_ir_filepath = tmp.path().join("test.qbe");

            let mut file = std::fs::File::create(&qbe_ir_filepath).unwrap();
            file.write_all(qbe_ir.to_string().as_bytes()).unwrap();

            let assembly_filepath = tmp.path().join("test.s");
            // run qbe -o $path $path.s && cc $path.s
            std::process::Command::new("qbe")
                .arg("-o")
                .arg(&assembly_filepath)
                .arg(&qbe_ir_filepath)
                .output()
                .unwrap();
            std::process::Command::new("cc")
                .arg(&assembly_filepath)
                .output()
                .unwrap();

            // run the executable and store the output in a string
            let output = std::process::Command::new("./a.out").output().unwrap();
            let output = String::from_utf8(output.stdout).unwrap();

            insta::assert_snapshot!(path.display().to_string(), output);
        }
    }
}
