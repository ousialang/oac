use std::{collections::HashMap, vec};

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

    let mut lt = Function::new(
        qbe::Linkage::public(),
        "lt".to_string(),
        vec![
            (qbe::Type::Word, qbe::Value::Temporary("a".to_string())),
            (qbe::Type::Word, qbe::Value::Temporary("b".to_string())),
        ],
        Some(qbe::Type::Word),
    );

    lt.add_block("start".to_string());

    lt.assign_instr(
        Value::Temporary("c".to_string()),
        Type::Word,
        Instr::Cmp(
            Type::Word,
            qbe::Cmp::Slt,
            Value::Temporary("a".to_string()),
            Value::Temporary("b".to_string()),
        ),
    );
    lt.add_instr(Instr::Ret(Some(Value::Temporary("c".to_string()))));
    module.add_function(lt);

    module.add_data(qbe::DataDef::new(
        Linkage::private(),
        "integer_fmt".to_string(),
        None,
        vec![
            (qbe::Type::Byte, DataItem::Str("%u\\n".to_string())),
            (qbe::Type::Byte, DataItem::Const(0)),
        ],
    ));

    let mut print = Function::new(
        qbe::Linkage::public(),
        "print".to_string(),
        vec![(Type::Word, Value::Temporary("a".to_string()))],
        Some(Type::Word),
    );

    print.add_block("start".to_string());
    print.add_instr(Instr::Call(
        "printf".to_string(),
        vec![
            (qbe::Type::Long, qbe::Value::Global("integer_fmt".into())),
            (qbe::Type::Word, qbe::Value::Temporary("a".to_string())),
        ],
        Some(1),
    ));
    print.add_instr(Instr::Ret(Some(Value::Const(0))));

    module.add_function(print);
}

pub fn compile(ir: ResolvedProgram) -> qbe::Module<'static> {
    let mut module = qbe::Module::default();

    add_builtins(&mut module);

    for func_def in ir.function_definitions.values() {
        compile_function(&mut module, func_def);
    }

    module
}

fn compile_statement(
    qbe_func: &mut qbe::Function,
    statement: &parser::Statement,
    variables: &mut HashMap<String, QbeAssignName>,
) {
    match statement {
        parser::Statement::While { condition, body } => {
            let condition_label = new_id();
            let start_label = new_id();
            let end_block_label = new_id();

            qbe_func.add_block(condition_label.clone());
            let condition_var = compile_expr(qbe_func, &condition, variables);

            qbe_func.add_instr(qbe::Instr::Jnz(
                qbe::Value::Temporary(condition_var),
                start_label.clone(),
                end_block_label.clone(),
            ));

            qbe_func.add_block(&start_label);
            for statement in body {
                compile_statement(qbe_func, statement, variables);
            }
            qbe_func.add_instr(qbe::Instr::Jmp(condition_label));

            qbe_func.add_block(&end_block_label);
        }
        parser::Statement::Return { expr } => {
            let expr_var = compile_expr(qbe_func, &expr, variables);
            trace!(%expr_var, "Emitting return instruction");
            qbe_func.add_instr(qbe::Instr::Ret(Some(qbe::Value::Temporary(expr_var))));
        }
        parser::Statement::Assign { variable, value } => {
            trace!(%variable, "Compiling assignment");

            let value_var = compile_expr(qbe_func, &value, variables);
            if let Some(existing_var) = variables.get(variable.as_str()) {
                qbe_func.assign_instr(
                    qbe::Value::Temporary(existing_var.clone()),
                    qbe::Type::Word,
                    qbe::Instr::Copy(qbe::Value::Temporary(value_var.clone())),
                );
            }
            variables.insert(variable.clone(), value_var);
        }
        parser::Statement::Expression { expr } => {
            compile_expr(qbe_func, &expr, variables);
        }
    }
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
        compile_statement(&mut qbe_func, statement, &mut variables);
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
                None,
            );

            func.assign_instr(Value::Temporary(id.clone()), Type::Word, instr);
        }
    }

    id
}

#[cfg(test)]
mod tests {
    use std::fs;

    use crate::{compile, Build};

    #[test]
    fn execution_tests() {
        let test_files = fs::read_dir("execution_tests").unwrap();

        for path in test_files {
            let path = path.unwrap().path();
            let tmp = tempfile::tempdir().unwrap();

            match compile(
                &tmp.path(),
                Build {
                    source: path.to_string_lossy().to_string(),
                },
            ) {
                Ok(()) => (),
                Err(err) => {
                    insta::assert_snapshot!(
                        path.display().to_string(),
                        format!("COMPILATION ERROR\n\n{err}")
                    );
                    continue;
                }
            };

            // run the executable and store the output in a string
            let output = std::process::Command::new("./target/oac/app")
                .current_dir(tmp.path())
                .output()
                .unwrap();
            let output = String::from_utf8(output.stdout).unwrap();

            insta::assert_snapshot!(path.display().to_string(), output);
        }
    }
}
