use std::{collections::HashMap, vec};

use qbe::*;
use tracing::trace;

type QbeAssignName = String;

use crate::{
    builtins::BuiltInType,
    ir::{self, ResolvedProgram},
    parser::{self, Op},
};

fn add_builtins(module: &mut qbe::Module<'static>) {
    {
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

    {
        let mut sub = Function::new(
            qbe::Linkage::public(),
            "sub".to_string(),
            vec![
                (qbe::Type::Word, qbe::Value::Temporary("a".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("b".to_string())),
            ],
            Some(qbe::Type::Word),
        );

        sub.add_block("start".to_string());

        sub.assign_instr(
            Value::Temporary("c".to_string()),
            Type::Word,
            Instr::Sub(
                Value::Temporary("a".to_string()),
                Value::Temporary("b".to_string()),
            ),
        );
        sub.add_instr(Instr::Ret(Some(Value::Temporary("c".to_string()))));
        module.add_function(sub);
    }

    {
        let mut eq = Function::new(
            qbe::Linkage::public(),
            "eq".to_string(),
            vec![
                (qbe::Type::Word, qbe::Value::Temporary("a".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("b".to_string())),
            ],
            Some(qbe::Type::Word),
        );

        eq.add_block("start".to_string());

        eq.assign_instr(
            Value::Temporary("c".to_string()),
            Type::Word,
            Instr::Cmp(
                Type::Word,
                qbe::Cmp::Eq,
                Value::Temporary("a".to_string()),
                Value::Temporary("b".to_string()),
            ),
        );
        eq.add_instr(Instr::Ret(Some(Value::Temporary("c".to_string()))));
        module.add_function(eq);
    }

    {
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
    }

    {
        module.add_data(qbe::DataDef::new(
            Linkage::private(),
            "integer_fmt".to_string(),
            None,
            vec![
                (qbe::Type::Byte, DataItem::Str("%u\\n".to_string())),
                (qbe::Type::Byte, DataItem::Const(0)),
            ],
        ));
    }

    {
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

    {
        module.add_data(qbe::DataDef::new(
            Linkage::private(),
            "string_fmt".to_string(),
            None,
            vec![
                (qbe::Type::Byte, DataItem::Str("%s\\n".to_string())),
                (qbe::Type::Byte, DataItem::Const(0)),
            ],
        ));

        let mut print_str = Function::new(
            qbe::Linkage::public(),
            "print_str".to_string(),
            vec![(Type::Long, Value::Temporary("a".to_string()))],
            Some(Type::Word),
        );

        print_str.add_block("start".to_string());
        print_str.add_instr(Instr::Call(
            "printf".to_string(),
            vec![
                (qbe::Type::Long, qbe::Value::Global("string_fmt".into())),
                (qbe::Type::Long, qbe::Value::Temporary("a".to_string())),
            ],
            Some(1),
        ));
        print_str.add_instr(Instr::Ret(Some(Value::Const(0))));

        module.add_function(print_str);
    }
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
    module: &mut qbe::Module<'static>,
    qbe_func: &mut qbe::Function,
    statement: &parser::Statement,
    variables: &mut Variables,
) {
    match statement {
        parser::Statement::Conditional { condition, body } => {
            let start_label = new_id();
            let end_block_label = new_id();

            let condition_var = compile_expr(module, qbe_func, &condition, variables).0;

            qbe_func.add_instr(qbe::Instr::Jnz(
                qbe::Value::Temporary(condition_var),
                start_label.clone(),
                end_block_label.clone(),
            ));

            qbe_func.add_block(&start_label);
            for statement in body {
                compile_statement(module, qbe_func, statement, variables);
            }

            qbe_func.add_block(&end_block_label);
        }
        parser::Statement::While { condition, body } => {
            let condition_label = new_id();
            let start_label = new_id();
            let end_block_label = new_id();

            qbe_func.add_block(condition_label.clone());
            let condition_var = compile_expr(module, qbe_func, &condition, variables).0;

            qbe_func.add_instr(qbe::Instr::Jnz(
                qbe::Value::Temporary(condition_var),
                start_label.clone(),
                end_block_label.clone(),
            ));

            qbe_func.add_block(&start_label);
            for statement in body {
                compile_statement(module, qbe_func, statement, variables);
            }
            qbe_func.add_instr(qbe::Instr::Jmp(condition_label));

            qbe_func.add_block(&end_block_label);
        }
        parser::Statement::Return { expr } => {
            let expr_var = compile_expr(module, qbe_func, &expr, variables).0;
            trace!(%expr_var, "Emitting return instruction");
            qbe_func.add_instr(qbe::Instr::Ret(Some(qbe::Value::Temporary(expr_var))));
        }
        parser::Statement::Assign { variable, value } => {
            trace!(%variable, "Compiling assignment");

            let value_var = compile_expr(module, qbe_func, &value, variables);
            if let Some(existing_var) = variables.get(variable.as_str()) {
                qbe_func.assign_instr(
                    qbe::Value::Temporary(existing_var.0.clone()),
                    qbe::Type::Word,
                    qbe::Instr::Copy(qbe::Value::Temporary(value_var.0.clone())),
                );
            }
            variables.insert(variable.clone(), value_var);
        }
        parser::Statement::Expression { expr } => {
            compile_expr(module, qbe_func, &expr, variables);
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
        variables.insert(param.name.clone(), (param.name.clone(), param.ty.clone()));
    }

    for statement in &func_def.body {
        compile_statement(module, &mut qbe_func, statement, &mut variables);
    }

    module.add_function(qbe_func);
}

fn new_id() -> String {
    format!("id{}", uuid::Uuid::now_v7().as_simple())
}

type Variables = HashMap<String, (QbeAssignName, BuiltInType)>;

fn compile_expr(
    module: &mut qbe::Module<'static>,
    func: &mut qbe::Function,
    expr: &parser::Expression,
    variables: &mut Variables,
) -> (QbeAssignName, BuiltInType) {
    trace!(?expr, "Compiling expression");

    let id = new_id();
    match expr {
        parser::Expression::Literal(parser::Literal::Int(value)) => {
            func.assign_instr(
                Value::Temporary(id.clone()),
                Type::Word,
                qbe::Instr::Copy(qbe::Value::Const(*value as u64)),
            );

            (id, BuiltInType::Int)
        }
        parser::Expression::Literal(parser::Literal::String(value)) => {
            let const_name = new_id();
            module.add_data(qbe::DataDef::new(
                Linkage::private(),
                const_name.clone(),
                None,
                vec![
                    (qbe::Type::Byte, DataItem::Str(value.clone())),
                    (qbe::Type::Byte, DataItem::Const(0)),
                ],
            ));
            func.assign_instr(
                Value::Temporary(id.clone()),
                Type::Long,
                qbe::Instr::Copy(qbe::Value::Global(const_name)),
            );

            (id, BuiltInType::String)
        }
        parser::Expression::Variable(name) => {
            return variables.get(name).unwrap().clone();
        }
        parser::Expression::Call(name, args) => {
            let mut arg_vars = vec![];
            for arg in args {
                let arg_var = compile_expr(module, func, arg, variables);
                arg_vars.push(arg_var);
            }

            let instr = qbe::Instr::Call(
                name.clone(),
                arg_vars
                    .iter()
                    // FIXME: word argument even for strings
                    .map(|v| {
                        let qbe_type = match v.1 {
                            BuiltInType::Int => qbe::Type::Word,
                            BuiltInType::I64 | BuiltInType::String => qbe::Type::Long,
                        };
                        (qbe_type, qbe::Value::Temporary(v.0.clone()))
                    })
                    .collect::<Vec<_>>(),
                None,
            );

            func.assign_instr(Value::Temporary(id.clone()), Type::Word, instr);

            (id, BuiltInType::Int) // FIXME: not all functions return int
        }
        parser::Expression::BinOp(op, left, right) => {
            let left_var = compile_expr(module, func, left, variables).0;
            let right_var = compile_expr(module, func, right, variables).0;

            let instr = match op {
                Op::Eq => qbe::Instr::Cmp(
                    qbe::Type::Word,
                    qbe::Cmp::Eq,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Neq => qbe::Instr::Cmp(
                    qbe::Type::Word,
                    qbe::Cmp::Ne,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Lt => qbe::Instr::Cmp(
                    qbe::Type::Word,
                    qbe::Cmp::Slt,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Gt => qbe::Instr::Cmp(
                    qbe::Type::Word,
                    qbe::Cmp::Sgt,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Le => qbe::Instr::Cmp(
                    qbe::Type::Word,
                    qbe::Cmp::Sle,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Ge => qbe::Instr::Cmp(
                    qbe::Type::Word,
                    qbe::Cmp::Sge,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Add => qbe::Instr::Add(
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Sub => qbe::Instr::Sub(
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Mul => qbe::Instr::Mul(
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Div => qbe::Instr::Div(
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
            };

            func.assign_instr(Value::Temporary(id.clone()), Type::Word, instr);

            (id, BuiltInType::Int)
        }
    }
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
                    arch: None,
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
