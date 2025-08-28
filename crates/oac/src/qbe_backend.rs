use std::{collections::HashMap, vec};

use qbe::*;
use tracing::trace;

type QbeAssignName = String;

use crate::{
    builtins::BuiltInType,
    ir::{self, ResolvedProgram},
    parser::{self, Op, StructDef},
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

fn type_to_qbe(ty: &ir::TypeDef) -> qbe::Type<'static> {
    match ty {
        ir::TypeDef::BuiltIn(BuiltInType::Int) => qbe::Type::Word,
        ir::TypeDef::BuiltIn(BuiltInType::I64) => qbe::Type::Long,
        ir::TypeDef::BuiltIn(BuiltInType::String) => qbe::Type::Long,
        ir::TypeDef::Struct(_) => qbe::Type::Long,
    }
}

fn compile_type(module: &mut qbe::Module, program: &ResolvedProgram, type_def: &ir::TypeDef) {
    trace!("Compiling type {:?}", type_def);

    match type_def {
        ir::TypeDef::BuiltIn(_) => {} // We generated those already
        ir::TypeDef::Struct(StructDef {
            struct_fields,
            name,
        }) => {
            let mut items = vec![];
            for field in struct_fields.iter() {
                let field_type = program.type_definitions.get(&field.ty).unwrap();
                let qbe_type = type_to_qbe(field_type);
                items.push((qbe_type, 1));
            }
            module.add_type(qbe::TypeDef {
                name: name.to_string(),
                align: None,
                items,
            });
        }
    }
}

pub fn compile(ir: ResolvedProgram) -> qbe::Module<'static> {
    let mut module = qbe::Module::default();

    add_builtins(&mut module);

    for type_def in ir.type_definitions.values() {
        compile_type(&mut module, &ir, type_def);
    }

    for func_def in ir.function_definitions.values() {
        compile_function(&mut module, ir.clone(), func_def.clone());
    }

    module
}

fn compile_statement(
    module: &mut qbe::Module<'static>,
    qbe_func: &mut qbe::Function<'static>,
    statement: &parser::Statement,
    program: ResolvedProgram,
    variables: &mut Variables,
) {
    match statement {
        parser::Statement::StructDef { def } => {
            let struct_type = program.type_definitions.get(&def.name).unwrap();
            if let ir::TypeDef::Struct(s) = struct_type {
                module.add_type(qbe::TypeDef {
                    name: s.name.to_string(),
                    align: None,
                    items: s
                        .struct_fields
                        .iter()
                        .map(|field| {
                            let field_type = program.type_definitions.get(&field.ty).unwrap();
                            (type_to_qbe(field_type), 1)
                        })
                        .collect(),
                });
            }
        }
        parser::Statement::Conditional { condition, body } => {
            let start_label = new_id();
            let end_block_label = new_id();

            let condition_var =
                compile_expr(module, qbe_func, &condition, program.clone(), variables).0;

            qbe_func.add_instr(qbe::Instr::Jnz(
                qbe::Value::Temporary(condition_var),
                start_label.clone(),
                end_block_label.clone(),
            ));

            qbe_func.add_block(&start_label);
            for statement in body {
                compile_statement(module, qbe_func, statement, program.clone(), variables);
            }

            qbe_func.add_block(&end_block_label);
        }
        parser::Statement::While { condition, body } => {
            let condition_label = new_id();
            let start_label = new_id();
            let end_block_label = new_id();

            qbe_func.add_block(condition_label.clone());
            let condition_var =
                compile_expr(module, qbe_func, &condition, program.clone(), variables).0;

            qbe_func.add_instr(qbe::Instr::Jnz(
                qbe::Value::Temporary(condition_var),
                start_label.clone(),
                end_block_label.clone(),
            ));

            qbe_func.add_block(&start_label);
            for statement in body {
                compile_statement(module, qbe_func, statement, program.clone(), variables);
            }
            qbe_func.add_instr(qbe::Instr::Jmp(condition_label));

            qbe_func.add_block(&end_block_label);
        }
        parser::Statement::Return { expr } => {
            let expr_var = compile_expr(module, qbe_func, &expr, program.clone(), variables).0;
            trace!(%expr_var, "Emitting return instruction");
            qbe_func.add_instr(qbe::Instr::Ret(Some(qbe::Value::Temporary(expr_var))));
        }
        parser::Statement::Assign { variable, value } => {
            trace!(%variable, "Compiling assignment");

            let value_var = compile_expr(module, qbe_func, &value, program.clone(), variables);
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
            compile_expr(module, qbe_func, &expr, program.clone(), variables);
        }
    }
}

fn compile_function(
    module: &mut qbe::Module<'static>,
    program: ResolvedProgram,
    func_def: ir::FunctionDefinition,
) {
    let qbe_args = func_def
        .sig
        .parameters
        .iter()
        .map(|param| {
            let ty = program.type_definitions.get(&param.ty).unwrap();
            (type_to_qbe(ty), qbe::Value::Temporary(param.name.clone()))
        })
        .collect::<Vec<_>>();

    let return_type_def = program
        .type_definitions
        .get(&func_def.sig.return_type)
        .unwrap();

    let mut qbe_func = qbe::Function::new(
        qbe::Linkage::public(),
        func_def.name.clone(),
        qbe_args,
        Some(type_to_qbe(return_type_def)),
    );

    qbe_func.add_block("start".to_string());

    let mut variables = HashMap::new();

    for param in &func_def.sig.parameters {
        variables.insert(param.name.clone(), (param.name.clone(), param.ty.clone()));
    }

    for statement in &func_def.body {
        compile_statement(
            module,
            &mut qbe_func,
            statement,
            program.clone(),
            &mut variables,
        );
    }

    module.add_function(qbe_func);
}

fn new_id() -> String {
    format!(".L{}", uuid::Uuid::now_v7().as_simple())
}

type Variables = HashMap<String, (QbeAssignName, ir::TypeRef)>;

fn compile_expr(
    module: &mut qbe::Module<'static>,
    func: &mut qbe::Function<'static>,
    expr: &parser::Expression,
    program: ResolvedProgram,
    variables: &mut Variables,
) -> (QbeAssignName, ir::TypeRef) {
    trace!(?expr, "Compiling expression");

    let id = new_id();
    match expr {
        parser::Expression::FieldAccess(expr, field) => {
            let (expr_var, expr_type) =
                compile_expr(module, func, expr, program.clone(), variables);
            let type_def = program.type_definitions.get(&expr_type).unwrap().clone();
            let return_type = if let ir::TypeDef::Struct(s) = type_def {
                s.struct_fields
                    .iter()
                    .find(|f| f.name == *field)
                    .unwrap()
                    .ty
                    .clone()
            } else {
                panic!("Expected struct type")
            };

            func.assign_instr(
                Value::Temporary(id.clone()),
                type_to_qbe(program.type_definitions.get(&return_type).unwrap()),
                Instr::Load(
                    type_to_qbe(program.type_definitions.get(&return_type).unwrap()),
                    Value::Temporary(format!("{}.{}", expr_var, field)),
                ),
            );

            (id, return_type)
        }
        parser::Expression::StructValue {
            struct_name,
            field_values,
        } => {
            let struct_def = program.type_definitions.get(struct_name).unwrap();
            if let ir::TypeDef::Struct(s) = struct_def {
                for (field_name, field_value) in field_values {
                    let (field_var, _) =
                        compile_expr(module, func, field_value, program.clone(), variables);
                    let field = s
                        .struct_fields
                        .iter()
                        .find(|f| &f.name == field_name)
                        .unwrap();
                    let field_type = program.type_definitions.get(&field.ty).unwrap().clone();
                    func.add_instr(Instr::Store(
                        type_to_qbe(&field_type),
                        Value::Temporary(field_var),
                        Value::Temporary(format!("{}.{}", id, field_name)),
                    ));
                }
            }

            (id, struct_name.to_string())
        }
        parser::Expression::Literal(parser::Literal::Int(value)) => {
            func.assign_instr(
                Value::Temporary(id.clone()),
                Type::Word,
                qbe::Instr::Copy(qbe::Value::Const(*value as u64)),
            );

            (id, "I32".to_string())
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

            (id, "String".to_string())
        }
        parser::Expression::Variable(name) => {
            return variables.get(name).unwrap().clone();
        }
        parser::Expression::Call(name, args) => {
            let mut arg_vars = vec![];
            for arg in args {
                let arg_var = compile_expr(module, func, arg, program.clone(), variables);
                arg_vars.push(arg_var);
            }

            let instr = qbe::Instr::Call(
                name.clone(),
                arg_vars
                    .iter()
                    .map(|v| {
                        let type_def = program.type_definitions.get(&v.1).unwrap();
                        let qbe_type = type_to_qbe(type_def);
                        (qbe_type, qbe::Value::Temporary(v.0.clone()))
                    })
                    .collect::<Vec<_>>(),
                None,
            );

            let sig = program.function_sigs.get(name).unwrap().clone();
            let return_type_def = program
                .type_definitions
                .get(&sig.return_type)
                .unwrap()
                .clone();
            let tmp_id_type = type_to_qbe(&return_type_def);

            func.assign_instr(Value::Temporary(id.clone()), tmp_id_type, instr);

            (id, sig.return_type.clone())
        }
        parser::Expression::BinOp(op, left, right) => {
            let left_var = compile_expr(module, func, left, program.clone(), variables).0;
            let right_var = compile_expr(module, func, right, program.clone(), variables).0;

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

            func.assign_instr(qbe::Value::Temporary(id.clone()), qbe::Type::Word, instr);

            (id, "I32".to_string())
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{compile, ir, parser::parse, tokenizer::tokenize, Build};
    use std::{fs, path::Path};

    use super::compile as compile_qbe;

    fn compile_and_compare(fixture_name: &str) {
        let path_str = format!("crates/oac/execution_tests/{}.oa", fixture_name);
        let path = Path::new(&path_str);
        let file_contents = std::fs::read_to_string(path)
            .unwrap_or_else(|_| panic!("Could not read test fixture: {}", path.display()));

        let tokens = tokenize(file_contents).unwrap();
        let program = parse(tokens).unwrap();
        let ir = ir::resolve(program).unwrap();

        let qbe_module = compile_qbe(ir);

        let qbe_ir = format!("{}", qbe_module);
        insta::assert_snapshot!(qbe_ir);
    }

    #[test]
    fn execution_tests() {
        let test_files = fs::read_dir("execution_tests").unwrap();

        for path in test_files {
            println!("Testing {}", path.as_ref().unwrap().path().display());

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
