use std::{collections::HashMap, sync::Arc, vec};

use qbe::*;
use tracing::trace;

use crate::{
    builtins::BuiltInType,
    ir::{self, ResolvedProgram},
    parser::{self, Op, StructDef},
};

type QbeAssignName = String;
type Variables = HashMap<String, (QbeAssignName, ir::TypeRef)>;

struct CodegenCtx {
    module: qbe::Module,
    resolved: Arc<ResolvedProgram>,
    qbe_types_by_name: HashMap<String, qbe::Type>,
}

fn add_builtins(ctx: &mut CodegenCtx) {
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

        ctx.module.add_function(sum);
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
        ctx.module.add_function(sub);
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
        ctx.module.add_function(eq);
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
        ctx.module.add_function(lt);
    }

    {
        ctx.module.add_data(qbe::DataDef::new(
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

        ctx.module.add_function(print);
    }

    {
        let mut f = Function::new(
            Linkage::private(),
            "i32_to_i64".to_string(),
            vec![(qbe::Type::Word, qbe::Value::Temporary("a".to_string()))],
            Some(Type::Long),
        );
        f.add_block("start".to_string());
        let long = new_id(&["long"]);
        f.assign_instr(
            Value::Temporary(long.to_string()),
            qbe::Type::Long,
            Instr::Extub(Value::Temporary("a".to_string())),
        );
        f.add_instr(Instr::Ret(Some(Value::Temporary(long))));
        ctx.module.add_function(f);
    }

    {
        ctx.module.add_data(qbe::DataDef::new(
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

        ctx.module.add_function(print_str);
    }

    ctx.qbe_types_by_name
        .insert("I32".to_string(), qbe::Type::Word);
    ctx.qbe_types_by_name
        .insert("I64".to_string(), qbe::Type::Long);
    ctx.qbe_types_by_name
        .insert("String".to_string(), qbe::Type::Long);
}

fn type_to_qbe(ty: &ir::TypeDef) -> qbe::Type {
    match ty {
        ir::TypeDef::BuiltIn(BuiltInType::Int) => qbe::Type::Word,
        ir::TypeDef::BuiltIn(BuiltInType::I64)
        | ir::TypeDef::BuiltIn(BuiltInType::String)
        | ir::TypeDef::Struct(_) => qbe::Type::Long, // pointer to struct
    }
}

fn compile_type(ctx: &mut CodegenCtx, type_def: &ir::TypeDef) {
    trace!("Compiling type {:?}", type_def);

    match type_def {
        ir::TypeDef::BuiltIn(_) => {} // We generated those already
        ir::TypeDef::Struct(StructDef {
            struct_fields,
            name,
        }) => {
            let mut items = vec![];
            for field in struct_fields.iter() {
                let field_type = ctx.resolved.type_definitions.get(&field.ty).unwrap();
                let qbe_type = type_to_qbe(field_type);
                items.push((qbe_type, 1));
            }
            let typedef = qbe::TypeDef {
                name: name.to_string(),
                align: None,
                items,
            };

            let type_def = ctx.module.add_type(typedef.clone());
            ctx.qbe_types_by_name.insert(
                name.to_string(),
                qbe::Type::Aggregate(Arc::new(type_def.clone())),
            );
        }
    }
}

fn compile_statement(
    ctx: &mut CodegenCtx,
    qbe_func: &mut qbe::Function,
    statement: &parser::Statement,
    variables: &mut Variables,
) {
    match statement {
        parser::Statement::StructDef { def } => {
            let struct_type = ctx.resolved.type_definitions.get(&def.name).unwrap();
            if let ir::TypeDef::Struct(_s) = struct_type {
                compile_type(ctx, &struct_type.clone());
            }
        }
        parser::Statement::Conditional { condition, body } => {
            let start_label = new_id(&["cond", "start"]);
            let end_block_label = new_id(&["cond", "end"]);

            let condition_var = compile_expr(ctx, qbe_func, &condition, variables).0;

            qbe_func.add_instr(qbe::Instr::Jnz(
                qbe::Value::Temporary(condition_var),
                start_label.clone(),
                end_block_label.clone(),
            ));

            qbe_func.add_block(&start_label);
            for statement in body {
                compile_statement(ctx, qbe_func, statement, variables);
            }

            qbe_func.add_block(&end_block_label);
        }
        parser::Statement::While { condition, body } => {
            let condition_label = new_id(&["while", "cond"]);
            let start_label = new_id(&["while", "start"]);
            let end_block_label = new_id(&["while", "end"]);

            qbe_func.add_block(condition_label.clone());
            let condition_var = compile_expr(ctx, qbe_func, &condition, variables).0;

            qbe_func.add_instr(qbe::Instr::Jnz(
                qbe::Value::Temporary(condition_var),
                start_label.clone(),
                end_block_label.clone(),
            ));

            qbe_func.add_block(&start_label);
            for statement in body {
                compile_statement(ctx, qbe_func, statement, variables);
            }
            qbe_func.add_instr(qbe::Instr::Jmp(condition_label));

            qbe_func.add_block(&end_block_label);
        }
        parser::Statement::Return { expr } => {
            let expr_var = compile_expr(ctx, qbe_func, &expr, variables).0;
            trace!(%expr_var, "Emitting return instruction");
            qbe_func.add_instr(qbe::Instr::Ret(Some(qbe::Value::Temporary(expr_var))));
        }
        parser::Statement::Expression { expr } => {
            compile_expr(ctx, qbe_func, &expr, variables);
        }
        parser::Statement::Assign { variable, value } => {
            trace!(%variable, "Compiling assignment");

            let value_var = compile_expr(ctx, qbe_func, &value, variables);
            if let Some(existing_var) = variables.get(variable.as_str()) {
                qbe_func.assign_instr(
                    qbe::Value::Temporary(existing_var.0.clone()),
                    qbe::Type::Word, // FIXME: read from the hashmap instead of hardcoding word.
                    qbe::Instr::Copy(qbe::Value::Temporary(value_var.0.clone())),
                );
            }
            variables.insert(variable.clone(), value_var);
        }
    }
}

fn compile_function(ctx: &mut CodegenCtx, func_def: ir::FunctionDefinition) {
    let qbe_args = func_def
        .sig
        .parameters
        .iter()
        .map(|param| {
            let ty = ctx.qbe_types_by_name.get(&param.ty).unwrap().clone();
            (ty, qbe::Value::Temporary(param.name.clone()))
        })
        .collect::<Vec<_>>();

    let return_type_def = ctx
        .resolved
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
        compile_statement(ctx, &mut qbe_func, statement, &mut variables);
    }

    ctx.module.add_function(qbe_func);
}

pub fn compile(ir: ResolvedProgram) -> qbe::Module {
    let mut ctx = CodegenCtx {
        module: qbe::Module::default(),
        resolved: Arc::new(ir),
        qbe_types_by_name: HashMap::new(),
    };

    add_builtins(&mut ctx);

    for type_def in ctx.resolved.clone().type_definitions.values() {
        compile_type(&mut ctx, type_def);
    }

    for func_def in ctx.resolved.clone().function_definitions.values() {
        compile_function(&mut ctx, func_def.clone());
    }

    ctx.module
}

fn new_id(labels: &[&str]) -> String {
    format!(
        ".L_{}_{}",
        labels.join("_"),
        uuid::Uuid::now_v7().as_simple()
    )
}

fn type_offset(ctx: &CodegenCtx, ty: &str) -> u64 {
    match ctx.resolved.type_definitions.get(ty) {
        Some(ty) => match ty {
            ir::TypeDef::BuiltIn(BuiltInType::Int) => 4,
            ir::TypeDef::BuiltIn(BuiltInType::I64)
            | ir::TypeDef::BuiltIn(BuiltInType::String)
            | ir::TypeDef::Struct(_) => 8,
        },
        None => panic!("Unknown type {}", ty),
    }
}

fn calculate_struct_field_offset(
    ctx: &mut CodegenCtx,
    struct_def: &StructDef,
    field_name: &str,
) -> u64 {
    let mut offset = 0;
    for field in struct_def.struct_fields.iter() {
        if field.name == *field_name {
            return offset;
        }
        offset += type_offset(ctx, &field.ty);
    }

    panic!(
        "Field {} not found in struct {}",
        field_name, struct_def.name
    );
}

fn compile_expr(
    ctx: &mut CodegenCtx,
    func: &mut qbe::Function,
    expr: &parser::Expression,
    variables: &mut Variables,
) -> (QbeAssignName, ir::TypeRef) {
    trace!(?expr, "Compiling expression");

    match expr {
        parser::Expression::FieldAccess {
            struct_variable,
            field: field_name,
        } => {
            let (struct_pointer_var, struct_name) =
                variables.get(struct_variable.as_str()).unwrap();
            let resolved = ctx.resolved.clone();
            let typedef = resolved.type_definitions.get(struct_name).unwrap();
            let ir::TypeDef::Struct(structdef) = typedef else {
                panic!("Not really a struct: {struct_name}");
            };
            let field_offset = calculate_struct_field_offset(ctx, structdef, field_name);
            let field_type = if let ir::TypeDef::Struct(s) = typedef {
                s.struct_fields
                    .iter()
                    .find(|f| f.name == *field_name)
                    .unwrap()
                    .ty
                    .clone()
            } else {
                panic!("Expected struct type")
            };

            let id = new_id(&["field", "access"]);

            let struct_field_address_id = new_id(&["field", "address", &field_name]);
            func.assign_instr(
                Value::Temporary(struct_field_address_id.clone()),
                qbe::Type::Long,
                Instr::Add(
                    Value::Temporary(struct_pointer_var.clone()),
                    Value::Const(field_offset),
                ),
            );

            func.assign_instr(
                Value::Temporary(id.clone()),
                type_to_qbe(ctx.resolved.type_definitions.get(&field_type).unwrap()),
                Instr::Load(
                    type_to_qbe(ctx.resolved.type_definitions.get(&field_type).unwrap()),
                    Value::Temporary(struct_field_address_id),
                ),
            );

            (id, field_type)
        }
        parser::Expression::StructValue {
            struct_name,
            field_values,
        } => {
            let id = new_id(&["struct", struct_name]);
            let resolved = ctx.resolved.clone();
            let typedef = resolved.type_definitions.get(struct_name).unwrap();
            let ir::TypeDef::Struct(structdef) = typedef else {
                panic!("Not really a struct: {struct_name}");
            };

            func.assign_instr(
                Value::Temporary(id.clone()),
                qbe::Type::Long,
                Instr::Alloc8(8),
            );

            for (field_name, field_value) in field_values {
                let (field_var, _) = compile_expr(ctx, func, field_value, variables);
                let field = structdef
                    .struct_fields
                    .iter()
                    .find(|f| &f.name == field_name)
                    .unwrap();
                let field_type = ctx
                    .resolved
                    .type_definitions
                    .get(&field.ty)
                    .unwrap()
                    .clone();
                let field_offset = calculate_struct_field_offset(ctx, &structdef, &field.name);
                let field_dest_id = new_id(&["field", "offset", &field.name]);
                func.assign_instr(
                    Value::Temporary(field_dest_id.clone()),
                    qbe::Type::Long,
                    Instr::Add(Value::Temporary(id.clone()), Value::Const(field_offset)),
                );
                func.add_instr(Instr::Store(
                    type_to_qbe(&field_type),
                    Value::Temporary(field_dest_id),
                    Value::Temporary(field_var.clone()),
                ));
            }

            (id, struct_name.to_string())
        }
        parser::Expression::Literal(parser::Literal::Int(value)) => {
            let id = new_id(&["literal", "int"]);
            func.assign_instr(
                Value::Temporary(id.clone()),
                Type::Word,
                qbe::Instr::Copy(qbe::Value::Const(*value as u64)),
            );

            (id, "I32".to_string())
        }
        parser::Expression::Literal(parser::Literal::String(value)) => {
            let id = new_id(&["literal", "string"]);
            let const_name = new_id(&[]);
            ctx.module.add_data(qbe::DataDef::new(
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
            let id = new_id(&["call", name]);
            let mut arg_vars = vec![];
            for arg in args {
                let arg_var = compile_expr(ctx, func, arg, variables);
                arg_vars.push(arg_var);
            }

            let instr = qbe::Instr::Call(
                name.clone(),
                arg_vars
                    .iter()
                    .map(|v| {
                        let type_def = ctx.resolved.type_definitions.get(&v.1).unwrap();
                        let qbe_type = type_to_qbe(type_def);
                        (qbe_type, qbe::Value::Temporary(v.0.clone()))
                    })
                    .collect::<Vec<_>>(),
                None,
            );

            let sig = ctx.resolved.function_sigs.get(name).unwrap().clone();
            let return_type_def = ctx
                .resolved
                .type_definitions
                .get(&sig.return_type)
                .unwrap()
                .clone();
            let tmp_id_type = type_to_qbe(&return_type_def);

            func.assign_instr(Value::Temporary(id.clone()), tmp_id_type, instr);

            (id, sig.return_type.clone())
        }
        parser::Expression::BinOp(op, left, right) => {
            let id = new_id(&["bin_op"]);
            let left_var = compile_expr(ctx, func, left, variables).0;
            let right_var = compile_expr(ctx, func, right, variables).0;

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
