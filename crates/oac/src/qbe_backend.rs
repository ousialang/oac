use std::{collections::HashMap, sync::Arc, vec};

use qbe::*;
use tracing::trace;

use crate::{
    builtins::BuiltInType,
    ir::{self, ResolvedProgram},
    parser::{self, Op, StructDef, UnaryOp},
};

type QbeAssignName = String;
type Variables = HashMap<String, (QbeAssignName, ir::TypeRef)>;
pub(crate) const PROVE_MARKER_PREFIX: &str = ".oac_prove_site_";
const ASSERT_FAILURE_EXIT_CODE: u64 = 242;

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
                (qbe::Type::Byte, DataItem::Str("%u\n".to_string())),
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
        let mut f = Function::new(
            Linkage::public(),
            "char_at".to_string(),
            vec![
                (qbe::Type::Long, qbe::Value::Temporary("s".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("index".to_string())),
            ],
            Some(Type::Word),
        );
        f.add_block("start".to_string());

        let index_i64 = new_id(&["index", "i64"]);
        f.assign_instr(
            Value::Temporary(index_i64.clone()),
            qbe::Type::Long,
            Instr::Call(
                "i32_to_i64".to_string(),
                vec![(qbe::Type::Word, qbe::Value::Temporary("index".to_string()))],
                None,
            ),
        );

        let address = new_id(&["char", "address"]);
        f.assign_instr(
            Value::Temporary(address.clone()),
            qbe::Type::Long,
            Instr::Add(
                Value::Temporary("s".to_string()),
                Value::Temporary(index_i64),
            ),
        );

        let ch = new_id(&["char"]);
        f.assign_instr(
            Value::Temporary(ch.clone()),
            qbe::Type::Word,
            Instr::Load(Type::UnsignedByte, Value::Temporary(address)),
        );
        f.add_instr(Instr::Ret(Some(Value::Temporary(ch))));

        ctx.module.add_function(f);
    }

    {
        let mut f = Function::new(
            Linkage::private(),
            "i64_to_i32".to_string(),
            vec![(qbe::Type::Long, qbe::Value::Temporary("a".to_string()))],
            Some(Type::Word),
        );
        f.add_block("start".to_string());
        let word = new_id(&["word"]);
        f.assign_instr(
            Value::Temporary(word.clone()),
            qbe::Type::Word,
            Instr::Copy(Value::Temporary("a".to_string())),
        );
        f.add_instr(Instr::Ret(Some(Value::Temporary(word))));
        ctx.module.add_function(f);
    }

    {
        let mut f = Function::new(
            Linkage::public(),
            "string_len".to_string(),
            vec![(qbe::Type::Long, qbe::Value::Temporary("s".to_string()))],
            Some(Type::Word),
        );
        f.add_block("start".to_string());
        let len_i64 = new_id(&["len", "i64"]);
        f.assign_instr(
            Value::Temporary(len_i64.clone()),
            qbe::Type::Long,
            Instr::Call(
                "strlen".to_string(),
                vec![(qbe::Type::Long, qbe::Value::Temporary("s".to_string()))],
                None,
            ),
        );
        let len_i32 = new_id(&["len", "i32"]);
        f.assign_instr(
            Value::Temporary(len_i32.clone()),
            qbe::Type::Word,
            Instr::Call(
                "i64_to_i32".to_string(),
                vec![(qbe::Type::Long, qbe::Value::Temporary(len_i64))],
                None,
            ),
        );
        f.add_instr(Instr::Ret(Some(Value::Temporary(len_i32))));
        ctx.module.add_function(f);
    }

    {
        let mut f = Function::new(
            Linkage::public(),
            "slice".to_string(),
            vec![
                (qbe::Type::Long, qbe::Value::Temporary("s".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("start".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("len".to_string())),
            ],
            Some(Type::Long),
        );
        f.add_block("start".to_string());

        let len_plus_one = new_id(&["len", "plus", "one"]);
        f.assign_instr(
            Value::Temporary(len_plus_one.clone()),
            qbe::Type::Word,
            Instr::Add(Value::Temporary("len".to_string()), Value::Const(1)),
        );

        let alloc_size_i64 = new_id(&["alloc", "size", "i64"]);
        f.assign_instr(
            Value::Temporary(alloc_size_i64.clone()),
            qbe::Type::Long,
            Instr::Call(
                "i32_to_i64".to_string(),
                vec![(qbe::Type::Word, qbe::Value::Temporary(len_plus_one))],
                None,
            ),
        );

        let dst = new_id(&["slice", "dst"]);
        f.assign_instr(
            Value::Temporary(dst.clone()),
            qbe::Type::Long,
            Instr::Call(
                "malloc".to_string(),
                vec![(qbe::Type::Long, qbe::Value::Temporary(alloc_size_i64))],
                None,
            ),
        );

        let start_i64 = new_id(&["start", "i64"]);
        f.assign_instr(
            Value::Temporary(start_i64.clone()),
            qbe::Type::Long,
            Instr::Call(
                "i32_to_i64".to_string(),
                vec![(qbe::Type::Word, qbe::Value::Temporary("start".to_string()))],
                None,
            ),
        );
        let src = new_id(&["slice", "src"]);
        f.assign_instr(
            Value::Temporary(src.clone()),
            qbe::Type::Long,
            Instr::Add(
                Value::Temporary("s".to_string()),
                Value::Temporary(start_i64),
            ),
        );

        let copy_n_i64 = new_id(&["copy", "n", "i64"]);
        f.assign_instr(
            Value::Temporary(copy_n_i64.clone()),
            qbe::Type::Long,
            Instr::Call(
                "i32_to_i64".to_string(),
                vec![(qbe::Type::Word, qbe::Value::Temporary("len".to_string()))],
                None,
            ),
        );

        f.add_instr(Instr::Call(
            "memcpy".to_string(),
            vec![
                (qbe::Type::Long, qbe::Value::Temporary(dst.clone())),
                (qbe::Type::Long, qbe::Value::Temporary(src)),
                (qbe::Type::Long, qbe::Value::Temporary(copy_n_i64.clone())),
            ],
            None,
        ));

        let nul_addr = new_id(&["nul", "addr"]);
        f.assign_instr(
            Value::Temporary(nul_addr.clone()),
            qbe::Type::Long,
            Instr::Add(Value::Temporary(dst.clone()), Value::Temporary(copy_n_i64)),
        );
        f.add_instr(Instr::Store(
            Type::Byte,
            Value::Temporary(nul_addr),
            Value::Const(0),
        ));

        f.add_instr(Instr::Ret(Some(Value::Temporary(dst))));
        ctx.module.add_function(f);
    }

    {
        ctx.module.add_data(qbe::DataDef::new(
            Linkage::private(),
            "string_fmt".to_string(),
            None,
            vec![
                (qbe::Type::Byte, DataItem::Str("%s\n".to_string())),
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
        .insert("Int".to_string(), qbe::Type::Word);
    ctx.qbe_types_by_name
        .insert("Bool".to_string(), qbe::Type::Word);
    ctx.qbe_types_by_name
        .insert("I32".to_string(), qbe::Type::Word);
    ctx.qbe_types_by_name
        .insert("I64".to_string(), qbe::Type::Long);
    ctx.qbe_types_by_name
        .insert("String".to_string(), qbe::Type::Long);
}

fn type_to_qbe(ty: &ir::TypeDef) -> qbe::Type {
    match ty {
        ir::TypeDef::BuiltIn(BuiltInType::Bool) => qbe::Type::Word,
        ir::TypeDef::BuiltIn(BuiltInType::I32) => qbe::Type::Word,
        ir::TypeDef::BuiltIn(BuiltInType::I64)
        | ir::TypeDef::BuiltIn(BuiltInType::String)
        | ir::TypeDef::Struct(_) => qbe::Type::Long, // pointer to struct
        ir::TypeDef::Enum(enum_def) => {
            if enum_def.is_tagged_union {
                qbe::Type::Long
            } else {
                qbe::Type::Word
            }
        }
    }
}

fn compile_type(ctx: &mut CodegenCtx, type_def: &ir::TypeDef) {
    trace!("Compiling type {:?}", type_def);

    match type_def {
        ir::TypeDef::BuiltIn(_) => {} // We generated those already
        ir::TypeDef::Enum(enum_def) => {
            ctx.qbe_types_by_name.insert(
                enum_def.name.clone(),
                if enum_def.is_tagged_union {
                    qbe::Type::Long
                } else {
                    qbe::Type::Word
                },
            );
        }
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

fn is_word_sized_value_type(ctx: &CodegenCtx, type_name: &str) -> bool {
    match ctx.resolved.type_definitions.get(type_name) {
        Some(ir::TypeDef::BuiltIn(BuiltInType::Bool))
        | Some(ir::TypeDef::BuiltIn(BuiltInType::I32)) => true,
        Some(ir::TypeDef::Enum(enum_def)) => !enum_def.is_tagged_union,
        _ => false,
    }
}

fn compile_match_subject(
    ctx: &mut CodegenCtx,
    qbe_func: &mut qbe::Function,
    subject: &parser::Expression,
    variables: &mut Variables,
    label_root: &str,
) -> (QbeAssignName, ir::TypeRef, ir::EnumTypeDef, QbeAssignName) {
    let (subject_var, subject_ty) = compile_expr(ctx, qbe_func, subject, variables);
    let enum_def = match ctx.resolved.type_definitions.get(&subject_ty) {
        Some(ir::TypeDef::Enum(enum_def)) => enum_def.clone(),
        _ => panic!("match subject must be enum"),
    };

    let tag_var = if enum_def.is_tagged_union {
        let id = new_id(&[label_root, "tag"]);
        qbe_func.assign_instr(
            qbe::Value::Temporary(id.clone()),
            qbe::Type::Word,
            qbe::Instr::Load(qbe::Type::Word, qbe::Value::Temporary(subject_var.clone())),
        );
        id
    } else {
        subject_var.clone()
    };

    (subject_var, subject_ty, enum_def, tag_var)
}

fn resolve_match_pattern<'a>(
    enum_def: &'a ir::EnumTypeDef,
    subject_ty: &str,
    pattern: &parser::MatchPattern,
) -> (&'a ir::EnumVariant, Option<String>) {
    match pattern {
        parser::MatchPattern::Variant {
            type_name,
            variant_name,
            binder,
        } => {
            assert_eq!(type_name, subject_ty);
            let variant = enum_def
                .variants
                .iter()
                .find(|v| v.name == *variant_name)
                .unwrap();
            (variant, binder.clone())
        }
    }
}

fn bind_match_payload(
    ctx: &mut CodegenCtx,
    qbe_func: &mut qbe::Function,
    arm_variables: &mut Variables,
    subject_var: &str,
    variant: &ir::EnumVariant,
    binder: Option<String>,
    label_root: &str,
) {
    if let (Some(binder), Some(payload_ty)) = (binder, variant.payload_ty.clone()) {
        let payload_addr = new_id(&[label_root, "payload", "addr"]);
        qbe_func.assign_instr(
            qbe::Value::Temporary(payload_addr.clone()),
            qbe::Type::Long,
            qbe::Instr::Add(
                qbe::Value::Temporary(subject_var.to_string()),
                qbe::Value::Const(8),
            ),
        );
        let payload_raw = new_id(&[label_root, "payload", "raw"]);
        qbe_func.assign_instr(
            qbe::Value::Temporary(payload_raw.clone()),
            qbe::Type::Long,
            qbe::Instr::Load(qbe::Type::Long, qbe::Value::Temporary(payload_addr)),
        );

        let payload_var = if is_word_sized_value_type(ctx, &payload_ty) {
            let payload_word = new_id(&[label_root, "payload", "word"]);
            qbe_func.assign_instr(
                qbe::Value::Temporary(payload_word.clone()),
                qbe::Type::Word,
                qbe::Instr::Copy(qbe::Value::Temporary(payload_raw)),
            );
            payload_word
        } else {
            payload_raw
        };
        arm_variables.insert(binder, (payload_var, payload_ty));
    }
}

enum MatchArmOutcome {
    FallsThrough,
    Terminated,
}

fn lower_match_dispatch<Arm, PatternOf, CompileArm>(
    ctx: &mut CodegenCtx,
    qbe_func: &mut qbe::Function,
    variables: &Variables,
    subject_var: &str,
    subject_ty: &str,
    enum_def: &ir::EnumTypeDef,
    tag_var: &str,
    arms: &[Arm],
    pattern_of: PatternOf,
    label_root: &str,
    force_end_block: bool,
    mut compile_arm: CompileArm,
) -> String
where
    PatternOf: Fn(&Arm) -> &parser::MatchPattern,
    CompileArm: FnMut(&mut CodegenCtx, &mut qbe::Function, &mut Variables, &Arm) -> MatchArmOutcome,
{
    let end_label = new_id(&[label_root, "end"]);
    let mut any_arm_falls_through = false;

    for (i, arm) in arms.iter().enumerate() {
        let arm_label = new_id(&[label_root, "arm"]);
        let next_label = if i + 1 < arms.len() {
            Some(new_id(&[label_root, "next"]))
        } else {
            None
        };

        let (variant, binder) = resolve_match_pattern(enum_def, subject_ty, pattern_of(arm));

        let cmp_var = new_id(&[label_root, "cmp"]);
        qbe_func.assign_instr(
            qbe::Value::Temporary(cmp_var.clone()),
            qbe::Type::Word,
            qbe::Instr::Cmp(
                qbe::Type::Word,
                qbe::Cmp::Eq,
                qbe::Value::Temporary(tag_var.to_string()),
                qbe::Value::Const(variant.tag as u64),
            ),
        );
        qbe_func.add_instr(qbe::Instr::Jnz(
            qbe::Value::Temporary(cmp_var),
            arm_label.clone(),
            next_label.clone().unwrap_or_else(|| arm_label.clone()),
        ));

        qbe_func.add_block(arm_label);
        let mut arm_variables = variables.clone();
        bind_match_payload(
            ctx,
            qbe_func,
            &mut arm_variables,
            subject_var,
            variant,
            binder,
            label_root,
        );

        let outcome = compile_arm(ctx, qbe_func, &mut arm_variables, arm);
        if matches!(outcome, MatchArmOutcome::FallsThrough) {
            any_arm_falls_through = true;
            qbe_func.add_instr(qbe::Instr::Jmp(end_label.clone()));
        }

        if let Some(next_label) = next_label {
            qbe_func.add_block(next_label);
        }
    }

    if force_end_block || any_arm_falls_through {
        qbe_func.add_block(end_label.clone());
    }
    end_label
}

fn compile_statement(
    ctx: &mut CodegenCtx,
    qbe_func: &mut qbe::Function,
    statement: &parser::Statement,
    variables: &mut Variables,
    prove_site_counter: &mut usize,
) {
    match statement {
        parser::Statement::StructDef { def } => {
            let struct_type = ctx.resolved.type_definitions.get(&def.name).unwrap();
            if let ir::TypeDef::Struct(_s) = struct_type {
                compile_type(ctx, &struct_type.clone());
            }
        }
        parser::Statement::Match { subject, arms } => {
            let (subject_var, subject_ty, enum_def, tag_var) =
                compile_match_subject(ctx, qbe_func, subject, variables, "match");
            lower_match_dispatch(
                ctx,
                qbe_func,
                variables,
                &subject_var,
                &subject_ty,
                &enum_def,
                &tag_var,
                arms,
                |arm| &arm.pattern,
                "match",
                false,
                |ctx, qbe_func, arm_variables, arm| {
                    for statement in &arm.body {
                        compile_statement(
                            ctx,
                            qbe_func,
                            statement,
                            arm_variables,
                            prove_site_counter,
                        );
                    }
                    if qbe_func.blocks.last().unwrap().jumps() {
                        MatchArmOutcome::Terminated
                    } else {
                        MatchArmOutcome::FallsThrough
                    }
                },
            );
        }
        parser::Statement::Conditional {
            condition,
            body,
            else_body,
        } => {
            let then_label = new_id(&["cond", "then"]);
            let else_label = new_id(&["cond", "else"]);
            let end_block_label = new_id(&["cond", "end"]);

            let condition_var = compile_expr(ctx, qbe_func, &condition, variables).0;

            qbe_func.add_instr(qbe::Instr::Jnz(
                qbe::Value::Temporary(condition_var),
                then_label.clone(),
                if else_body.is_some() {
                    else_label.clone()
                } else {
                    end_block_label.clone()
                },
            ));

            qbe_func.add_block(&then_label);
            for statement in body {
                compile_statement(ctx, qbe_func, statement, variables, prove_site_counter);
            }
            let then_falls_through = !qbe_func.blocks.last().unwrap().jumps();
            if then_falls_through {
                qbe_func.add_instr(qbe::Instr::Jmp(end_block_label.clone()));
            }

            let mut else_falls_through = false;
            if let Some(else_body) = else_body {
                qbe_func.add_block(&else_label);
                for statement in else_body {
                    compile_statement(ctx, qbe_func, statement, variables, prove_site_counter);
                }
                else_falls_through = !qbe_func.blocks.last().unwrap().jumps();
                if else_falls_through {
                    qbe_func.add_instr(qbe::Instr::Jmp(end_block_label.clone()));
                }
            }

            let needs_end_block = else_body.is_none() || then_falls_through || else_falls_through;
            if needs_end_block {
                qbe_func.add_block(&end_block_label);
            }
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
                compile_statement(ctx, qbe_func, statement, variables, prove_site_counter);
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
        parser::Statement::Prove { condition } => {
            let condition_var = compile_expr(ctx, qbe_func, condition, variables).0;
            let marker_temp = format!("{PROVE_MARKER_PREFIX}{}", *prove_site_counter);
            *prove_site_counter += 1;
            qbe_func.assign_instr(
                qbe::Value::Temporary(marker_temp),
                qbe::Type::Word,
                qbe::Instr::Copy(qbe::Value::Temporary(condition_var)),
            );
        }
        parser::Statement::Assert { condition } => {
            let condition_var = compile_expr(ctx, qbe_func, condition, variables).0;
            let assert_pass_label = new_id(&["assert", "pass"]);
            let assert_fail_label = new_id(&["assert", "fail"]);

            qbe_func.add_instr(qbe::Instr::Jnz(
                qbe::Value::Temporary(condition_var),
                assert_pass_label.clone(),
                assert_fail_label.clone(),
            ));

            qbe_func.add_block(assert_fail_label);
            qbe_func.add_instr(qbe::Instr::Call(
                "exit".to_string(),
                vec![(qbe::Type::Word, qbe::Value::Const(ASSERT_FAILURE_EXIT_CODE))],
                None,
            ));
            qbe_func.add_instr(qbe::Instr::Hlt);

            qbe_func.add_block(assert_pass_label);
        }
        parser::Statement::Assign { variable, value } => {
            trace!(%variable, "Compiling assignment");

            let value_var = compile_expr(ctx, qbe_func, &value, variables);
            if let Some(existing_var) = variables.get(variable.as_str()) {
                let existing_type = ctx
                    .resolved
                    .type_definitions
                    .get(&existing_var.1)
                    .expect("existing variable type should exist");
                qbe_func.assign_instr(
                    qbe::Value::Temporary(existing_var.0.clone()),
                    type_to_qbe(existing_type),
                    qbe::Instr::Copy(qbe::Value::Temporary(value_var.0.clone())),
                );
            } else {
                variables.insert(variable.clone(), value_var);
            }
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
    let mut prove_site_counter = 0usize;
    for param in &func_def.sig.parameters {
        variables.insert(param.name.clone(), (param.name.clone(), param.ty.clone()));
    }

    for statement in &func_def.body {
        compile_statement(
            ctx,
            &mut qbe_func,
            statement,
            &mut variables,
            &mut prove_site_counter,
        );
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
            ir::TypeDef::BuiltIn(BuiltInType::Bool) => 4,
            ir::TypeDef::BuiltIn(BuiltInType::I32) => 4,
            ir::TypeDef::Enum(enum_def) => {
                if enum_def.is_tagged_union {
                    8
                } else {
                    4
                }
            }
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

fn struct_size_bytes(ctx: &CodegenCtx, struct_def: &StructDef) -> u64 {
    struct_def
        .struct_fields
        .iter()
        .map(|field| type_offset(ctx, &field.ty))
        .sum()
}

fn compile_named_call(
    ctx: &mut CodegenCtx,
    func: &mut qbe::Function,
    function_name: &str,
    args: &[parser::Expression],
    variables: &mut Variables,
) -> (QbeAssignName, ir::TypeRef) {
    let id = new_id(&["call", function_name]);
    let mut arg_vars = vec![];
    for arg in args {
        let arg_var = compile_expr(ctx, func, arg, variables);
        arg_vars.push(arg_var);
    }

    let instr = qbe::Instr::Call(
        function_name.to_string(),
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

    let sig = ctx
        .resolved
        .function_sigs
        .get(function_name)
        .unwrap()
        .clone();
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

fn compile_expr(
    ctx: &mut CodegenCtx,
    func: &mut qbe::Function,
    expr: &parser::Expression,
    variables: &mut Variables,
) -> (QbeAssignName, ir::TypeRef) {
    trace!(?expr, "Compiling expression");

    match expr {
        parser::Expression::Match { subject, arms } => {
            let var_types = variables
                .iter()
                .map(|(name, (_, ty))| (name.clone(), ty.clone()))
                .collect::<HashMap<_, _>>();
            let match_ty = ir::get_expression_type(
                expr,
                &var_types,
                &ctx.resolved.function_sigs,
                &ctx.resolved.type_definitions,
            )
            .unwrap_or_else(|err| {
                panic!("failed to type-check match expression in codegen: {err}")
            });
            let match_qbe_ty = type_to_qbe(
                ctx.resolved
                    .type_definitions
                    .get(&match_ty)
                    .expect("match expression type should exist"),
            );

            let result_slot = new_id(&["match", "expr", "slot"]);
            func.assign_instr(
                qbe::Value::Temporary(result_slot.clone()),
                qbe::Type::Long,
                qbe::Instr::Alloc8(8),
            );

            let (subject_var, subject_ty, enum_def, tag_var) =
                compile_match_subject(ctx, func, subject, variables, "match_expr");
            lower_match_dispatch(
                ctx,
                func,
                variables,
                &subject_var,
                &subject_ty,
                &enum_def,
                &tag_var,
                arms,
                |arm| &arm.pattern,
                "match_expr",
                true,
                |ctx, func, arm_variables, arm| {
                    let (arm_value, arm_value_ty) =
                        compile_expr(ctx, func, &arm.value, arm_variables);
                    assert_eq!(
                        arm_value_ty, match_ty,
                        "match expression arm type mismatch in codegen"
                    );
                    func.add_instr(qbe::Instr::Store(
                        match_qbe_ty.clone(),
                        qbe::Value::Temporary(result_slot.clone()),
                        qbe::Value::Temporary(arm_value),
                    ));
                    MatchArmOutcome::FallsThrough
                },
            );

            let result = new_id(&["match", "expr", "result"]);
            func.assign_instr(
                qbe::Value::Temporary(result.clone()),
                match_qbe_ty.clone(),
                qbe::Instr::Load(match_qbe_ty, qbe::Value::Temporary(result_slot)),
            );
            (result, match_ty)
        }
        parser::Expression::FieldAccess {
            struct_variable,
            field: field_name,
        } => {
            if let Some((struct_pointer_var, struct_name)) = variables.get(struct_variable.as_str())
            {
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
            } else {
                let enum_def = match ctx.resolved.type_definitions.get(struct_variable) {
                    Some(ir::TypeDef::Enum(enum_def)) => enum_def,
                    _ => panic!("Unknown variable/type {}", struct_variable),
                };
                let variant = enum_def
                    .variants
                    .iter()
                    .find(|v| v.name == *field_name)
                    .unwrap();
                assert!(
                    variant.payload_ty.is_none(),
                    "payload enum variant requires constructor call"
                );
                if enum_def.is_tagged_union {
                    let enum_ptr = new_id(&["enum", "alloc"]);
                    func.assign_instr(
                        qbe::Value::Temporary(enum_ptr.clone()),
                        qbe::Type::Long,
                        qbe::Instr::Call(
                            "malloc".to_string(),
                            vec![(qbe::Type::Long, qbe::Value::Const(16))],
                            None,
                        ),
                    );
                    func.add_instr(qbe::Instr::Store(
                        qbe::Type::Word,
                        qbe::Value::Temporary(enum_ptr.clone()),
                        qbe::Value::Const(variant.tag as u64),
                    ));
                    let payload_addr = new_id(&["enum", "payload", "addr"]);
                    func.assign_instr(
                        qbe::Value::Temporary(payload_addr.clone()),
                        qbe::Type::Long,
                        qbe::Instr::Add(
                            qbe::Value::Temporary(enum_ptr.clone()),
                            qbe::Value::Const(8),
                        ),
                    );
                    func.add_instr(qbe::Instr::Store(
                        qbe::Type::Long,
                        qbe::Value::Temporary(payload_addr),
                        qbe::Value::Const(0),
                    ));
                    (enum_ptr, enum_def.name.clone())
                } else {
                    let id = new_id(&["enum", "variant", struct_variable, field_name]);
                    func.assign_instr(
                        qbe::Value::Temporary(id.clone()),
                        qbe::Type::Word,
                        qbe::Instr::Copy(qbe::Value::Const(variant.tag as u64)),
                    );
                    (id, enum_def.name.clone())
                }
            }
        }
        parser::Expression::PostfixCall { callee, args } => match callee.as_ref() {
            parser::Expression::FieldAccess {
                struct_variable,
                field,
            } => {
                if let Some(ir::TypeDef::Enum(enum_def)) =
                    ctx.resolved.type_definitions.get(struct_variable)
                {
                    if let Some(variant) = enum_def.variants.iter().find(|v| v.name == *field) {
                        variant
                            .payload_ty
                            .as_ref()
                            .expect("tag-only enum variant is not callable");
                        let enum_name = enum_def.name.clone();
                        let variant_tag = variant.tag;

                        assert_eq!(
                            args.len(),
                            1,
                            "enum payload constructors currently support a single argument"
                        );
                        let (arg_var, arg_ty) = compile_expr(ctx, func, &args[0], variables);
                        let enum_ptr = new_id(&["enum", "alloc"]);
                        func.assign_instr(
                            qbe::Value::Temporary(enum_ptr.clone()),
                            qbe::Type::Long,
                            qbe::Instr::Call(
                                "malloc".to_string(),
                                vec![(qbe::Type::Long, qbe::Value::Const(16))],
                                None,
                            ),
                        );

                        func.add_instr(qbe::Instr::Store(
                            qbe::Type::Word,
                            qbe::Value::Temporary(enum_ptr.clone()),
                            qbe::Value::Const(variant_tag as u64),
                        ));

                        let payload_addr = new_id(&["enum", "payload", "addr"]);
                        func.assign_instr(
                            qbe::Value::Temporary(payload_addr.clone()),
                            qbe::Type::Long,
                            qbe::Instr::Add(
                                qbe::Value::Temporary(enum_ptr.clone()),
                                qbe::Value::Const(8),
                            ),
                        );
                        let payload_value = if is_word_sized_value_type(ctx, &arg_ty) {
                            let ext = new_id(&["enum", "payload", "ext"]);
                            func.assign_instr(
                                qbe::Value::Temporary(ext.clone()),
                                qbe::Type::Long,
                                qbe::Instr::Extsw(qbe::Value::Temporary(arg_var)),
                            );
                            qbe::Value::Temporary(ext)
                        } else {
                            qbe::Value::Temporary(arg_var)
                        };
                        func.add_instr(qbe::Instr::Store(
                            qbe::Type::Long,
                            qbe::Value::Temporary(payload_addr),
                            payload_value,
                        ));

                        return (enum_ptr, enum_name);
                    }
                }

                let namespaced_call =
                    parser::qualify_namespace_function_name(struct_variable, field);
                if ctx.resolved.function_sigs.contains_key(&namespaced_call) {
                    return compile_named_call(ctx, func, &namespaced_call, args, variables);
                }

                panic!("unsupported postfix call target")
            }
            _ => panic!("unsupported postfix call target"),
        },
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
                Instr::Call(
                    "malloc".to_string(),
                    vec![(
                        qbe::Type::Long,
                        qbe::Value::Const(struct_size_bytes(ctx, structdef)),
                    )],
                    None,
                ),
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
        parser::Expression::Literal(parser::Literal::Bool(value)) => {
            let id = new_id(&["literal", "bool"]);
            func.assign_instr(
                Value::Temporary(id.clone()),
                Type::Word,
                qbe::Instr::Copy(qbe::Value::Const(if *value { 1 } else { 0 })),
            );
            (id, "Bool".to_string())
        }
        parser::Expression::Variable(name) => {
            return variables.get(name).unwrap().clone();
        }
        parser::Expression::UnaryOp(op, expr) => {
            let id = new_id(&["unary_op"]);
            let (expr_var, _expr_ty) = compile_expr(ctx, func, expr, variables);

            match op {
                UnaryOp::Not => {
                    func.assign_instr(
                        qbe::Value::Temporary(id.clone()),
                        qbe::Type::Word,
                        qbe::Instr::Cmp(
                            qbe::Type::Word,
                            qbe::Cmp::Eq,
                            qbe::Value::Temporary(expr_var),
                            qbe::Value::Const(0),
                        ),
                    );
                }
            }

            (id, "Bool".to_string())
        }
        parser::Expression::Call(name, args) => {
            compile_named_call(ctx, func, name, args, variables)
        }
        parser::Expression::BinOp(op, left, right) => {
            let id = new_id(&["bin_op"]);
            let (left_var, left_ty) = compile_expr(ctx, func, left, variables);
            let (right_var, right_ty) = compile_expr(ctx, func, right, variables);
            let cmp_ty = if left_ty == "I64" || right_ty == "I64" {
                qbe::Type::Long
            } else {
                qbe::Type::Word
            };

            let instr = match op {
                Op::Eq => qbe::Instr::Cmp(
                    cmp_ty.clone(),
                    qbe::Cmp::Eq,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Neq => qbe::Instr::Cmp(
                    cmp_ty.clone(),
                    qbe::Cmp::Ne,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Lt => qbe::Instr::Cmp(
                    cmp_ty.clone(),
                    qbe::Cmp::Slt,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Gt => qbe::Instr::Cmp(
                    cmp_ty.clone(),
                    qbe::Cmp::Sgt,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Le => qbe::Instr::Cmp(
                    cmp_ty.clone(),
                    qbe::Cmp::Sle,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Ge => qbe::Instr::Cmp(
                    cmp_ty,
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
                Op::And => qbe::Instr::And(
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                Op::Or => qbe::Instr::Or(
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
            };

            func.assign_instr(qbe::Value::Temporary(id.clone()), qbe::Type::Word, instr);

            let out_ty = match op {
                Op::And | Op::Or => "Bool".to_string(),
                Op::Eq | Op::Neq | Op::Lt | Op::Gt | Op::Le | Op::Ge => "Bool".to_string(),
                Op::Add | Op::Sub | Op::Mul | Op::Div => left_ty,
            };

            (id, out_ty)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{compile, ir, parser::parse, tokenizer::tokenize, Build};
    use std::{
        fs,
        path::Path,
        process::{Command, Stdio},
        thread::sleep,
        time::{Duration, Instant},
    };

    use super::compile as compile_qbe;
    const EXECUTION_TIMEOUT: Duration = Duration::from_secs(5);

    fn run_executable_with_timeout(workdir: &Path) -> Result<String, String> {
        let mut child = Command::new("./target/oac/app")
            .current_dir(workdir)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|err| format!("failed to spawn executable: {err}"))?;

        let started = Instant::now();
        loop {
            match child.try_wait() {
                Ok(Some(_)) => {
                    let output = child
                        .wait_with_output()
                        .map_err(|err| format!("failed to collect executable output: {err}"))?;

                    if output.status.code().is_none() {
                        return Err(format!(
                            "executable terminated by signal\\nstdout:\\n{}\\nstderr:\\n{}",
                            String::from_utf8_lossy(&output.stdout),
                            String::from_utf8_lossy(&output.stderr)
                        ));
                    }

                    return String::from_utf8(output.stdout)
                        .map_err(|err| format!("executable stdout was not valid UTF-8: {err}"));
                }
                Ok(None) => {
                    if started.elapsed() > EXECUTION_TIMEOUT {
                        let _ = child.kill();
                        let _ = child.wait();
                        return Err(format!(
                            "execution timed out after {} seconds",
                            EXECUTION_TIMEOUT.as_secs()
                        ));
                    }
                    sleep(Duration::from_millis(25));
                }
                Err(err) => {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(format!("failed while waiting for executable: {err}"));
                }
            }
        }
    }

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
    fn qbe_codegen_supports_namespaced_function_calls() {
        let source = r#"
struct Option {
	value: I32,
}

namespace Option {
	fun is_some(v: Option) -> I32 {
		return v.value
	}
}

fun main() -> I32 {
	v = Option struct { value: 7 }
	return Option.is_some(v)
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let program = parse(tokens).expect("parse source");
        let ir = ir::resolve(program).expect("resolve source");
        let qbe_module = compile_qbe(ir);
        let qbe_ir = format!("{qbe_module}");
        assert!(
            qbe_ir.contains("call $Option__is_some"),
            "expected namespaced function call in qbe output, got:\n{qbe_ir}"
        );
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

            match run_executable_with_timeout(tmp.path()) {
                Ok(output) => insta::assert_snapshot!(path.display().to_string(), output),
                Err(err) => {
                    insta::assert_snapshot!(
                        path.display().to_string(),
                        format!("RUNTIME ERROR\n\n{err}")
                    );
                }
            }
        }
    }
}
