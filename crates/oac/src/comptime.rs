use std::collections::{HashMap, HashSet};

use crate::ir::SourceSpan;
use crate::parser::{
    self, Ast, Expression, Literal, Op, Statement, StructDef, StructField, TypeDefDecl, UnaryOp,
};

const MAX_WHILE_ITERATIONS: usize = 100_000;

#[derive(Clone, Debug, Default)]
struct DeclSetValue {
    type_definitions: Vec<TypeDefDecl>,
    top_level_functions: Vec<parser::Function>,
    invariants: Vec<parser::StructInvariantDecl>,
}

#[derive(Clone, Debug)]
struct StructInfoValue {
    name: String,
    fields: Vec<StructField>,
}

#[derive(Clone, Debug)]
struct FieldInfoValue {
    #[allow(dead_code)]
    owner_struct: String,
    #[allow(dead_code)]
    index: usize,
    name: String,
    ty: String,
}

#[derive(Clone, Debug)]
enum CtValue {
    Bool(bool),
    I32(i32),
    #[allow(dead_code)]
    I64(i64),
    String(String),
    Type(String),
    StructInfo(StructInfoValue),
    FieldInfo(FieldInfoValue),
    DeclSet(DeclSetValue),
    SemanticExpr(String),
    #[allow(dead_code)]
    SourceSpan(SourceSpan),
    Option {
        inner: Option<Box<CtValue>>,
        inner_type: String,
    },
}

#[derive(Clone, Debug)]
struct CtValueWithMeta {
    value: CtValue,
    provenance: Option<String>,
}

impl CtValueWithMeta {
    fn new(value: CtValue, provenance: Option<String>) -> Self {
        Self { value, provenance }
    }
}

#[derive(Clone, Debug, Default)]
struct TypeCatalog {
    all_types: HashSet<String>,
    structs: HashMap<String, StructDef>,
}

impl TypeCatalog {
    fn from_ast(ast: &Ast) -> anyhow::Result<Self> {
        let mut catalog = Self::default();
        for builtin in [
            "Int",
            "Bool",
            "U8",
            "I32",
            "I64",
            "FP32",
            "FP64",
            "Type",
            "DeclSet",
            "SemanticExpr",
            "SourceSpan",
            "StructInfo",
            "FieldInfo",
        ] {
            catalog.all_types.insert(builtin.to_string());
        }
        for type_def in &ast.type_definitions {
            catalog.insert_type_def(type_def)?;
        }
        Ok(catalog)
    }

    fn insert_type_def(&mut self, type_def: &TypeDefDecl) -> anyhow::Result<()> {
        match type_def {
            TypeDefDecl::Struct(def) => {
                if !self.all_types.insert(def.name.clone()) {
                    return Err(anyhow::anyhow!(
                        "duplicate type emitted by comptime evaluator: {}",
                        def.name
                    ));
                }
                self.structs.insert(def.name.clone(), def.clone());
            }
            TypeDefDecl::Enum(def) => {
                if !self.all_types.insert(def.name.clone()) {
                    return Err(anyhow::anyhow!(
                        "duplicate type emitted by comptime evaluator: {}",
                        def.name
                    ));
                }
            }
        }
        Ok(())
    }

    fn extend_from_declset(&mut self, declset: &DeclSetValue) -> anyhow::Result<()> {
        for type_def in &declset.type_definitions {
            self.insert_type_def(type_def)?;
        }
        Ok(())
    }
}

#[derive(Clone)]
struct EvalWorld {
    functions: HashMap<String, parser::Function>,
    type_catalog: TypeCatalog,
}

pub fn execute_comptime_applies(ast: &mut Ast) -> anyhow::Result<()> {
    if ast.comptime_applies.is_empty() {
        return Ok(());
    }

    let mut functions = HashMap::new();
    for function in &ast.top_level_functions {
        if function.is_comptime {
            if functions
                .insert(function.name.clone(), function.clone())
                .is_some()
            {
                return Err(anyhow::anyhow!(
                    "duplicate comptime function {}",
                    function.name
                ));
            }
        }
    }

    let mut world = EvalWorld {
        functions,
        type_catalog: TypeCatalog::from_ast(ast)?,
    };

    let mut call_stack = Vec::new();
    for apply in ast.comptime_applies.clone() {
        let function = world
            .functions
            .get(&apply.function_name)
            .ok_or_else(|| anyhow::anyhow!("unknown comptime function {}", apply.function_name))?
            .clone();
        if !function.is_comptime {
            return Err(anyhow::anyhow!(
                "comptime apply target {} must be declared with `comptime fun`",
                apply.function_name
            ));
        }
        if function.parameters.len() != 1 {
            return Err(anyhow::anyhow!(
                "comptime apply target {} must accept exactly one parameter",
                apply.function_name
            ));
        }
        if function.parameters[0].ty != "Type" {
            return Err(anyhow::anyhow!(
                "comptime apply target {} must accept a Type parameter, got {}",
                apply.function_name,
                function.parameters[0].ty
            ));
        }
        let result = evaluate_comptime_function(
            &function.name,
            vec![CtValueWithMeta::new(
                CtValue::Type(apply.argument_type.clone()),
                None,
            )],
            &mut world,
            &mut call_stack,
        )?;
        let CtValue::DeclSet(declset) = result.value else {
            return Err(anyhow::anyhow!(
                "comptime apply target {} must return DeclSet",
                function.name
            ));
        };
        world.type_catalog.extend_from_declset(&declset)?;
        merge_declset_into_ast(ast, declset)?;
    }

    Ok(())
}

fn merge_declset_into_ast(ast: &mut Ast, declset: DeclSetValue) -> anyhow::Result<()> {
    for type_def in declset.type_definitions {
        ast.type_definitions.push(type_def);
    }
    for function in declset.top_level_functions {
        if ast
            .top_level_functions
            .iter()
            .any(|existing| existing.name == function.name)
        {
            return Err(anyhow::anyhow!(
                "comptime emitted duplicate top-level function {}",
                function.name
            ));
        }
        ast.top_level_functions.push(function);
    }
    for invariant in declset.invariants {
        ast.invariants.push(invariant);
    }
    Ok(())
}

fn evaluate_comptime_function(
    function_name: &str,
    args: Vec<CtValueWithMeta>,
    world: &mut EvalWorld,
    call_stack: &mut Vec<String>,
) -> anyhow::Result<CtValueWithMeta> {
    if call_stack.iter().any(|name| name == function_name) {
        return Err(anyhow::anyhow!(
            "recursive comptime calls are unsupported in v1: {} -> {}",
            call_stack.join(" -> "),
            function_name
        ));
    }
    let function = world
        .functions
        .get(function_name)
        .ok_or_else(|| anyhow::anyhow!("unknown comptime function {}", function_name))?
        .clone();
    if !function.is_comptime {
        return Err(anyhow::anyhow!(
            "function {} is not a comptime function",
            function_name
        ));
    }
    if function.parameters.len() != args.len() {
        return Err(anyhow::anyhow!(
            "comptime function {} expects {} arguments, got {}",
            function_name,
            function.parameters.len(),
            args.len()
        ));
    }

    for (parameter, arg) in function.parameters.iter().zip(args.iter()) {
        if !ct_value_matches_type(&arg.value, &parameter.ty) {
            return Err(anyhow::anyhow!(
                "comptime function {} argument type mismatch for {}: expected {}, got {}",
                function_name,
                parameter.name,
                parameter.ty,
                ct_value_type_name(&arg.value)
            ));
        }
    }

    call_stack.push(function_name.to_string());
    let mut env = HashMap::new();
    for type_name in world.type_catalog.all_types.iter() {
        env.insert(
            type_name.clone(),
            CtValueWithMeta::new(CtValue::Type(type_name.clone()), None),
        );
    }
    for (parameter, arg) in function.parameters.iter().zip(args) {
        env.insert(parameter.name.clone(), arg);
    }

    for (statement_index, statement) in function.body.iter().enumerate() {
        let path = format!("comptime_fn:{function_name}/stmt:{statement_index}");
        if let Some(ret) = evaluate_statement(statement, &path, &mut env, world, call_stack)? {
            if !ct_value_matches_type(&ret.value, &function.return_type) {
                return Err(anyhow::anyhow!(
                    "comptime function {} must return {}, got {}",
                    function_name,
                    function.return_type,
                    ct_value_type_name(&ret.value)
                ));
            }
            call_stack.pop();
            return Ok(ret);
        }
    }

    call_stack.pop();
    Err(anyhow::anyhow!(
        "comptime function {} must return a value",
        function_name
    ))
}

fn evaluate_statement(
    statement: &Statement,
    path: &str,
    env: &mut HashMap<String, CtValueWithMeta>,
    world: &mut EvalWorld,
    call_stack: &mut Vec<String>,
) -> anyhow::Result<Option<CtValueWithMeta>> {
    match statement {
        Statement::StructDef { .. } => Err(anyhow::anyhow!(
            "local struct declarations are unsupported in comptime function bodies"
        )),
        Statement::Match { .. } => Err(anyhow::anyhow!(
            "match statements are unsupported in comptime evaluator v1"
        )),
        Statement::Conditional {
            condition,
            body,
            else_body,
        } => {
            let cond = evaluate_expression(
                condition,
                &format!("{path}/if.cond"),
                env,
                world,
                call_stack,
            )?;
            let cond_bool = expect_bool(&cond.value, "if condition")?;
            if cond_bool {
                for (index, statement) in body.iter().enumerate() {
                    if let Some(ret) = evaluate_statement(
                        statement,
                        &format!("{path}/if.body.{index}"),
                        env,
                        world,
                        call_stack,
                    )? {
                        return Ok(Some(ret));
                    }
                }
            } else if let Some(else_body) = else_body {
                for (index, statement) in else_body.iter().enumerate() {
                    if let Some(ret) = evaluate_statement(
                        statement,
                        &format!("{path}/if.else.{index}"),
                        env,
                        world,
                        call_stack,
                    )? {
                        return Ok(Some(ret));
                    }
                }
            }
            Ok(None)
        }
        Statement::Assign { variable, value } => {
            let evaluated = evaluate_expression(
                value,
                &format!("{path}/assign.value"),
                env,
                world,
                call_stack,
            )?;
            env.insert(variable.clone(), evaluated);
            Ok(None)
        }
        Statement::Return { expr } => {
            let evaluated =
                evaluate_expression(expr, &format!("{path}/return"), env, world, call_stack)?;
            Ok(Some(evaluated))
        }
        Statement::Expression { expr } => {
            evaluate_expression(expr, &format!("{path}/expr"), env, world, call_stack)?;
            Ok(None)
        }
        Statement::Prove { condition } => {
            let evaluated = evaluate_expression(
                condition,
                &format!("{path}/prove.cond"),
                env,
                world,
                call_stack,
            )?;
            if !expect_bool(&evaluated.value, "prove condition")? {
                return Err(anyhow::anyhow!(
                    "prove condition evaluated to false in comptime function"
                ));
            }
            Ok(None)
        }
        Statement::Assert { condition } => {
            let evaluated = evaluate_expression(
                condition,
                &format!("{path}/assert.cond"),
                env,
                world,
                call_stack,
            )?;
            if !expect_bool(&evaluated.value, "assert condition")? {
                return Err(anyhow::anyhow!(
                    "assert condition evaluated to false in comptime function"
                ));
            }
            Ok(None)
        }
        Statement::While { condition, body } => {
            let mut iteration_count = 0usize;
            loop {
                iteration_count += 1;
                if iteration_count > MAX_WHILE_ITERATIONS {
                    return Err(anyhow::anyhow!(
                        "comptime while loop exceeded iteration limit ({})",
                        MAX_WHILE_ITERATIONS
                    ));
                }
                let cond = evaluate_expression(
                    condition,
                    &format!("{path}/while.cond"),
                    env,
                    world,
                    call_stack,
                )?;
                let cond_bool = expect_bool(&cond.value, "while condition")?;
                if !cond_bool {
                    break;
                }
                for (statement_index, statement) in body.iter().enumerate() {
                    if let Some(ret) = evaluate_statement(
                        statement,
                        &format!("{path}/while.body.{statement_index}"),
                        env,
                        world,
                        call_stack,
                    )? {
                        return Ok(Some(ret));
                    }
                }
            }
            Ok(None)
        }
    }
}

fn evaluate_expression(
    expression: &Expression,
    path: &str,
    env: &mut HashMap<String, CtValueWithMeta>,
    world: &mut EvalWorld,
    call_stack: &mut Vec<String>,
) -> anyhow::Result<CtValueWithMeta> {
    match expression {
        Expression::Match { .. } => Err(anyhow::anyhow!(
            "match expressions are unsupported in comptime evaluator v1"
        )),
        Expression::Literal(Literal::Int(n)) => {
            let value = i32::try_from(*n)
                .map_err(|_| anyhow::anyhow!("integer literal {} is out of i32 range", n))?;
            Ok(CtValueWithMeta::new(
                CtValue::I32(value),
                Some(path.to_string()),
            ))
        }
        Expression::Literal(Literal::Float32(value)) => Err(anyhow::anyhow!(
            "FP32 literal {} is unsupported in comptime evaluator",
            value
        )),
        Expression::Literal(Literal::Float64(value)) => Err(anyhow::anyhow!(
            "FP64 literal {} is unsupported in comptime evaluator",
            value
        )),
        Expression::Literal(Literal::String(s)) => Ok(CtValueWithMeta::new(
            CtValue::String(s.clone()),
            Some(path.to_string()),
        )),
        Expression::Literal(Literal::Bool(b)) => Ok(CtValueWithMeta::new(
            CtValue::Bool(*b),
            Some(path.to_string()),
        )),
        Expression::Variable(name) => env
            .get(name)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("unknown variable {} in comptime evaluator", name)),
        Expression::Call(name, args) => {
            let evaluated_args = args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    evaluate_expression(
                        arg,
                        &format!("{path}/call.arg.{index}"),
                        env,
                        world,
                        call_stack,
                    )
                })
                .collect::<anyhow::Result<Vec<_>>>()?;
            evaluate_call(name, evaluated_args, path, world, call_stack)
        }
        Expression::PostfixCall { .. } => Err(anyhow::anyhow!(
            "postfix calls are unsupported in comptime evaluator v1"
        )),
        Expression::BinOp(op, left, right) => {
            let left =
                evaluate_expression(left, &format!("{path}/bin.left"), env, world, call_stack)?;
            let right =
                evaluate_expression(right, &format!("{path}/bin.right"), env, world, call_stack)?;
            let value = evaluate_binary_op(*op, &left.value, &right.value)?;
            Ok(CtValueWithMeta::new(value, Some(path.to_string())))
        }
        Expression::UnaryOp(op, expr) => {
            let inner =
                evaluate_expression(expr, &format!("{path}/unary"), env, world, call_stack)?;
            match op {
                UnaryOp::Not => Ok(CtValueWithMeta::new(
                    CtValue::Bool(!expect_bool(&inner.value, "unary ! operand")?),
                    Some(path.to_string()),
                )),
            }
        }
        Expression::FieldAccess { .. } => Err(anyhow::anyhow!(
            "field access is unsupported in comptime evaluator v1"
        )),
        Expression::StructValue { .. } => Err(anyhow::anyhow!(
            "struct literals are unsupported in comptime evaluator v1"
        )),
    }
}

fn evaluate_binary_op(op: Op, left: &CtValue, right: &CtValue) -> anyhow::Result<CtValue> {
    match op {
        Op::And => Ok(CtValue::Bool(
            expect_bool(left, "&& left operand")? && expect_bool(right, "&& right operand")?,
        )),
        Op::Or => Ok(CtValue::Bool(
            expect_bool(left, "|| left operand")? || expect_bool(right, "|| right operand")?,
        )),
        Op::Add => Ok(CtValue::I32(
            expect_i32(left, "+ left operand")? + expect_i32(right, "+ right operand")?,
        )),
        Op::Sub => Ok(CtValue::I32(
            expect_i32(left, "- left operand")? - expect_i32(right, "- right operand")?,
        )),
        Op::Mul => Ok(CtValue::I32(
            expect_i32(left, "* left operand")? * expect_i32(right, "* right operand")?,
        )),
        Op::Div => Ok(CtValue::I32(
            expect_i32(left, "/ left operand")? / expect_i32(right, "/ right operand")?,
        )),
        Op::Eq => Ok(CtValue::Bool(values_equal(left, right)?)),
        Op::Neq => Ok(CtValue::Bool(!values_equal(left, right)?)),
        Op::Lt => Ok(CtValue::Bool(
            expect_i32(left, "< left operand")? < expect_i32(right, "< right operand")?,
        )),
        Op::Gt => Ok(CtValue::Bool(
            expect_i32(left, "> left operand")? > expect_i32(right, "> right operand")?,
        )),
        Op::Le => Ok(CtValue::Bool(
            expect_i32(left, "<= left operand")? <= expect_i32(right, "<= right operand")?,
        )),
        Op::Ge => Ok(CtValue::Bool(
            expect_i32(left, ">= left operand")? >= expect_i32(right, ">= right operand")?,
        )),
    }
}

fn evaluate_call(
    name: &str,
    args: Vec<CtValueWithMeta>,
    path: &str,
    world: &mut EvalWorld,
    call_stack: &mut Vec<String>,
) -> anyhow::Result<CtValueWithMeta> {
    let as_value = |value| CtValueWithMeta::new(value, Some(path.to_string()));
    let as_option = |inner: Option<CtValue>, inner_type: &str| {
        CtValueWithMeta::new(
            CtValue::Option {
                inner: inner.map(Box::new),
                inner_type: inner_type.to_string(),
            },
            Some(path.to_string()),
        )
    };

    match name {
        "expr_meta_opt" => {
            ensure_arity(name, &args, 1)?;
            if let Some(meta) = args[0].provenance.clone() {
                Ok(as_option(Some(CtValue::SemanticExpr(meta)), "SemanticExpr"))
            } else {
                Ok(as_option(None, "SemanticExpr"))
            }
        }
        "definition_location_opt" => {
            ensure_arity(name, &args, 1)?;
            if args[0].provenance.is_some() {
                Ok(as_option(
                    Some(CtValue::SourceSpan(SourceSpan {
                        file: None,
                        start_line: None,
                        start_column: None,
                        end_line: None,
                        end_column: None,
                    })),
                    "SourceSpan",
                ))
            } else {
                Ok(as_option(None, "SourceSpan"))
            }
        }
        "concat" => {
            ensure_arity(name, &args, 2)?;
            Ok(as_value(CtValue::String(format!(
                "{}{}",
                expect_string(&args[0].value, "concat left argument")?,
                expect_string(&args[1].value, "concat right argument")?
            ))))
        }
        "is_some" => {
            ensure_arity(name, &args, 1)?;
            let CtValue::Option { inner, .. } = &args[0].value else {
                return Err(anyhow::anyhow!(
                    "is_some expects Option[T], got {}",
                    ct_value_type_name(&args[0].value)
                ));
            };
            Ok(as_value(CtValue::Bool(inner.is_some())))
        }
        "unwrap" => {
            ensure_arity(name, &args, 1)?;
            let CtValue::Option { inner, inner_type } = &args[0].value else {
                return Err(anyhow::anyhow!(
                    "unwrap expects Option[T], got {}",
                    ct_value_type_name(&args[0].value)
                ));
            };
            let Some(inner) = inner.clone() else {
                return Err(anyhow::anyhow!(
                    "unwrap called on None for Option[{}]",
                    inner_type
                ));
            };
            Ok(CtValueWithMeta::new(*inner, Some(path.to_string())))
        }
        "resolve_type" => {
            ensure_arity(name, &args, 1)?;
            Ok(as_value(CtValue::Type(
                expect_string(&args[0].value, "resolve_type argument")?.to_string(),
            )))
        }
        "type_name" => {
            ensure_arity(name, &args, 1)?;
            Ok(as_value(CtValue::String(
                expect_type_name(&args[0].value, "type_name argument")?.to_string(),
            )))
        }
        "is_struct" => {
            ensure_arity(name, &args, 1)?;
            let type_name = expect_type_name(&args[0].value, "is_struct argument")?;
            Ok(as_value(CtValue::Bool(
                world.type_catalog.structs.contains_key(type_name),
            )))
        }
        "as_struct_opt" => {
            ensure_arity(name, &args, 1)?;
            let type_name = expect_type_name(&args[0].value, "as_struct_opt argument")?;
            if let Some(struct_def) = world.type_catalog.structs.get(type_name) {
                Ok(as_option(
                    Some(CtValue::StructInfo(StructInfoValue {
                        name: struct_def.name.clone(),
                        fields: struct_def.struct_fields.clone(),
                    })),
                    "StructInfo",
                ))
            } else {
                Ok(as_option(None, "StructInfo"))
            }
        }
        "struct_field_count" => {
            ensure_arity(name, &args, 1)?;
            let struct_info = expect_struct_info(&args[0].value, "struct_field_count argument")?;
            Ok(as_value(CtValue::I32(struct_info.fields.len() as i32)))
        }
        "struct_field_at" => {
            ensure_arity(name, &args, 2)?;
            let struct_info = expect_struct_info(&args[0].value, "struct_field_at first argument")?;
            let index = expect_i32(&args[1].value, "struct_field_at second argument")?;
            if index < 0 || index as usize >= struct_info.fields.len() {
                return Ok(as_option(None, "FieldInfo"));
            }
            let field = &struct_info.fields[index as usize];
            Ok(as_option(
                Some(CtValue::FieldInfo(FieldInfoValue {
                    owner_struct: struct_info.name.clone(),
                    index: index as usize,
                    name: field.name.clone(),
                    ty: field.ty.clone(),
                })),
                "FieldInfo",
            ))
        }
        "field_name" => {
            ensure_arity(name, &args, 1)?;
            let field_info = expect_field_info(&args[0].value, "field_name argument")?;
            Ok(as_value(CtValue::String(field_info.name.clone())))
        }
        "field_type" => {
            ensure_arity(name, &args, 1)?;
            let field_info = expect_field_info(&args[0].value, "field_type argument")?;
            Ok(as_value(CtValue::Type(field_info.ty.clone())))
        }
        "declset_new" => {
            ensure_arity(name, &args, 0)?;
            Ok(as_value(CtValue::DeclSet(DeclSetValue::default())))
        }
        "declset_add_derived_struct" => {
            ensure_arity(name, &args, 3)?;
            let mut declset =
                expect_declset(&args[0].value, "declset_add_derived_struct first argument")?
                    .clone();
            let base =
                expect_struct_info(&args[1].value, "declset_add_derived_struct second argument")?;
            let new_name =
                expect_string(&args[2].value, "declset_add_derived_struct third argument")?
                    .to_string();
            if world.type_catalog.all_types.contains(&new_name)
                || declset.type_definitions.iter().any(|def| match def {
                    TypeDefDecl::Struct(def) => def.name == new_name,
                    TypeDefDecl::Enum(def) => def.name == new_name,
                })
            {
                return Err(anyhow::anyhow!(
                    "declset_add_derived_struct cannot emit duplicate type {}",
                    new_name
                ));
            }
            declset
                .type_definitions
                .push(TypeDefDecl::Struct(StructDef {
                    name: new_name,
                    struct_fields: base.fields.clone(),
                }));
            Ok(as_value(CtValue::DeclSet(declset)))
        }
        "declset_add_invariant_field_gt_i32" => {
            ensure_arity(name, &args, 5)?;
            let mut declset = expect_declset(
                &args[0].value,
                "declset_add_invariant_field_gt_i32 first argument",
            )?
            .clone();
            let target_type = expect_type_name(
                &args[1].value,
                "declset_add_invariant_field_gt_i32 second argument",
            )?;
            let display_name = expect_string(
                &args[2].value,
                "declset_add_invariant_field_gt_i32 third argument",
            )?
            .to_string();
            let field_name = expect_string(
                &args[3].value,
                "declset_add_invariant_field_gt_i32 fourth argument",
            )?
            .to_string();
            let min_exclusive = expect_i32(
                &args[4].value,
                "declset_add_invariant_field_gt_i32 fifth argument",
            )?;

            let struct_def = find_struct_for_type(target_type, &declset, &world.type_catalog)
                .ok_or_else(|| {
                    anyhow::anyhow!(
                        "declset_add_invariant_field_gt_i32 target {} is not a known struct",
                        target_type
                    )
                })?;
            let field = struct_def
                .struct_fields
                .iter()
                .find(|field| field.name == field_name)
                .ok_or_else(|| {
                    anyhow::anyhow!(
                        "declset_add_invariant_field_gt_i32 target {} has no field named {}",
                        target_type,
                        field_name
                    )
                })?;
            if field.ty != "I32" {
                return Err(anyhow::anyhow!(
                    "declset_add_invariant_field_gt_i32 requires I32 field, got {}.{}: {}",
                    target_type,
                    field_name,
                    field.ty
                ));
            }
            let literal = u32::try_from(min_exclusive).map_err(|_| {
                anyhow::anyhow!(
                    "declset_add_invariant_field_gt_i32 only supports non-negative lower bounds in v1"
                )
            })?;

            declset.invariants.push(parser::StructInvariantDecl {
                identifier: None,
                display_name,
                parameter: parser::Parameter {
                    name: "v".to_string(),
                    ty: target_type.to_string(),
                },
                body: vec![Statement::Return {
                    expr: Expression::BinOp(
                        Op::Gt,
                        Box::new(Expression::FieldAccess {
                            struct_variable: "v".to_string(),
                            field: field_name,
                        }),
                        Box::new(Expression::Literal(Literal::Int(literal))),
                    ),
                }],
            });

            Ok(as_value(CtValue::DeclSet(declset)))
        }
        _ => {
            if world.functions.contains_key(name) {
                let result = evaluate_comptime_function(name, args, world, call_stack)?;
                Ok(CtValueWithMeta::new(result.value, Some(path.to_string())))
            } else {
                Err(anyhow::anyhow!(
                    "unsupported function call {} in comptime evaluator (v1 is deterministic and pure)",
                    name
                ))
            }
        }
    }
}

fn find_struct_for_type<'a>(
    target_type: &str,
    declset: &'a DeclSetValue,
    catalog: &'a TypeCatalog,
) -> Option<&'a StructDef> {
    for type_def in declset.type_definitions.iter().rev() {
        if let TypeDefDecl::Struct(def) = type_def {
            if def.name == target_type {
                return Some(def);
            }
        }
    }
    catalog.structs.get(target_type)
}

fn ensure_arity(name: &str, args: &[CtValueWithMeta], expected: usize) -> anyhow::Result<()> {
    if args.len() != expected {
        return Err(anyhow::anyhow!(
            "{} expects {} arguments, got {}",
            name,
            expected,
            args.len()
        ));
    }
    Ok(())
}

fn expect_bool<'a>(value: &'a CtValue, context: &str) -> anyhow::Result<bool> {
    if let CtValue::Bool(value) = value {
        Ok(*value)
    } else {
        Err(anyhow::anyhow!(
            "{} expected Bool, got {}",
            context,
            ct_value_type_name(value)
        ))
    }
}

fn expect_i32<'a>(value: &'a CtValue, context: &str) -> anyhow::Result<i32> {
    if let CtValue::I32(value) = value {
        Ok(*value)
    } else {
        Err(anyhow::anyhow!(
            "{} expected I32, got {}",
            context,
            ct_value_type_name(value)
        ))
    }
}

fn expect_string<'a>(value: &'a CtValue, context: &str) -> anyhow::Result<&'a str> {
    if let CtValue::String(value) = value {
        Ok(value)
    } else {
        Err(anyhow::anyhow!(
            "{} expected String, got {}",
            context,
            ct_value_type_name(value)
        ))
    }
}

fn expect_type_name<'a>(value: &'a CtValue, context: &str) -> anyhow::Result<&'a str> {
    if let CtValue::Type(value) = value {
        Ok(value)
    } else {
        Err(anyhow::anyhow!(
            "{} expected Type, got {}",
            context,
            ct_value_type_name(value)
        ))
    }
}

fn expect_struct_info<'a>(
    value: &'a CtValue,
    context: &str,
) -> anyhow::Result<&'a StructInfoValue> {
    if let CtValue::StructInfo(value) = value {
        Ok(value)
    } else {
        Err(anyhow::anyhow!(
            "{} expected StructInfo, got {}",
            context,
            ct_value_type_name(value)
        ))
    }
}

fn expect_field_info<'a>(value: &'a CtValue, context: &str) -> anyhow::Result<&'a FieldInfoValue> {
    if let CtValue::FieldInfo(value) = value {
        Ok(value)
    } else {
        Err(anyhow::anyhow!(
            "{} expected FieldInfo, got {}",
            context,
            ct_value_type_name(value)
        ))
    }
}

fn expect_declset<'a>(value: &'a CtValue, context: &str) -> anyhow::Result<&'a DeclSetValue> {
    if let CtValue::DeclSet(value) = value {
        Ok(value)
    } else {
        Err(anyhow::anyhow!(
            "{} expected DeclSet, got {}",
            context,
            ct_value_type_name(value)
        ))
    }
}

fn values_equal(left: &CtValue, right: &CtValue) -> anyhow::Result<bool> {
    match (left, right) {
        (CtValue::Bool(a), CtValue::Bool(b)) => Ok(a == b),
        (CtValue::I32(a), CtValue::I32(b)) => Ok(a == b),
        (CtValue::I64(a), CtValue::I64(b)) => Ok(a == b),
        (CtValue::String(a), CtValue::String(b)) => Ok(a == b),
        (CtValue::Type(a), CtValue::Type(b)) => Ok(a == b),
        (CtValue::SemanticExpr(a), CtValue::SemanticExpr(b)) => Ok(a == b),
        _ => Err(anyhow::anyhow!(
            "unsupported equality comparison between {} and {}",
            ct_value_type_name(left),
            ct_value_type_name(right)
        )),
    }
}

fn ct_value_type_name(value: &CtValue) -> String {
    match value {
        CtValue::Bool(_) => "Bool".to_string(),
        CtValue::I32(_) => "I32".to_string(),
        CtValue::I64(_) => "I64".to_string(),
        CtValue::String(_) => "String".to_string(),
        CtValue::Type(_) => "Type".to_string(),
        CtValue::StructInfo(_) => "StructInfo".to_string(),
        CtValue::FieldInfo(_) => "FieldInfo".to_string(),
        CtValue::DeclSet(_) => "DeclSet".to_string(),
        CtValue::SemanticExpr(_) => "SemanticExpr".to_string(),
        CtValue::SourceSpan(_) => "SourceSpan".to_string(),
        CtValue::Option { inner_type, .. } => format!("Option[{inner_type}]"),
    }
}

fn ct_value_matches_type(value: &CtValue, ty: &str) -> bool {
    match value {
        CtValue::Option { inner_type, .. } => ty == format!("Option[{inner_type}]"),
        _ => ct_value_type_name(value) == ty,
    }
}

#[cfg(test)]
mod tests {
    use crate::{parser, tokenizer};

    use super::execute_comptime_applies;

    fn parse_source(source: &str) -> parser::Ast {
        let tokens = tokenizer::tokenize(source.to_string()).expect("tokenize source");
        parser::parse(tokens).expect("parse source")
    }

    #[test]
    fn no_applies_is_noop() {
        let mut ast = parse_source(
            r#"
struct Counter {
	value: I32,
}

fun main() -> I32 {
	return 0
}
"#,
        );
        execute_comptime_applies(&mut ast).expect("execute comptime applies");
        assert_eq!(ast.type_definitions.len(), 1);
        assert!(ast.comptime_applies.is_empty());
    }

    #[test]
    fn apply_emits_derived_struct_and_invariant() {
        let mut ast = parse_source(
            r#"
struct Counter {
	label: String,
	value: I32,
}

comptime fun make_positive_second(T: Type) -> DeclSet {
	ds = declset_new()
	s = as_struct_opt(T)
	if is_some(s) {
		info = unwrap(s)
		if struct_field_count(info) >= 2 {
			f = struct_field_at(info, 1)
			if is_some(f) {
				second = unwrap(f)
				if field_type(second) == I32 {
					new_name = concat(type_name(T), "PositiveSecond")
					ds2 = declset_add_derived_struct(ds, info, new_name)
					return declset_add_invariant_field_gt_i32(
						ds2,
						resolve_type(new_name),
						"second field must be > 0",
						field_name(second),
						0
					)
				}
			}
		}
	}
	return ds
}

comptime apply make_positive_second(Counter)
"#,
        );

        execute_comptime_applies(&mut ast).expect("execute comptime applies");
        assert!(ast.type_definitions.iter().any(|def| {
            matches!(
                def,
                parser::TypeDefDecl::Struct(def) if def.name == "CounterPositiveSecond"
            )
        }));
        assert!(ast
            .invariants
            .iter()
            .any(|inv| inv.parameter.ty == "CounterPositiveSecond"));
    }

    #[test]
    fn apply_order_is_deterministic() {
        let mut ast = parse_source(
            r#"
struct Counter {
	value: I32,
}

comptime fun derive(T: Type) -> DeclSet {
	ds = declset_new()
	s = as_struct_opt(T)
	if is_some(s) {
		info = unwrap(s)
		return declset_add_derived_struct(ds, info, concat(type_name(T), "X"))
	}
	return ds
}

comptime apply derive(Counter)
comptime apply derive(CounterX)
"#,
        );
        execute_comptime_applies(&mut ast).expect("execute comptime applies");
        assert!(ast.type_definitions.iter().any(|def| {
            matches!(def, parser::TypeDefDecl::Struct(def) if def.name == "CounterX")
        }));
        assert!(ast.type_definitions.iter().any(|def| {
            matches!(def, parser::TypeDefDecl::Struct(def) if def.name == "CounterXX")
        }));
    }

    #[test]
    fn provenance_some_none_behavior() {
        let mut ast = parse_source(
            r#"
struct Counter {
	value: I32,
}

comptime fun meta_probe(T: Type) -> DeclSet {
	meta_from_param = expr_meta_opt(T)
	meta_from_expr = expr_meta_opt(resolve_type("I32"))
	assert(!is_some(meta_from_param))
	assert(is_some(meta_from_expr))
	return declset_new()
}

comptime apply meta_probe(Counter)
"#,
        );
        execute_comptime_applies(&mut ast).expect("execute comptime applies");
    }

    #[test]
    fn bad_emit_fails_closed() {
        let mut ast = parse_source(
            r#"
comptime fun bad(T: Type) -> DeclSet {
	ds = declset_new()
	s = as_struct_opt(T)
	info = unwrap(s)
	return declset_add_derived_struct(ds, info, "X")
}

comptime apply bad(I32)
"#,
        );
        let err = execute_comptime_applies(&mut ast).expect_err("bad emit should fail");
        assert!(err.to_string().contains("unwrap called on None"));
    }
}
