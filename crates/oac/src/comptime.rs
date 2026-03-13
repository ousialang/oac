use std::collections::HashMap;

use crate::ir::{self, SourceSpan};
use crate::parser::{
    self, Ast, EnumVariantDef, Expression, Literal, Op, Statement, StructDef, StructField,
    TypeDefDecl, UnaryOp,
};

const MAX_WHILE_ITERATIONS: usize = 100_000;
const MAX_CALL_STACK_DEPTH: usize = 256;

const META_TYPE_NAME_INTRINSIC: &str = "__intrinsic__meta__type_name";
const META_RESOLVE_TYPE_INTRINSIC: &str = "__intrinsic__meta__resolve_type";
const META_EXPR_METADATA_INTRINSIC: &str = "__intrinsic__meta__expr_opt";
const META_DEFINITION_LOCATION_INTRINSIC: &str = "__intrinsic__meta__definition_location_opt";
const META_IS_STRUCT_INTRINSIC: &str = "__intrinsic__meta__is_struct";
const META_IS_ENUM_INTRINSIC: &str = "__intrinsic__meta__is_enum";
const META_AS_STRUCT_OPT_INTRINSIC: &str = "__intrinsic__meta__as_struct_opt";
const META_AS_ENUM_OPT_INTRINSIC: &str = "__intrinsic__meta__as_enum_opt";
const META_STRUCT_FIELD_COUNT_INTRINSIC: &str = "__intrinsic__meta__struct_field_count";
const META_STRUCT_FIELD_AT_INTRINSIC: &str = "__intrinsic__meta__struct_field_at";
const META_ENUM_VARIANT_COUNT_INTRINSIC: &str = "__intrinsic__meta__enum_variant_count";
const META_ENUM_VARIANT_AT_INTRINSIC: &str = "__intrinsic__meta__enum_variant_at";
const META_FIELD_NAME_INTRINSIC: &str = "__intrinsic__meta__field_name";
const META_FIELD_TYPE_INTRINSIC: &str = "__intrinsic__meta__field_type";
const META_VARIANT_NAME_INTRINSIC: &str = "__intrinsic__meta__variant_name";
const META_VARIANT_PAYLOAD_TYPE_OPT_INTRINSIC: &str = "__intrinsic__meta__variant_payload_type_opt";
const META_SOURCE_SPAN_DISPLAY_INTRINSIC: &str = "__intrinsic__meta__source_span_display_compact";
const META_EXPR_OPT_FUNCTION: &str = "Meta__expr_opt";
const EMIT_DECLSET_NEW_INTRINSIC: &str = "__intrinsic__emit__declset_new";
const EMIT_ADD_EMPTY_ENUM_INTRINSIC: &str = "__intrinsic__emit__declset_add_empty_enum";
const EMIT_ADD_ENUM_TAG_VARIANT_INTRINSIC: &str = "__intrinsic__emit__declset_add_enum_tag_variant";
const EMIT_ADD_ENUM_PAYLOAD_VARIANT_INTRINSIC: &str =
    "__intrinsic__emit__declset_add_enum_payload_variant";
const EMIT_ADD_DERIVED_STRUCT_INTRINSIC: &str = "__intrinsic__emit__declset_add_derived_struct";
const EMIT_ADD_INVARIANT_FIELD_GT_I32_INTRINSIC: &str =
    "__intrinsic__emit__declset_add_invariant_field_gt_i32";

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
struct EnumInfoValue {
    name: String,
    variants: Vec<EnumVariantDef>,
}

#[derive(Clone, Debug)]
struct VariantInfoValue {
    #[allow(dead_code)]
    owner_enum: String,
    #[allow(dead_code)]
    index: usize,
    name: String,
    payload_ty: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SemanticExprValue {
    id: String,
    source_span: Option<SourceSpan>,
}

#[derive(Clone, Debug)]
struct PatternMatchResult {
    matched: bool,
    binding: Option<(String, CtValueWithMeta)>,
}

#[derive(Clone, Debug)]
enum CtValue {
    Bool(bool),
    I32(i32),
    #[allow(dead_code)]
    I64(i64),
    FP32(String),
    FP64(String),
    String(String),
    Type(String),
    Struct {
        type_name: String,
        fields: HashMap<String, CtValueWithMeta>,
    },
    Enum {
        type_name: String,
        variant_name: String,
        payload: Option<Box<CtValueWithMeta>>,
    },
    StructInfo(StructInfoValue),
    FieldInfo(FieldInfoValue),
    EnumInfo(EnumInfoValue),
    VariantInfo(VariantInfoValue),
    DeclSet(DeclSetValue),
    SemanticExpr(SemanticExprValue),
    #[allow(dead_code)]
    SourceSpan(SourceSpan),
    Option {
        inner: Option<Box<CtValue>>,
        inner_type: String,
        concrete_type: String,
    },
}

#[derive(Clone, Debug)]
struct CtValueWithMeta {
    value: CtValue,
    provenance: Option<String>,
    source_span: Option<SourceSpan>,
}

impl CtValueWithMeta {
    fn new(value: CtValue, provenance: Option<String>, source_span: Option<SourceSpan>) -> Self {
        Self {
            value,
            provenance,
            source_span,
        }
    }
}

fn resolve_bootstrap_program(ast: &Ast) -> anyhow::Result<ir::ResolvedProgram> {
    ir::resolve_with_mode(ast.clone(), ir::ResolveMode::BootstrapComptime)
}

fn resolved_function_definition<'a>(
    program: &'a ir::ResolvedProgram,
    function_name: &str,
) -> Option<(&'a ir::FunctionDefinition, bool)> {
    program
        .comptime_function_definitions
        .get(function_name)
        .map(|definition| (definition, true))
        .or_else(|| {
            program
                .function_definitions
                .get(function_name)
                .map(|definition| (definition, false))
        })
}

fn resolved_expression_source_span(
    program: &ir::ResolvedProgram,
    path: &str,
) -> Option<SourceSpan> {
    program
        .semantic_expr_metadata
        .get(path)
        .and_then(|metadata| metadata.source_span.clone())
}

pub fn execute_comptime_applies(
    ast: &mut Ast,
    mut program: ir::ResolvedProgram,
) -> anyhow::Result<()> {
    if ast.comptime_applies.is_empty() {
        return Ok(());
    }

    for apply in ast.comptime_applies.clone() {
        let (function, is_comptime) = resolved_function_definition(&program, &apply.function_name)
            .ok_or_else(|| anyhow::anyhow!("unknown comptime function {}", apply.function_name))?;
        let function_name = function.name.clone();
        let parameter_count = function.sig.parameters.len();
        let first_parameter_type = function
            .sig
            .parameters
            .first()
            .map(|param| param.ty.clone());
        if !is_comptime {
            return Err(anyhow::anyhow!(
                "comptime apply target {} must be declared with `comptime fun`",
                apply.function_name
            ));
        }
        if parameter_count != 1 {
            return Err(anyhow::anyhow!(
                "comptime apply target {} must accept exactly one parameter",
                apply.function_name
            ));
        }
        if first_parameter_type.as_deref() != Some("Type") {
            return Err(anyhow::anyhow!(
                "comptime apply target {} must accept a Type parameter, got {}",
                apply.function_name,
                first_parameter_type.unwrap_or_else(|| "<missing>".to_string())
            ));
        }
        let result = evaluate_function(
            &function_name,
            vec![CtValueWithMeta::new(
                CtValue::Type(apply.argument_type.clone()),
                None,
                None,
            )],
            &program,
            &mut Vec::new(),
        )?;
        let CtValue::DeclSet(declset) = result.value else {
            return Err(anyhow::anyhow!(
                "comptime apply target {} must return DeclSet",
                function_name
            ));
        };
        merge_declset_into_ast(ast, declset)?;
        program = resolve_bootstrap_program(ast)?;
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

fn evaluate_function(
    function_name: &str,
    args: Vec<CtValueWithMeta>,
    program: &ir::ResolvedProgram,
    call_stack: &mut Vec<String>,
) -> anyhow::Result<CtValueWithMeta> {
    if call_stack.len() >= MAX_CALL_STACK_DEPTH {
        return Err(anyhow::anyhow!(
            "comptime call stack exceeded limit ({}): {} -> {}",
            MAX_CALL_STACK_DEPTH,
            call_stack.join(" -> "),
            function_name
        ));
    }
    let (function, is_comptime) = resolved_function_definition(program, function_name)
        .ok_or_else(|| anyhow::anyhow!("unknown comptime-callable function {}", function_name))?;
    if function.sig.parameters.len() != args.len() {
        return Err(anyhow::anyhow!(
            "function {} expects {} arguments, got {}",
            function_name,
            function.sig.parameters.len(),
            args.len()
        ));
    }

    for (parameter, arg) in function.sig.parameters.iter().zip(args.iter()) {
        if !ct_value_matches_type(&arg.value, &parameter.ty) {
            return Err(anyhow::anyhow!(
                "function {} argument type mismatch for {}: expected {}, got {}",
                function_name,
                parameter.name,
                parameter.ty,
                ct_value_type_name(&arg.value)
            ));
        }
    }

    call_stack.push(function_name.to_string());
    let mut env = HashMap::new();
    for type_name in program.type_definitions.keys() {
        env.insert(
            type_name.clone(),
            CtValueWithMeta::new(CtValue::Type(type_name.clone()), None, None),
        );
    }
    for (parameter, arg) in function.sig.parameters.iter().zip(args) {
        env.insert(parameter.name.clone(), arg);
    }

    for (clause_ordinal, clause) in function.preconditions.iter().enumerate() {
        let full_path = format!(
            "{}/pre:{}",
            function_scope_prefix(function_name, is_comptime),
            clause_ordinal
        );
        let condition = evaluate_expression(clause, &full_path, &mut env, program, call_stack)?;
        if !expect_bool(&condition.value, "comptime precondition")? {
            call_stack.pop();
            return Err(anyhow::anyhow!(
                "precondition {} of {} evaluated to false during comptime execution",
                clause_ordinal,
                function_name
            ));
        }
    }

    for (statement_index, statement) in function.body.iter().enumerate() {
        let full_path = format!(
            "{}/stmt:{}",
            function_scope_prefix(function_name, is_comptime),
            statement_index
        );
        if let Some(ret) = evaluate_statement(statement, &full_path, &mut env, program, call_stack)?
        {
            if !ct_value_matches_type(&ret.value, &function.sig.return_type) {
                return Err(anyhow::anyhow!(
                    "function {} must return {}, got {}",
                    function_name,
                    function.sig.return_type,
                    ct_value_type_name(&ret.value)
                ));
            }
            call_stack.pop();
            return Ok(ret);
        }
    }

    call_stack.pop();
    Err(anyhow::anyhow!(
        "function {} must return a value",
        function_name
    ))
}

fn function_scope_prefix(function_name: &str, is_comptime: bool) -> String {
    if is_comptime {
        format!("comptime_fn:{function_name}")
    } else {
        format!("fn:{function_name}")
    }
}

fn with_expression_metadata(
    mut value: CtValueWithMeta,
    path: &str,
    program: &ir::ResolvedProgram,
) -> CtValueWithMeta {
    value.provenance = Some(path.to_string());
    value.source_span = resolved_expression_source_span(program, path);
    value
}

fn evaluate_statement(
    statement: &Statement,
    path: &str,
    env: &mut HashMap<String, CtValueWithMeta>,
    program: &ir::ResolvedProgram,
    call_stack: &mut Vec<String>,
) -> anyhow::Result<Option<CtValueWithMeta>> {
    match statement {
        Statement::StructDef { .. } => Err(anyhow::anyhow!(
            "local struct declarations are unsupported in comptime function bodies"
        )),
        Statement::Match { subject, arms } => {
            let subject_value = evaluate_expression(
                subject,
                &format!("{path}/match.subject"),
                env,
                program,
                call_stack,
            )?;
            for (arm_index, arm) in arms.iter().enumerate() {
                let pattern_match = match_pattern_binding(&subject_value, &arm.pattern)?;
                if pattern_match.matched {
                    let previous = pattern_match
                        .binding
                        .as_ref()
                        .and_then(|(name, value)| env.insert(name.clone(), value.clone()));
                    for (statement_index, statement) in arm.body.iter().enumerate() {
                        let arm_full_path =
                            format!("{path}/match.arm.{arm_index}.{statement_index}");
                        if let Some(ret) =
                            evaluate_statement(statement, &arm_full_path, env, program, call_stack)?
                        {
                            restore_match_binding(env, pattern_match.binding.as_ref(), previous);
                            return Ok(Some(ret));
                        }
                    }
                    restore_match_binding(env, pattern_match.binding.as_ref(), previous);
                    return Ok(None);
                }
            }
            Err(anyhow::anyhow!(
                "non-exhaustive match in comptime evaluator"
            ))
        }
        Statement::Conditional {
            condition,
            body,
            else_body,
        } => {
            let cond = evaluate_expression(
                condition,
                &format!("{path}/if.cond"),
                env,
                program,
                call_stack,
            )?;
            let cond_bool = expect_bool(&cond.value, "if condition")?;
            if cond_bool {
                for (index, statement) in body.iter().enumerate() {
                    if let Some(ret) = evaluate_statement(
                        statement,
                        &format!("{path}/if.body.{index}"),
                        env,
                        program,
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
                        program,
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
                program,
                call_stack,
            )?;
            env.insert(variable.clone(), evaluated);
            Ok(None)
        }
        Statement::Return { expr } => {
            let evaluated = evaluate_expression(
                expr,
                &format!("{path}/return.expr"),
                env,
                program,
                call_stack,
            )?;
            Ok(Some(evaluated))
        }
        Statement::Expression { expr } => {
            evaluate_expression(expr, &format!("{path}/expr"), env, program, call_stack)?;
            Ok(None)
        }
        Statement::Prove { condition } => {
            let evaluated = evaluate_expression(
                condition,
                &format!("{path}/prove.cond"),
                env,
                program,
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
                program,
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
                    program,
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
                        program,
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
    program: &ir::ResolvedProgram,
    call_stack: &mut Vec<String>,
) -> anyhow::Result<CtValueWithMeta> {
    match expression {
        Expression::Match { subject, arms } => {
            let subject_value = evaluate_expression(
                subject,
                &format!("{path}/match.subject"),
                env,
                program,
                call_stack,
            )?;
            for (arm_index, arm) in arms.iter().enumerate() {
                let pattern_match = match_pattern_binding(&subject_value, &arm.pattern)?;
                if pattern_match.matched {
                    let previous = pattern_match
                        .binding
                        .as_ref()
                        .and_then(|(name, value)| env.insert(name.clone(), value.clone()));
                    let value = evaluate_expression(
                        &arm.value,
                        &format!("{path}/match.arm.{arm_index}"),
                        env,
                        program,
                        call_stack,
                    )?;
                    restore_match_binding(env, pattern_match.binding.as_ref(), previous);
                    return Ok(with_expression_metadata(value, path, program));
                }
            }
            Err(anyhow::anyhow!(
                "non-exhaustive match in comptime evaluator"
            ))
        }
        Expression::Literal(Literal::Int(n)) => {
            let value = i32::try_from(*n)
                .map_err(|_| anyhow::anyhow!("integer literal {} is out of i32 range", n))?;
            Ok(CtValueWithMeta::new(
                CtValue::I32(value),
                Some(path.to_string()),
                resolved_expression_source_span(program, path),
            ))
        }
        Expression::Literal(Literal::Float32(value)) => Ok(CtValueWithMeta::new(
            CtValue::FP32(value.clone()),
            Some(path.to_string()),
            resolved_expression_source_span(program, path),
        )),
        Expression::Literal(Literal::Float64(value)) => Ok(CtValueWithMeta::new(
            CtValue::FP64(value.clone()),
            Some(path.to_string()),
            resolved_expression_source_span(program, path),
        )),
        Expression::Literal(Literal::String(s)) => Ok(CtValueWithMeta::new(
            CtValue::String(s.clone()),
            Some(path.to_string()),
            resolved_expression_source_span(program, path),
        )),
        Expression::Literal(Literal::Bool(b)) => Ok(CtValueWithMeta::new(
            CtValue::Bool(*b),
            Some(path.to_string()),
            resolved_expression_source_span(program, path),
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
                        program,
                        call_stack,
                    )
                })
                .collect::<anyhow::Result<Vec<_>>>()?;
            let value = evaluate_call(name, evaluated_args, path, program, call_stack)?;
            Ok(with_expression_metadata(value, path, program))
        }
        Expression::MethodCall {
            receiver,
            method,
            args,
        } => {
            let evaluated_args = args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    evaluate_expression(
                        arg,
                        &format!("{path}/method.arg.{index}"),
                        env,
                        program,
                        call_stack,
                    )
                })
                .collect::<anyhow::Result<Vec<_>>>()?;
            if let Expression::Variable(name) = receiver.as_ref() {
                let can_use_type_namespace = matches!(
                    env.get(name).map(|value| &value.value),
                    Some(CtValue::Type(type_name)) if type_name == name
                );
                if is_builtin_operator_trait_name(name) && !env.contains_key(name) {
                    return evaluate_builtin_operator_trait_call(
                        name,
                        method,
                        evaluated_args,
                        path,
                    );
                }
                if can_use_type_namespace || !env.contains_key(name) {
                    if let Some(enum_value) = try_make_enum_constructor(
                        name,
                        method,
                        evaluated_args.clone(),
                        path,
                        program,
                    )? {
                        return Ok(with_expression_metadata(enum_value, path, program));
                    }
                    let namespaced_call = parser::qualify_namespace_function_name(name, method);
                    if resolved_function_definition(program, &namespaced_call).is_some()
                        || namespaced_call == META_EXPR_OPT_FUNCTION
                    {
                        let value = evaluate_call(
                            &namespaced_call,
                            evaluated_args,
                            path,
                            program,
                            call_stack,
                        )?;
                        return Ok(with_expression_metadata(value, path, program));
                    }
                }
            }
            let evaluated_receiver = evaluate_expression(
                receiver,
                &format!("{path}/method.receiver"),
                env,
                program,
                call_stack,
            )?;
            let value = evaluate_supported_method_call(
                evaluated_receiver,
                method,
                evaluated_args,
                path,
                program,
                call_stack,
            )?;
            Ok(with_expression_metadata(value, path, program))
        }
        Expression::PostfixCall { callee, args } => {
            let callee = callee.as_ref();
            let evaluated_args = args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    evaluate_expression(
                        arg,
                        &format!("{path}/postfix.arg.{index}"),
                        env,
                        program,
                        call_stack,
                    )
                })
                .collect::<anyhow::Result<Vec<_>>>()?;
            match callee {
                Expression::FieldAccess {
                    struct_variable,
                    field,
                } if is_builtin_operator_trait_name(struct_variable) => {
                    let value = evaluate_builtin_operator_trait_call(
                        struct_variable,
                        field,
                        evaluated_args,
                        path,
                    )?;
                    Ok(with_expression_metadata(value, path, program))
                }
                Expression::FieldAccess {
                    struct_variable,
                    field,
                } => {
                    if let Some(enum_value) = try_make_enum_constructor(
                        struct_variable,
                        field,
                        evaluated_args.clone(),
                        path,
                        program,
                    )? {
                        return Ok(with_expression_metadata(enum_value, path, program));
                    }
                    let namespaced_call =
                        parser::qualify_namespace_function_name(struct_variable, field);
                    let value =
                        evaluate_call(&namespaced_call, evaluated_args, path, program, call_stack)?;
                    Ok(with_expression_metadata(value, path, program))
                }
                _ => Err(anyhow::anyhow!(
                    "postfix calls are unsupported in comptime evaluator"
                )),
            }
        }
        Expression::BinOp(op, left, right) => {
            let left =
                evaluate_expression(left, &format!("{path}/bin.left"), env, program, call_stack)?;
            let right = evaluate_expression(
                right,
                &format!("{path}/bin.right"),
                env,
                program,
                call_stack,
            )?;
            let value = evaluate_binary_op(*op, &left.value, &right.value)?;
            Ok(CtValueWithMeta::new(
                value,
                Some(path.to_string()),
                resolved_expression_source_span(program, path),
            ))
        }
        Expression::UnaryOp(op, expr) => {
            let inner =
                evaluate_expression(expr, &format!("{path}/unary"), env, program, call_stack)?;
            match op {
                UnaryOp::Not => Ok(CtValueWithMeta::new(
                    CtValue::Bool(!expect_bool(&inner.value, "unary ! operand")?),
                    Some(path.to_string()),
                    resolved_expression_source_span(program, path),
                )),
            }
        }
        Expression::FieldAccess {
            struct_variable,
            field,
        } => {
            let value = env.get(struct_variable).cloned().ok_or_else(|| {
                anyhow::anyhow!(
                    "unknown variable {} in comptime field access",
                    struct_variable
                )
            })?;
            let result = match value.value {
                CtValue::Struct { fields, .. } => fields.get(field).cloned().ok_or_else(|| {
                    anyhow::anyhow!("field {} not found in {}", field, struct_variable)
                }),
                _ => Err(anyhow::anyhow!(
                    "field access requires struct value, got {}",
                    ct_value_type_name(&value.value)
                )),
            }?;
            Ok(with_expression_metadata(result, path, program))
        }
        Expression::StructValue {
            struct_name,
            field_values,
        } => {
            let struct_def = resolved_struct_def(program, struct_name)
                .ok_or_else(|| {
                    anyhow::anyhow!("unknown struct {} in comptime literal", struct_name)
                })?
                .clone();
            let mut fields = HashMap::new();
            for (field_index, (field_name, field_value)) in field_values.iter().enumerate() {
                let value = evaluate_expression(
                    field_value,
                    &format!("{path}/struct.field.{field_index}"),
                    env,
                    program,
                    call_stack,
                )?;
                fields.insert(field_name.clone(), value);
            }
            for field in &struct_def.struct_fields {
                if !fields.contains_key(&field.name) {
                    return Err(anyhow::anyhow!(
                        "missing field {} in comptime struct literal {}",
                        field.name,
                        struct_name
                    ));
                }
            }
            Ok(CtValueWithMeta::new(
                CtValue::Struct {
                    type_name: struct_name.clone(),
                    fields,
                },
                Some(path.to_string()),
                resolved_expression_source_span(program, path),
            ))
        }
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
        Op::Add => checked_i32_binary(
            expect_i32(left, "+ left operand")?,
            expect_i32(right, "+ right operand")?,
            "+",
            i32::checked_add,
        )
        .map(CtValue::I32),
        Op::Sub => checked_i32_binary(
            expect_i32(left, "- left operand")?,
            expect_i32(right, "- right operand")?,
            "-",
            i32::checked_sub,
        )
        .map(CtValue::I32),
        Op::Mul => checked_i32_binary(
            expect_i32(left, "* left operand")?,
            expect_i32(right, "* right operand")?,
            "*",
            i32::checked_mul,
        )
        .map(CtValue::I32),
        Op::Div => checked_i32_div(
            expect_i32(left, "/ left operand")?,
            expect_i32(right, "/ right operand")?,
        )
        .map(CtValue::I32),
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

fn evaluate_builtin_operator_trait_call(
    trait_name: &str,
    method_name: &str,
    args: Vec<CtValueWithMeta>,
    path: &str,
) -> anyhow::Result<CtValueWithMeta> {
    let as_value = |value| CtValueWithMeta::new(value, Some(path.to_string()), None);
    if args.len() != 2 {
        return Err(anyhow::anyhow!(
            "trait call {}.{} expects 2 arguments in comptime evaluator, got {}",
            trait_name,
            method_name,
            args.len()
        ));
    }
    let left = &args[0].value;
    let right = &args[1].value;

    match (trait_name, method_name) {
        ("Addition", "add") => checked_i32_binary(
            expect_i32(left, "Addition.add left operand")?,
            expect_i32(right, "Addition.add right operand")?,
            "+",
            i32::checked_add,
        )
        .map(CtValue::I32)
        .map(as_value),
        ("Subtraction", "sub") => checked_i32_binary(
            expect_i32(left, "Subtraction.sub left operand")?,
            expect_i32(right, "Subtraction.sub right operand")?,
            "-",
            i32::checked_sub,
        )
        .map(CtValue::I32)
        .map(as_value),
        ("Multiplication", "mul") => checked_i32_binary(
            expect_i32(left, "Multiplication.mul left operand")?,
            expect_i32(right, "Multiplication.mul right operand")?,
            "*",
            i32::checked_mul,
        )
        .map(CtValue::I32)
        .map(as_value),
        ("Division", "div") => checked_i32_div(
            expect_i32(left, "Division.div left operand")?,
            expect_i32(right, "Division.div right operand")?,
        )
        .map(CtValue::I32)
        .map(as_value),
        ("Equality", "equals") => match (left, right) {
            (CtValue::Bool(a), CtValue::Bool(b)) => Ok(as_value(CtValue::Bool(a == b))),
            (CtValue::I32(a), CtValue::I32(b)) => Ok(as_value(CtValue::Bool(a == b))),
            (CtValue::I64(a), CtValue::I64(b)) => Ok(as_value(CtValue::Bool(a == b))),
            _ => Err(anyhow::anyhow!(
                "trait call Equality.equals is unsupported in comptime evaluator for {} and {}",
                ct_value_type_name(left),
                ct_value_type_name(right)
            )),
        },
        ("Comparison", "compare") => {
            let lhs = expect_i32(left, "Comparison.compare left operand")?;
            let rhs = expect_i32(right, "Comparison.compare right operand")?;
            let value = if lhs < rhs {
                -1
            } else if lhs > rhs {
                1
            } else {
                0
            };
            Ok(as_value(CtValue::I32(value)))
        }
        _ => Err(anyhow::anyhow!(
            "trait call {}.{} is unsupported in comptime evaluator v1",
            trait_name,
            method_name
        )),
    }
}

fn is_builtin_operator_trait_name(name: &str) -> bool {
    matches!(
        name,
        "Addition" | "Subtraction" | "Multiplication" | "Division" | "Equality" | "Comparison"
    )
}

fn resolved_struct_def<'a>(
    program: &'a ir::ResolvedProgram,
    struct_name: &str,
) -> Option<&'a StructDef> {
    match program.type_definitions.get(struct_name) {
        Some(ir::TypeDef::Struct(def)) => Some(def),
        _ => None,
    }
}

fn resolved_enum_def<'a>(
    program: &'a ir::ResolvedProgram,
    enum_name: &str,
) -> Option<&'a ir::EnumTypeDef> {
    match program.type_definitions.get(enum_name) {
        Some(ir::TypeDef::Enum(def)) => Some(def),
        _ => None,
    }
}

fn resolved_type_exists(program: &ir::ResolvedProgram, type_name: &str) -> bool {
    program.type_definitions.contains_key(type_name)
}

fn evaluate_supported_method_call(
    receiver: CtValueWithMeta,
    method_name: &str,
    args: Vec<CtValueWithMeta>,
    path: &str,
    program: &ir::ResolvedProgram,
    call_stack: &mut Vec<String>,
) -> anyhow::Result<CtValueWithMeta> {
    if let Some(namespace) = ct_value_namespace_name(&receiver.value) {
        let function_name = parser::qualify_namespace_function_name(&namespace, method_name);
        if resolved_function_definition(program, &function_name).is_some() {
            let mut call_args = Vec::with_capacity(args.len() + 1);
            call_args.push(receiver);
            call_args.extend(args);
            return evaluate_call(&function_name, call_args, path, program, call_stack);
        }
    }
    Err(anyhow::anyhow!(
        "method call {}.{} is unsupported in comptime evaluator",
        ct_value_type_name(&receiver.value),
        method_name
    ))
}

fn ct_value_namespace_name(value: &CtValue) -> Option<String> {
    match value {
        CtValue::String(_) => Some("String".to_string()),
        CtValue::Type(_) => Some("Type".to_string()),
        CtValue::Struct { type_name, .. } => Some(type_name.clone()),
        CtValue::Enum { type_name, .. } => Some(type_name.clone()),
        CtValue::StructInfo(_) => Some("StructInfo".to_string()),
        CtValue::FieldInfo(_) => Some("FieldInfo".to_string()),
        CtValue::EnumInfo(_) => Some("EnumInfo".to_string()),
        CtValue::VariantInfo(_) => Some("VariantInfo".to_string()),
        CtValue::DeclSet(_) => Some("DeclSet".to_string()),
        CtValue::SemanticExpr(_) => Some("SemanticExpr".to_string()),
        CtValue::SourceSpan(_) => Some("SourceSpan".to_string()),
        CtValue::Option { concrete_type, .. } => Some(concrete_type.clone()),
        CtValue::Bool(_)
        | CtValue::I32(_)
        | CtValue::I64(_)
        | CtValue::FP32(_)
        | CtValue::FP64(_) => None,
    }
}

fn try_make_enum_constructor(
    enum_name: &str,
    variant_name: &str,
    args: Vec<CtValueWithMeta>,
    path: &str,
    program: &ir::ResolvedProgram,
) -> anyhow::Result<Option<CtValueWithMeta>> {
    let Some(enum_def) = resolved_enum_def(program, enum_name) else {
        return Ok(None);
    };
    let Some(variant) = enum_def
        .variants
        .iter()
        .find(|variant| variant.name == variant_name)
    else {
        return Ok(None);
    };
    let payload = match (&variant.payload_ty, args.as_slice()) {
        (None, []) => None,
        (Some(_), [value]) => Some(Box::new(value.clone())),
        (None, _) => {
            return Err(anyhow::anyhow!(
                "enum constructor {}.{} expects no payload",
                enum_name,
                variant_name
            ))
        }
        (Some(_), _) => {
            return Err(anyhow::anyhow!(
                "enum constructor {}.{} expects one payload argument",
                enum_name,
                variant_name
            ))
        }
    };
    Ok(Some(CtValueWithMeta::new(
        CtValue::Enum {
            type_name: enum_name.to_string(),
            variant_name: variant_name.to_string(),
            payload,
        },
        Some(path.to_string()),
        None,
    )))
}

fn match_pattern_binding(
    subject: &CtValueWithMeta,
    pattern: &parser::MatchPattern,
) -> anyhow::Result<PatternMatchResult> {
    let parser::MatchPattern::Variant {
        type_name,
        variant_name,
        binder,
    } = pattern;

    match &subject.value {
        CtValue::Enum {
            type_name: subject_type,
            variant_name: subject_variant,
            payload,
        } if subject_type == type_name && subject_variant == variant_name => {
            let binding = match (binder, payload) {
                (Some(name), Some(payload)) => Some((name.clone(), (**payload).clone())),
                (None, None) => None,
                (None, Some(_)) => None,
                (Some(_), None) => {
                    return Err(anyhow::anyhow!(
                        "match binder requires payload for {}.{}",
                        type_name,
                        variant_name
                    ))
                }
            };
            Ok(PatternMatchResult {
                matched: true,
                binding,
            })
        }
        CtValue::Option {
            inner,
            concrete_type,
            ..
        } if concrete_type == type_name => match (variant_name.as_str(), inner, binder) {
            ("None", None, None) => Ok(PatternMatchResult {
                matched: true,
                binding: None,
            }),
            ("None", None, Some(_)) => Err(anyhow::anyhow!(
                "match binder requires payload for {}.{}",
                type_name,
                variant_name
            )),
            ("Some", Some(payload), Some(name)) => Ok(PatternMatchResult {
                matched: true,
                binding: Some((
                    name.clone(),
                    CtValueWithMeta::new(
                        (**payload).clone(),
                        subject.provenance.clone(),
                        subject.source_span.clone(),
                    ),
                )),
            }),
            ("Some", Some(_), None) => Ok(PatternMatchResult {
                matched: true,
                binding: None,
            }),
            _ => Ok(PatternMatchResult {
                matched: false,
                binding: None,
            }),
        },
        _ => Ok(PatternMatchResult {
            matched: false,
            binding: None,
        }),
    }
}

fn restore_match_binding(
    env: &mut HashMap<String, CtValueWithMeta>,
    binding: Option<&(String, CtValueWithMeta)>,
    previous: Option<CtValueWithMeta>,
) {
    if let Some((name, _)) = binding {
        if let Some(previous) = previous {
            env.insert(name.clone(), previous);
        } else {
            env.remove(name);
        }
    }
}

fn checked_i32_binary(
    left: i32,
    right: i32,
    op: &str,
    checked: fn(i32, i32) -> Option<i32>,
) -> anyhow::Result<i32> {
    checked(left, right)
        .ok_or_else(|| anyhow::anyhow!("comptime integer overflow in {left} {op} {right}"))
}

fn checked_i32_div(left: i32, right: i32) -> anyhow::Result<i32> {
    if right == 0 {
        return Err(anyhow::anyhow!(
            "comptime division by zero in {left} / {right}"
        ));
    }
    left.checked_div(right)
        .ok_or_else(|| anyhow::anyhow!("comptime integer overflow in {left} / {right}"))
}

fn evaluate_call(
    name: &str,
    args: Vec<CtValueWithMeta>,
    path: &str,
    program: &ir::ResolvedProgram,
    call_stack: &mut Vec<String>,
) -> anyhow::Result<CtValueWithMeta> {
    let as_value = |value| CtValueWithMeta::new(value, Some(path.to_string()), None);
    let as_option = |inner: Option<CtValue>, concrete_type: &str, inner_type: &str| {
        CtValueWithMeta::new(
            CtValue::Option {
                inner: inner.map(Box::new),
                inner_type: inner_type.to_string(),
                concrete_type: concrete_type.to_string(),
            },
            Some(path.to_string()),
            None,
        )
    };

    if let Some(ignored) = try_evaluate_ignored_output_call(name, &args, path)? {
        return Ok(ignored);
    }

    match name {
        META_EXPR_OPT_FUNCTION | META_EXPR_METADATA_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            if let Some(meta) = args[0].provenance.clone() {
                Ok(as_option(
                    Some(CtValue::SemanticExpr(SemanticExprValue {
                        id: meta,
                        source_span: args[0].source_span.clone(),
                    })),
                    "SemanticExprOpt",
                    "SemanticExpr",
                ))
            } else {
                Ok(as_option(None, "SemanticExprOpt", "SemanticExpr"))
            }
        }
        META_DEFINITION_LOCATION_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            let semantic_expr =
                expect_semantic_expr(&args[0].value, "definition_location_opt argument")?;
            if let Some(span) = semantic_expr.source_span.clone() {
                Ok(as_option(
                    Some(CtValue::SourceSpan(span)),
                    "SourceSpanOpt",
                    "SourceSpan",
                ))
            } else {
                Ok(as_option(None, "SourceSpanOpt", "SourceSpan"))
            }
        }
        "String__concat" => {
            ensure_arity(name, &args, 2)?;
            Ok(as_value(CtValue::String(format!(
                "{}{}",
                expect_string(&args[0].value, "concat left argument")?,
                expect_string(&args[1].value, "concat right argument")?
            ))))
        }
        META_RESOLVE_TYPE_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            Ok(as_value(CtValue::Type(
                expect_string(&args[0].value, "resolve_type argument")?.to_string(),
            )))
        }
        META_TYPE_NAME_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            Ok(as_value(CtValue::String(
                expect_type_name(&args[0].value, "type_name argument")?.to_string(),
            )))
        }
        META_IS_STRUCT_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            let type_name = expect_type_name(&args[0].value, "is_struct argument")?;
            Ok(as_value(CtValue::Bool(
                resolved_struct_def(program, type_name).is_some(),
            )))
        }
        META_IS_ENUM_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            let type_name = expect_type_name(&args[0].value, "is_enum argument")?;
            Ok(as_value(CtValue::Bool(
                resolved_enum_def(program, type_name).is_some(),
            )))
        }
        META_AS_STRUCT_OPT_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            let type_name = expect_type_name(&args[0].value, "as_struct_opt argument")?;
            if let Some(struct_def) = resolved_struct_def(program, type_name) {
                Ok(as_option(
                    Some(CtValue::StructInfo(StructInfoValue {
                        name: struct_def.name.clone(),
                        fields: struct_def.struct_fields.clone(),
                    })),
                    "StructInfoOpt",
                    "StructInfo",
                ))
            } else {
                Ok(as_option(None, "StructInfoOpt", "StructInfo"))
            }
        }
        META_AS_ENUM_OPT_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            let type_name = expect_type_name(&args[0].value, "as_enum_opt argument")?;
            if let Some(enum_def) = resolved_enum_def(program, type_name) {
                Ok(as_option(
                    Some(CtValue::EnumInfo(EnumInfoValue {
                        name: enum_def.name.clone(),
                        variants: enum_def
                            .variants
                            .iter()
                            .map(|variant| EnumVariantDef {
                                name: variant.name.clone(),
                                payload_ty: variant.payload_ty.clone(),
                            })
                            .collect(),
                    })),
                    "EnumInfoOpt",
                    "EnumInfo",
                ))
            } else {
                Ok(as_option(None, "EnumInfoOpt", "EnumInfo"))
            }
        }
        META_STRUCT_FIELD_COUNT_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            let struct_info = expect_struct_info(&args[0].value, "struct_field_count argument")?;
            Ok(as_value(CtValue::I32(struct_info.fields.len() as i32)))
        }
        META_STRUCT_FIELD_AT_INTRINSIC => {
            ensure_arity(name, &args, 2)?;
            let struct_info = expect_struct_info(&args[0].value, "struct_field_at first argument")?;
            let index = expect_i32(&args[1].value, "struct_field_at second argument")?;
            if index < 0 || index as usize >= struct_info.fields.len() {
                return Ok(as_option(None, "FieldInfoOpt", "FieldInfo"));
            }
            let field = &struct_info.fields[index as usize];
            Ok(as_option(
                Some(CtValue::FieldInfo(FieldInfoValue {
                    owner_struct: struct_info.name.clone(),
                    index: index as usize,
                    name: field.name.clone(),
                    ty: field.ty.clone(),
                })),
                "FieldInfoOpt",
                "FieldInfo",
            ))
        }
        META_ENUM_VARIANT_COUNT_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            let enum_info = expect_enum_info(&args[0].value, "enum_variant_count argument")?;
            Ok(as_value(CtValue::I32(enum_info.variants.len() as i32)))
        }
        META_ENUM_VARIANT_AT_INTRINSIC => {
            ensure_arity(name, &args, 2)?;
            let enum_info = expect_enum_info(&args[0].value, "enum_variant_at first argument")?;
            let index = expect_i32(&args[1].value, "enum_variant_at second argument")?;
            if index < 0 || index as usize >= enum_info.variants.len() {
                return Ok(as_option(None, "VariantInfoOpt", "VariantInfo"));
            }
            let variant = &enum_info.variants[index as usize];
            Ok(as_option(
                Some(CtValue::VariantInfo(VariantInfoValue {
                    owner_enum: enum_info.name.clone(),
                    index: index as usize,
                    name: variant.name.clone(),
                    payload_ty: variant.payload_ty.clone(),
                })),
                "VariantInfoOpt",
                "VariantInfo",
            ))
        }
        META_FIELD_NAME_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            let field_info = expect_field_info(&args[0].value, "field_name argument")?;
            Ok(as_value(CtValue::String(field_info.name.clone())))
        }
        META_FIELD_TYPE_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            let field_info = expect_field_info(&args[0].value, "field_type argument")?;
            Ok(as_value(CtValue::Type(field_info.ty.clone())))
        }
        META_VARIANT_NAME_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            let variant_info = expect_variant_info(&args[0].value, "variant_name argument")?;
            Ok(as_value(CtValue::String(variant_info.name.clone())))
        }
        META_VARIANT_PAYLOAD_TYPE_OPT_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            let variant_info =
                expect_variant_info(&args[0].value, "variant_payload_type_opt argument")?;
            Ok(as_option(
                variant_info.payload_ty.clone().map(CtValue::Type),
                "TypeOpt",
                "Type",
            ))
        }
        META_SOURCE_SPAN_DISPLAY_INTRINSIC => {
            ensure_arity(name, &args, 1)?;
            let span = expect_source_span(&args[0].value, "SourceSpan.display_compact argument")?;
            Ok(as_value(CtValue::String(format_source_span_compact(span))))
        }
        EMIT_DECLSET_NEW_INTRINSIC => {
            ensure_arity(name, &args, 0)?;
            Ok(as_value(CtValue::DeclSet(DeclSetValue::default())))
        }
        EMIT_ADD_EMPTY_ENUM_INTRINSIC => {
            ensure_arity(name, &args, 2)?;
            let mut declset =
                expect_declset(&args[0].value, "declset_add_empty_enum first argument")?.clone();
            let new_name = expect_string(&args[1].value, "declset_add_empty_enum second argument")?
                .to_string();
            if type_known_in_declset_or_program(&new_name, &declset, program) {
                return Err(anyhow::anyhow!(
                    "declset_add_empty_enum cannot emit duplicate type {}",
                    new_name
                ));
            }
            declset
                .type_definitions
                .push(TypeDefDecl::Enum(parser::EnumDef {
                    name: new_name,
                    variants: vec![],
                }));
            Ok(as_value(CtValue::DeclSet(declset)))
        }
        EMIT_ADD_ENUM_TAG_VARIANT_INTRINSIC => {
            ensure_arity(name, &args, 3)?;
            let mut declset = expect_declset(
                &args[0].value,
                "declset_add_enum_tag_variant first argument",
            )?
            .clone();
            let enum_name = expect_string(
                &args[1].value,
                "declset_add_enum_tag_variant second argument",
            )?;
            let variant_name = expect_string(
                &args[2].value,
                "declset_add_enum_tag_variant third argument",
            )?
            .to_string();
            let enum_def = find_emitted_enum_mut(&mut declset, enum_name).ok_or_else(|| {
                anyhow::anyhow!(
                    "declset_add_enum_tag_variant target {} is not an emitted enum in this DeclSet",
                    enum_name
                )
            })?;
            ensure_enum_variant_name_available(
                enum_def,
                &variant_name,
                "declset_add_enum_tag_variant",
            )?;
            enum_def.variants.push(EnumVariantDef {
                name: variant_name,
                payload_ty: None,
            });
            Ok(as_value(CtValue::DeclSet(declset)))
        }
        EMIT_ADD_ENUM_PAYLOAD_VARIANT_INTRINSIC => {
            ensure_arity(name, &args, 4)?;
            let mut declset = expect_declset(
                &args[0].value,
                "declset_add_enum_payload_variant first argument",
            )?
            .clone();
            let enum_name = expect_string(
                &args[1].value,
                "declset_add_enum_payload_variant second argument",
            )?;
            let variant_name = expect_string(
                &args[2].value,
                "declset_add_enum_payload_variant third argument",
            )?
            .to_string();
            let payload_ty = expect_type_name(
                &args[3].value,
                "declset_add_enum_payload_variant fourth argument",
            )?
            .to_string();
            let enum_def = find_emitted_enum_mut(&mut declset, enum_name).ok_or_else(|| {
                anyhow::anyhow!(
                    "declset_add_enum_payload_variant target {} is not an emitted enum in this DeclSet",
                    enum_name
                )
            })?;
            ensure_enum_variant_name_available(
                enum_def,
                &variant_name,
                "declset_add_enum_payload_variant",
            )?;
            enum_def.variants.push(EnumVariantDef {
                name: variant_name,
                payload_ty: Some(payload_ty),
            });
            Ok(as_value(CtValue::DeclSet(declset)))
        }
        EMIT_ADD_DERIVED_STRUCT_INTRINSIC => {
            ensure_arity(name, &args, 3)?;
            let mut declset =
                expect_declset(&args[0].value, "declset_add_derived_struct first argument")?
                    .clone();
            let base =
                expect_struct_info(&args[1].value, "declset_add_derived_struct second argument")?;
            let new_name =
                expect_string(&args[2].value, "declset_add_derived_struct third argument")?
                    .to_string();
            if resolved_type_exists(program, &new_name)
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
        EMIT_ADD_INVARIANT_FIELD_GT_I32_INTRINSIC => {
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

            let struct_def =
                find_struct_for_type(target_type, &declset, program).ok_or_else(|| {
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
                parameters: vec![parser::Parameter {
                    name: "v".to_string(),
                    ty: target_type.to_string(),
                }],
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
                source_span: None,
                local_source_spans: HashMap::new(),
            });

            Ok(as_value(CtValue::DeclSet(declset)))
        }
        _ => {
            if resolved_function_definition(program, name).is_some() {
                let result = evaluate_function(name, args, program, call_stack)?;
                Ok(CtValueWithMeta::new(
                    result.value,
                    Some(path.to_string()),
                    result.source_span,
                ))
            } else {
                Err(anyhow::anyhow!(
                    "unsupported function call {} in comptime evaluator (it remains deterministic and pure)",
                    name
                ))
            }
        }
    }
}

fn try_evaluate_ignored_output_call(
    name: &str,
    args: &[CtValueWithMeta],
    path: &str,
) -> anyhow::Result<Option<CtValueWithMeta>> {
    let as_value = |value| CtValueWithMeta::new(value, Some(path.to_string()), None);
    match name {
        "print" => {
            ensure_arity(name, args, 1)?;
            expect_i32(&args[0].value, "print argument")?;
            Ok(Some(as_value(CtValue::I32(0))))
        }
        "print_str" => {
            ensure_arity(name, args, 1)?;
            expect_string(&args[0].value, "print_str argument")?;
            Ok(Some(as_value(CtValue::I32(0))))
        }
        _ => Ok(None),
    }
}

fn find_struct_for_type<'a>(
    target_type: &str,
    declset: &'a DeclSetValue,
    program: &'a ir::ResolvedProgram,
) -> Option<&'a StructDef> {
    for type_def in declset.type_definitions.iter().rev() {
        if let TypeDefDecl::Struct(def) = type_def {
            if def.name == target_type {
                return Some(def);
            }
        }
    }
    resolved_struct_def(program, target_type)
}

fn find_emitted_enum_mut<'a>(
    declset: &'a mut DeclSetValue,
    target_type: &str,
) -> Option<&'a mut parser::EnumDef> {
    for type_def in declset.type_definitions.iter_mut().rev() {
        if let TypeDefDecl::Enum(def) = type_def {
            if def.name == target_type {
                return Some(def);
            }
        }
    }
    None
}

fn type_known_in_declset_or_program(
    target_type: &str,
    declset: &DeclSetValue,
    program: &ir::ResolvedProgram,
) -> bool {
    resolved_type_exists(program, target_type)
        || declset
            .type_definitions
            .iter()
            .any(|type_def| match type_def {
                TypeDefDecl::Struct(def) => def.name == target_type,
                TypeDefDecl::Enum(def) => def.name == target_type,
            })
}

fn ensure_enum_variant_name_available(
    enum_def: &parser::EnumDef,
    variant_name: &str,
    builtin_name: &str,
) -> anyhow::Result<()> {
    if enum_def
        .variants
        .iter()
        .any(|variant| variant.name == variant_name)
    {
        return Err(anyhow::anyhow!(
            "{} target {} already has variant {}",
            builtin_name,
            enum_def.name,
            variant_name
        ));
    }
    Ok(())
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

fn expect_enum_info<'a>(value: &'a CtValue, context: &str) -> anyhow::Result<&'a EnumInfoValue> {
    if let CtValue::EnumInfo(value) = value {
        Ok(value)
    } else {
        Err(anyhow::anyhow!(
            "{} expected EnumInfo, got {}",
            context,
            ct_value_type_name(value)
        ))
    }
}

fn expect_variant_info<'a>(
    value: &'a CtValue,
    context: &str,
) -> anyhow::Result<&'a VariantInfoValue> {
    if let CtValue::VariantInfo(value) = value {
        Ok(value)
    } else {
        Err(anyhow::anyhow!(
            "{} expected VariantInfo, got {}",
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

fn expect_semantic_expr<'a>(
    value: &'a CtValue,
    context: &str,
) -> anyhow::Result<&'a SemanticExprValue> {
    if let CtValue::SemanticExpr(value) = value {
        Ok(value)
    } else {
        Err(anyhow::anyhow!(
            "{} expected SemanticExpr, got {}",
            context,
            ct_value_type_name(value)
        ))
    }
}

fn expect_source_span<'a>(value: &'a CtValue, context: &str) -> anyhow::Result<&'a SourceSpan> {
    if let CtValue::SourceSpan(value) = value {
        Ok(value)
    } else {
        Err(anyhow::anyhow!(
            "{} expected SourceSpan, got {}",
            context,
            ct_value_type_name(value)
        ))
    }
}

fn format_source_span_compact(span: &SourceSpan) -> String {
    let Some(file) = span.file.as_deref() else {
        return "<unknown>".to_string();
    };
    let Some(start_line) = span.start_line else {
        return file.to_string();
    };
    let Some(start_column) = span.start_column else {
        return format!("{file}:{start_line}");
    };
    format!("{file}:{start_line}:{start_column}")
}

fn values_equal(left: &CtValue, right: &CtValue) -> anyhow::Result<bool> {
    match (left, right) {
        (CtValue::Bool(a), CtValue::Bool(b)) => Ok(a == b),
        (CtValue::I32(a), CtValue::I32(b)) => Ok(a == b),
        (CtValue::I64(a), CtValue::I64(b)) => Ok(a == b),
        (CtValue::FP32(a), CtValue::FP32(b)) => Ok(a == b),
        (CtValue::FP64(a), CtValue::FP64(b)) => Ok(a == b),
        (CtValue::Type(a), CtValue::Type(b)) => Ok(a == b),
        (CtValue::SemanticExpr(a), CtValue::SemanticExpr(b)) => Ok(a == b),
        _ => Err(anyhow::anyhow!(
            "unsupported equality in comptime evaluator for {} and {}",
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
        CtValue::FP32(_) => "FP32".to_string(),
        CtValue::FP64(_) => "FP64".to_string(),
        CtValue::String(_) => "String".to_string(),
        CtValue::Type(_) => "Type".to_string(),
        CtValue::Struct { type_name, .. } => type_name.clone(),
        CtValue::Enum { type_name, .. } => type_name.clone(),
        CtValue::StructInfo(_) => "StructInfo".to_string(),
        CtValue::FieldInfo(_) => "FieldInfo".to_string(),
        CtValue::EnumInfo(_) => "EnumInfo".to_string(),
        CtValue::VariantInfo(_) => "VariantInfo".to_string(),
        CtValue::DeclSet(_) => "DeclSet".to_string(),
        CtValue::SemanticExpr(_) => "SemanticExpr".to_string(),
        CtValue::SourceSpan(_) => "SourceSpan".to_string(),
        CtValue::Option { concrete_type, .. } => concrete_type.clone(),
    }
}

fn ct_value_matches_type(value: &CtValue, ty: &str) -> bool {
    match value {
        CtValue::Option {
            inner_type,
            concrete_type,
            ..
        } => {
            let expected = normalize_type_alias(ty);
            let concrete = normalize_type_alias(concrete_type);
            expected == concrete || expected == format!("Option[{inner_type}]")
        }
        _ => normalize_type_alias(&ct_value_type_name(value)) == normalize_type_alias(ty),
    }
}

fn normalize_type_alias(ty: &str) -> String {
    match ty {
        "Int" => "I32".to_string(),
        "PtrInt" => "I64".to_string(),
        _ => ty.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::execute_comptime_applies;
    use crate::ir::{self, ResolveMode};
    use crate::{parser, tokenizer};

    fn parse_source(source: &str) -> parser::Ast {
        let tokens = tokenizer::tokenize(source.to_string()).expect("tokenize source");
        parser::parse(tokens).expect("parse source")
    }

    fn execute(ast: &mut parser::Ast) -> anyhow::Result<()> {
        if ast.comptime_applies.is_empty() {
            return Ok(());
        }
        let bootstrap = ir::resolve_with_mode(ast.clone(), ResolveMode::BootstrapComptime)
            .expect("bootstrap resolve");
        execute_comptime_applies(ast, bootstrap)
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
        execute(&mut ast).expect("execute comptime applies");
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
	ds = DeclSet.new()
	s = T.as_struct_opt()
	if s.is_some() {
		info = s.unwrap()
		if info.field_count() >= 2 {
			f = info.field_at(1)
			if f.is_some() {
				second = f.unwrap()
				if second.ty() == I32 {
					new_name = T.name().concat("PositiveSecond")
					ds2 = ds.add_derived_struct(info, new_name)
					return ds2.add_invariant_field_gt_i32(
						Type.resolve(new_name),
						"second field must be > 0",
						second.name(),
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

        execute(&mut ast).expect("execute comptime applies");
        assert!(ast.type_definitions.iter().any(|def| {
            matches!(
                def,
                parser::TypeDefDecl::Struct(def) if def.name == "CounterPositiveSecond"
            )
        }));
        assert!(ast.invariants.iter().any(
            |inv| inv.parameters.len() == 1 && inv.parameters[0].ty == "CounterPositiveSecond"
        ));
    }

    #[test]
    fn apply_order_is_deterministic() {
        let mut ast = parse_source(
            r#"
struct Counter {
	value: I32,
}

comptime fun derive(T: Type) -> DeclSet {
	ds = DeclSet.new()
	s = T.as_struct_opt()
	if s.is_some() {
		info = s.unwrap()
		return ds.add_derived_struct(info, T.name().concat("X"))
	}
	return ds
}

comptime apply derive(Counter)
comptime apply derive(CounterX)
"#,
        );
        execute(&mut ast).expect("execute comptime applies");
        assert!(ast.type_definitions.iter().any(|def| {
            matches!(def, parser::TypeDefDecl::Struct(def) if def.name == "CounterX")
        }));
        assert!(ast.type_definitions.iter().any(|def| {
            matches!(def, parser::TypeDefDecl::Struct(def) if def.name == "CounterXX")
        }));
    }

    #[test]
    fn enum_reflection_builtins_work() {
        let mut ast = parse_source(
            r#"
struct Payload {
	value: I32,
}

enum Token {
	Int: I32,
	Plus,
	Wrapped: Payload,
}

comptime fun reflect(T: Type) -> DeclSet {
	ds = DeclSet.new()
	assert(T.is_enum())
	assert(!Type.resolve("Payload").is_enum())
	assert(!T.as_struct_opt().is_some())
	e = T.as_enum_opt()
	assert(e.is_some())
	info = e.unwrap()
	assert(info.variant_count() == 3)
	out_name = T.name().concat("Tags")
	ds = ds.add_empty_enum(out_name)
	first = info.variant_at(0)
	assert(first.is_some())
	v0 = first.unwrap()
	p0 = v0.payload_type_opt()
	assert(p0.is_some())
	assert(p0.unwrap() == I32)
	second = info.variant_at(1)
	assert(second.is_some())
	v1 = second.unwrap()
	assert(!v1.payload_type_opt().is_some())
	third = info.variant_at(2)
	assert(third.is_some())
	v2 = third.unwrap()
	p2 = v2.payload_type_opt()
	assert(p2.is_some())
	assert(p2.unwrap() == Payload)
	neg_one = 0 - 1
	assert(!info.variant_at(neg_one).is_some())
	assert(!info.variant_at(3).is_some())
	i = 0
	while i < info.variant_count() {
		v = info.variant_at(i).unwrap()
		ds = ds.add_enum_tag_variant(out_name, v.name())
		i = i + 1
	}
	return ds
}

comptime apply reflect(Token)
"#,
        );

        execute(&mut ast).expect("execute comptime applies");
        let emitted = ast
            .type_definitions
            .iter()
            .find_map(|def| match def {
                parser::TypeDefDecl::Enum(def) if def.name == "TokenTags" => Some(def),
                _ => None,
            })
            .expect("missing TokenTags enum");
        assert_eq!(emitted.variants.len(), 3);
        assert_eq!(emitted.variants[0].name, "Int");
        assert_eq!(emitted.variants[0].payload_ty, None);
        assert_eq!(emitted.variants[1].name, "Plus");
        assert_eq!(emitted.variants[1].payload_ty, None);
        assert_eq!(emitted.variants[2].name, "Wrapped");
        assert_eq!(emitted.variants[2].payload_ty, None);
    }

    #[test]
    fn enum_payload_emission_builtin_works() {
        let mut ast = parse_source(
            r#"
struct Payload {
	value: I32,
}

enum Token {
	Int: I32,
	Plus,
	Wrapped: Payload,
}

comptime fun clone_enum(T: Type) -> DeclSet {
	ds = DeclSet.new()
	e = T.as_enum_opt().unwrap()
	out_name = T.name().concat("Clone")
	ds = ds.add_empty_enum(out_name)
	i = 0
	while i < e.variant_count() {
		v = e.variant_at(i).unwrap()
		payload_opt = v.payload_type_opt()
		if payload_opt.is_some() {
			ds = ds.add_enum_payload_variant(out_name, v.name(), payload_opt.unwrap())
		} else {
			ds = ds.add_enum_tag_variant(out_name, v.name())
		}
		i = i + 1
	}
	return ds
}

comptime apply clone_enum(Token)
"#,
        );

        execute(&mut ast).expect("execute comptime applies");
        let emitted = ast
            .type_definitions
            .iter()
            .find_map(|def| match def {
                parser::TypeDefDecl::Enum(def) if def.name == "TokenClone" => Some(def),
                _ => None,
            })
            .expect("missing TokenClone enum");
        assert_eq!(emitted.variants.len(), 3);
        assert_eq!(emitted.variants[0].name, "Int");
        assert_eq!(emitted.variants[0].payload_ty.as_deref(), Some("I32"));
        assert_eq!(emitted.variants[1].name, "Plus");
        assert_eq!(emitted.variants[1].payload_ty, None);
        assert_eq!(emitted.variants[2].name, "Wrapped");
        assert_eq!(emitted.variants[2].payload_ty.as_deref(), Some("Payload"));
    }

    #[test]
    fn stdlib_enum_tags_helper_is_available() {
        let mut ast = parse_source(
            r#"
enum Token {
	Int: I32,
	Plus,
	Wrapped: String,
}

comptime apply derive_enum_tags(Token)
"#,
        );

        execute(&mut ast).expect("execute comptime applies");
        let emitted = ast
            .type_definitions
            .iter()
            .find_map(|def| match def {
                parser::TypeDefDecl::Enum(def) if def.name == "TokenTags" => Some(def),
                _ => None,
            })
            .expect("missing TokenTags enum");
        assert_eq!(emitted.variants.len(), 3);
        assert_eq!(emitted.variants[0].name, "Int");
        assert_eq!(emitted.variants[0].payload_ty, None);
        assert_eq!(emitted.variants[1].name, "Plus");
        assert_eq!(emitted.variants[1].payload_ty, None);
        assert_eq!(emitted.variants[2].name, "Wrapped");
        assert_eq!(emitted.variants[2].payload_ty, None);
    }

    #[test]
    fn provenance_some_none_behavior() {
        let mut ast = parse_source(
            r#"
struct Counter {
	value: I32,
}

comptime fun meta_probe(T: Type) -> DeclSet {
	meta_from_param = Meta.expr_opt(T)
	assert(!meta_from_param.is_some())
	assert(Meta.expr_opt(Type.resolve("I32")).is_some())
	return DeclSet.new()
}

comptime apply meta_probe(Counter)
"#,
        );
        execute(&mut ast).expect("execute comptime applies");
    }

    #[test]
    fn bad_emit_fails_closed() {
        let mut ast = parse_source(
            r#"
comptime fun bad(T: Type) -> DeclSet {
	ds = DeclSet.new()
	s = T.as_struct_opt()
	info = s.unwrap()
	return ds.add_derived_struct(info, "X")
}

comptime apply bad(I32)
"#,
        );
        let err = execute(&mut ast).expect_err("bad emit should fail");
        assert!(err
            .to_string()
            .contains("precondition 0 of StructInfoOpt__unwrap evaluated to false"));
    }

    #[test]
    fn checked_i32_overflow_fails_closed() {
        let mut ast = parse_source(
            r#"
comptime fun overflow(T: Type) -> DeclSet {
	x = 2147483647 + 1
	return DeclSet.new()
}

comptime apply overflow(I32)
"#,
        );
        let err = execute(&mut ast).expect_err("overflow should fail");
        assert!(err
            .to_string()
            .contains("comptime integer overflow in 2147483647 + 1"));
    }

    #[test]
    fn checked_i32_divide_by_zero_fails_closed() {
        let mut ast = parse_source(
            r#"
comptime fun div_zero(T: Type) -> DeclSet {
	x = 1 / 0
	return DeclSet.new()
}

comptime apply div_zero(I32)
"#,
        );
        let err = execute(&mut ast).expect_err("division by zero should fail");
        assert!(err
            .to_string()
            .contains("comptime division by zero in 1 / 0"));
    }

    #[test]
    fn checked_i32_min_over_neg_one_fails_closed() {
        let mut ast = parse_source(
            r#"
comptime fun div_min(T: Type) -> DeclSet {
	min = 0 - 2147483647
	min = min - 1
	neg_one = 0 - 1
	x = min / neg_one
	return DeclSet.new()
}

comptime apply div_min(I32)
"#,
        );
        let err = execute(&mut ast).expect_err("min / -1 should fail");
        assert!(err
            .to_string()
            .contains("comptime integer overflow in -2147483648 / -1"));
    }

    #[test]
    fn builtin_operator_trait_calls_work_for_i32_in_comptime() {
        let mut ast = parse_source(
            r#"
comptime fun ops(T: Type) -> DeclSet {
	sum = Addition.add(1, 2)
	diff = Subtraction.sub(sum, 1)
	product = Multiplication.mul(diff, 3)
	quotient = Division.div(product, 2)
	cmp = Comparison.compare(quotient, 3)
	assert(Equality.equals(quotient, 3))
	assert(cmp == 0)
	return DeclSet.new()
}

comptime apply ops(I32)
"#,
        );
        execute(&mut ast).expect("builtin operator trait calls should work");
    }

    #[test]
    fn resolved_operator_impl_calls_work_in_comptime() {
        let mut ast = parse_source(
            r#"
struct Counter {
	value: I32,
}

impl Equality for Counter {
	fun equals(a: Counter, b: Counter) -> Bool {
		return a.value == b.value
	}
}

comptime fun check(T: Type) -> DeclSet {
	same = Counter struct { value: 7 } == Counter struct { value: 7 }
	assert(same)
	return DeclSet.new()
}

comptime apply check(I32)
"#,
        );
        execute(&mut ast).expect("resolved operator impl calls should work in comptime");
    }

    #[test]
    fn ordinary_helper_preconditions_and_custom_operator_impls_work_in_comptime() {
        let mut ast = parse_source(
            r#"
struct Counter {
	value: I32,
}

impl Equality for Counter {
	fun equals(a: Counter, b: Counter) -> Bool {
		return a.value == b.value
	}
}

fun require_same(v: Counter) -> Counter pre {
	v == Counter struct { value: 7 }
} {
	return v
}

comptime fun derive(T: Type) -> DeclSet {
	c = require_same(Counter struct { value: 7 })
	assert(c == Counter struct { value: 7 })
	return DeclSet.new()
}

comptime apply derive(Counter)
"#,
        );

        execute(&mut ast).expect("ordinary helper preconditions should execute in comptime");
    }

    #[test]
    fn print_and_print_str_are_ignored_in_comptime() {
        let mut ast = parse_source(
            r#"
fun log_value(v: I32) -> I32 {
	return print(v)
}

fun log_text(s: String) -> I32 {
	return print_str(s)
}

comptime fun debug(T: Type) -> DeclSet {
	assert(log_value(7) == 0)
	assert(log_text("hello") == 0)
	return DeclSet.new()
}

comptime apply debug(I32)
"#,
        );

        execute(&mut ast).expect("print-style output should be ignored in comptime");
    }

    #[test]
    fn later_applies_see_types_emitted_by_earlier_applies() {
        let mut ast = parse_source(
            r#"
struct Counter {
	value: I32,
}

comptime fun emit_x(T: Type) -> DeclSet {
	return DeclSet.new().add_derived_struct(T.as_struct_opt().unwrap(), T.name().concat("X"))
}

comptime fun emit_y(T: Type) -> DeclSet {
	return DeclSet.new().add_derived_struct(T.as_struct_opt().unwrap(), T.name().concat("Y"))
}

comptime apply emit_x(Counter)
comptime apply emit_y(CounterX)
"#,
        );

        execute(&mut ast).expect("later applies should see earlier emitted types");
        assert!(ast.type_definitions.iter().any(|def| {
            matches!(def, parser::TypeDefDecl::Struct(def) if def.name == "CounterX")
        }));
        assert!(ast.type_definitions.iter().any(|def| {
            matches!(def, parser::TypeDefDecl::Struct(def) if def.name == "CounterXY")
        }));
    }
}
