//! Type-checking and IR generation.

use std::collections::{HashMap, HashSet};

use serde::Serialize;
use tracing::trace;

use crate::ast_paths::{local_precondition_key, local_statement_key};
use crate::ast_walk::{self, AstPathStyle};
use crate::builtins::BuiltInType;
use crate::flat_imports;
use crate::parser::{self, Ast, Expression, Literal, StructDef, UnaryOp};
pub use crate::source_span::SourceSpan;
use crate::symbol_keys::{
    trait_impl_function_name, trait_impl_method_key, trait_impl_target_key, trait_method_key,
};

const LEGACY_INVARIANT_PREFIX: &str = "__struct__";
const LEGACY_INVARIANT_SUFFIX: &str = "__invariant";
const LEGACY_INVARIANT_KEY: &str = "legacy";
const MODEL_INVARIANT_PREFIX: &str = "__model__invariant__";
const MODEL_INVARIANT_SIDE_EFFECT_BUILTINS: [&str; 9] = [
    "load_u8",
    "load_i32",
    "load_i64",
    "load_bool",
    "store_u8",
    "store_i32",
    "store_i64",
    "store_bool",
    "print",
];
const RESERVED_BUILTIN_FUNCTION_NAMES: [&str; 2] = ["prove", "assert"];
const SEMANTIC_BUILTIN_TYPES: [&str; 8] = [
    "Type",
    "DeclSet",
    "SemanticExpr",
    "SourceSpan",
    "StructInfo",
    "FieldInfo",
    "EnumInfo",
    "VariantInfo",
];
const META_EXPR_OPT_FUNCTION: &str = "Meta__expr_opt";
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
const EMIT_DECLSET_NEW_INTRINSIC: &str = "__intrinsic__emit__declset_new";
const EMIT_ADD_EMPTY_ENUM_INTRINSIC: &str = "__intrinsic__emit__declset_add_empty_enum";
const EMIT_ADD_ENUM_TAG_VARIANT_INTRINSIC: &str = "__intrinsic__emit__declset_add_enum_tag_variant";
const EMIT_ADD_ENUM_PAYLOAD_VARIANT_INTRINSIC: &str =
    "__intrinsic__emit__declset_add_enum_payload_variant";
const EMIT_ADD_DERIVED_STRUCT_INTRINSIC: &str = "__intrinsic__emit__declset_add_derived_struct";
const EMIT_ADD_INVARIANT_FIELD_GT_I32_INTRINSIC: &str =
    "__intrinsic__emit__declset_add_invariant_field_gt_i32";
const SEMANTIC_EMISSION_BUILTINS: [&str; 6] = [
    EMIT_DECLSET_NEW_INTRINSIC,
    EMIT_ADD_EMPTY_ENUM_INTRINSIC,
    EMIT_ADD_ENUM_TAG_VARIANT_INTRINSIC,
    EMIT_ADD_ENUM_PAYLOAD_VARIANT_INTRINSIC,
    EMIT_ADD_DERIVED_STRUCT_INTRINSIC,
    EMIT_ADD_INVARIANT_FIELD_GT_I32_INTRINSIC,
];
const SEMANTIC_INTROSPECTION_BUILTINS: [&str; 18] = [
    META_EXPR_OPT_FUNCTION,
    META_TYPE_NAME_INTRINSIC,
    META_RESOLVE_TYPE_INTRINSIC,
    META_EXPR_METADATA_INTRINSIC,
    META_DEFINITION_LOCATION_INTRINSIC,
    META_IS_STRUCT_INTRINSIC,
    META_IS_ENUM_INTRINSIC,
    META_AS_STRUCT_OPT_INTRINSIC,
    META_AS_ENUM_OPT_INTRINSIC,
    META_STRUCT_FIELD_COUNT_INTRINSIC,
    META_STRUCT_FIELD_AT_INTRINSIC,
    META_ENUM_VARIANT_COUNT_INTRINSIC,
    META_ENUM_VARIANT_AT_INTRINSIC,
    META_FIELD_NAME_INTRINSIC,
    META_FIELD_TYPE_INTRINSIC,
    META_VARIANT_NAME_INTRINSIC,
    META_VARIANT_PAYLOAD_TYPE_OPT_INTRINSIC,
    META_SOURCE_SPAN_DISPLAY_INTRINSIC,
];

fn normalize_numeric_alias(ty: &str) -> &str {
    match ty {
        "Int" => "I32",
        "PtrInt" => "I64",
        _ => ty,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BuiltinTraitOperator {
    Addition,
    Subtraction,
    Multiplication,
    Division,
    Equality,
    Comparison,
}

impl BuiltinTraitOperator {
    fn from_trait_method(trait_name: &str, method_name: &str) -> Option<Self> {
        match (trait_name, method_name) {
            ("Addition", "add") => Some(Self::Addition),
            ("Subtraction", "sub") => Some(Self::Subtraction),
            ("Multiplication", "mul") => Some(Self::Multiplication),
            ("Division", "div") => Some(Self::Division),
            ("Equality", "equals") => Some(Self::Equality),
            ("Comparison", "compare") => Some(Self::Comparison),
            _ => None,
        }
    }

    fn from_binary_op(op: parser::Op) -> Option<Self> {
        match op {
            parser::Op::Add => Some(Self::Addition),
            parser::Op::Sub => Some(Self::Subtraction),
            parser::Op::Mul => Some(Self::Multiplication),
            parser::Op::Div => Some(Self::Division),
            parser::Op::Eq | parser::Op::Neq => Some(Self::Equality),
            parser::Op::Lt | parser::Op::Gt | parser::Op::Le | parser::Op::Ge => {
                Some(Self::Comparison)
            }
            parser::Op::And | parser::Op::Or => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TraitCallTarget {
    Function(String),
    BuiltinOperator(BuiltinTraitOperator),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum BinaryOperatorResolution {
    Builtin {
        return_type: TypeRef,
    },
    TraitCall {
        target_function: String,
        return_type: TypeRef,
    },
    ComparisonTraitCall {
        target_function: String,
    },
}

fn is_builtin_scalar_arithmetic_type(ty: &str) -> bool {
    matches!(
        normalize_numeric_alias(ty),
        "U8" | "I32" | "I64" | "FP32" | "FP64"
    )
}

fn is_builtin_scalar_equality_type(ty: &str) -> bool {
    matches!(
        normalize_numeric_alias(ty),
        "Bool" | "U8" | "I32" | "I64" | "FP32" | "FP64"
    )
}

fn is_builtin_semantic_equality_type(ty: &str) -> bool {
    matches!(ty, "Type" | "SemanticExpr")
}

fn is_builtin_trait_operator_for_type(operator: BuiltinTraitOperator, ty: &str) -> bool {
    match operator {
        BuiltinTraitOperator::Addition
        | BuiltinTraitOperator::Subtraction
        | BuiltinTraitOperator::Multiplication
        | BuiltinTraitOperator::Division
        | BuiltinTraitOperator::Comparison => is_builtin_scalar_arithmetic_type(ty),
        BuiltinTraitOperator::Equality => is_builtin_scalar_equality_type(ty),
    }
}

fn is_reserved_builtin_operator_impl(trait_name: &str, for_type: &str) -> bool {
    match trait_name {
        "Addition" | "Subtraction" | "Multiplication" | "Division" | "Comparison" => {
            is_builtin_scalar_arithmetic_type(for_type)
        }
        "Equality" => is_builtin_scalar_equality_type(for_type),
        _ => false,
    }
}

fn seed_builtin_operator_trait_impl_targets(
    declared_traits: &HashMap<String, Vec<TraitMethodSignature>>,
    trait_impl_targets: &mut HashSet<String>,
) {
    for (trait_name, concrete_types) in [
        (
            "Addition",
            &["U8", "I32", "Int", "I64", "PtrInt", "FP32", "FP64"][..],
        ),
        (
            "Subtraction",
            &["U8", "I32", "Int", "I64", "PtrInt", "FP32", "FP64"][..],
        ),
        (
            "Multiplication",
            &["U8", "I32", "Int", "I64", "PtrInt", "FP32", "FP64"][..],
        ),
        (
            "Division",
            &["U8", "I32", "Int", "I64", "PtrInt", "FP32", "FP64"][..],
        ),
        (
            "Comparison",
            &["U8", "I32", "Int", "I64", "PtrInt", "FP32", "FP64"][..],
        ),
        (
            "Equality",
            &["Bool", "U8", "I32", "Int", "I64", "PtrInt", "FP32", "FP64"][..],
        ),
    ] {
        if !declared_traits.contains_key(trait_name) {
            continue;
        }
        for concrete_type in concrete_types {
            trait_impl_targets.insert(trait_impl_target_key(trait_name, concrete_type));
        }
    }
}

pub(crate) fn resolve_trait_call_target(
    trait_name: &str,
    method_name: &str,
    args: &[Expression],
    var_types: &HashMap<String, TypeRef>,
    fns: &HashMap<String, FunctionSignature>,
    type_definitions: &HashMap<String, TypeDef>,
    trait_method_signatures: &HashMap<String, TraitMethodSignature>,
    trait_impl_methods: &HashMap<String, String>,
) -> anyhow::Result<(TraitCallTarget, TypeRef)> {
    let trait_method = trait_method_signatures
        .get(&trait_method_key(trait_name, method_name))
        .ok_or_else(|| {
            anyhow::anyhow!(
                "unsupported trait call {}.{}(...): expected a declared trait method",
                trait_name,
                method_name
            )
        })?;
    if args.is_empty() {
        return Err(anyhow::anyhow!(
            "trait call {}.{} requires at least one argument for Self",
            trait_name,
            method_name
        ));
    }
    if args.len() != trait_method.parameter_types.len() {
        return Err(anyhow::anyhow!(
            "trait call {}.{} expects {} arguments, got {}",
            trait_name,
            method_name,
            trait_method.parameter_types.len(),
            args.len()
        ));
    }
    let self_type = get_expression_type(
        &args[0],
        var_types,
        fns,
        type_definitions,
        trait_method_signatures,
        trait_impl_methods,
    )?;
    for (index, (argument, param_ty)) in args
        .iter()
        .zip(trait_method.parameter_types.iter())
        .enumerate()
    {
        let argument_type = get_expression_type(
            argument,
            var_types,
            fns,
            type_definitions,
            trait_method_signatures,
            trait_impl_methods,
        )?;
        let expected_type = replace_self_type(param_ty, &self_type);
        if normalize_numeric_alias(&argument_type) != normalize_numeric_alias(&expected_type) {
            return Err(anyhow::anyhow!(
                "trait call {}.{} argument {} mismatch: expected {}, got {}",
                trait_name,
                method_name,
                index,
                expected_type,
                argument_type
            ));
        }
    }

    let return_type = replace_self_type(&trait_method.return_type, &self_type);
    if let Some(operator) = BuiltinTraitOperator::from_trait_method(trait_name, method_name) {
        if is_builtin_trait_operator_for_type(operator, &self_type) {
            return Ok((TraitCallTarget::BuiltinOperator(operator), return_type));
        }
    }

    let impl_key = trait_impl_method_key(trait_name, &self_type, method_name);
    let target_function = trait_impl_methods.get(&impl_key).ok_or_else(|| {
        anyhow::anyhow!(
            "missing impl {} for {} required by trait call {}.{}",
            trait_name,
            self_type,
            trait_name,
            method_name
        )
    })?;

    Ok((
        TraitCallTarget::Function(target_function.clone()),
        return_type,
    ))
}

fn resolve_binary_operator(
    op: parser::Op,
    left: &Expression,
    right: &Expression,
    var_types: &HashMap<String, TypeRef>,
    fns: &HashMap<String, FunctionSignature>,
    type_definitions: &HashMap<String, TypeDef>,
    trait_method_signatures: &HashMap<String, TraitMethodSignature>,
    trait_impl_methods: &HashMap<String, String>,
) -> anyhow::Result<BinaryOperatorResolution> {
    let left_type = get_expression_type(
        left,
        var_types,
        fns,
        type_definitions,
        trait_method_signatures,
        trait_impl_methods,
    )?;
    let right_type = get_expression_type(
        right,
        var_types,
        fns,
        type_definitions,
        trait_method_signatures,
        trait_impl_methods,
    )?;
    let left_norm = normalize_numeric_alias(&left_type);
    let right_norm = normalize_numeric_alias(&right_type);

    match op {
        parser::Op::And | parser::Op::Or => {
            if left_norm == "Bool" && right_norm == "Bool" {
                return Ok(BinaryOperatorResolution::Builtin {
                    return_type: "Bool".to_string(),
                });
            }
            return Err(anyhow::anyhow!(
                "expected Bool operands for {:?}, but got {:?} and {:?}",
                op,
                left_type,
                right_type
            ));
        }
        parser::Op::Add | parser::Op::Sub | parser::Op::Mul | parser::Op::Div => {
            if left_norm == right_norm && is_builtin_scalar_arithmetic_type(left_norm) {
                return Ok(BinaryOperatorResolution::Builtin {
                    return_type: left_norm.to_string(),
                });
            }
        }
        parser::Op::Eq | parser::Op::Neq => {
            if left_norm != right_norm {
                return Err(anyhow::anyhow!(
                    "expected both operands of {:?} to have the same type, but got {:?} and {:?}",
                    op,
                    left_type,
                    right_type
                ));
            }
            if is_builtin_scalar_equality_type(left_norm)
                || is_builtin_semantic_equality_type(left_norm)
            {
                return Ok(BinaryOperatorResolution::Builtin {
                    return_type: "Bool".to_string(),
                });
            }
        }
        parser::Op::Lt | parser::Op::Gt | parser::Op::Le | parser::Op::Ge => {
            if left_norm == right_norm && is_builtin_scalar_arithmetic_type(left_norm) {
                return Ok(BinaryOperatorResolution::Builtin {
                    return_type: "Bool".to_string(),
                });
            }
        }
    }

    let Some(operator_trait) = BuiltinTraitOperator::from_binary_op(op) else {
        unreachable!("bool operators are handled above");
    };
    if left_norm != right_norm {
        return Err(anyhow::anyhow!(
            "expected both operands of {:?} to have the same type, but got {:?} and {:?}",
            op,
            left_type,
            right_type
        ));
    }

    let trait_name = match operator_trait {
        BuiltinTraitOperator::Addition => "Addition",
        BuiltinTraitOperator::Subtraction => "Subtraction",
        BuiltinTraitOperator::Multiplication => "Multiplication",
        BuiltinTraitOperator::Division => "Division",
        BuiltinTraitOperator::Equality => "Equality",
        BuiltinTraitOperator::Comparison => "Comparison",
    };
    let method_name = match operator_trait {
        BuiltinTraitOperator::Addition => "add",
        BuiltinTraitOperator::Subtraction => "sub",
        BuiltinTraitOperator::Multiplication => "mul",
        BuiltinTraitOperator::Division => "div",
        BuiltinTraitOperator::Equality => "equals",
        BuiltinTraitOperator::Comparison => "compare",
    };

    let impl_key = trait_impl_method_key(trait_name, left_norm, method_name);
    if let Some(target_function) = trait_impl_methods.get(&impl_key) {
        return Ok(match operator_trait {
            BuiltinTraitOperator::Comparison => BinaryOperatorResolution::ComparisonTraitCall {
                target_function: target_function.clone(),
            },
            BuiltinTraitOperator::Addition
            | BuiltinTraitOperator::Subtraction
            | BuiltinTraitOperator::Multiplication
            | BuiltinTraitOperator::Division => BinaryOperatorResolution::TraitCall {
                target_function: target_function.clone(),
                return_type: left_type,
            },
            BuiltinTraitOperator::Equality => BinaryOperatorResolution::TraitCall {
                target_function: target_function.clone(),
                return_type: "Bool".to_string(),
            },
        });
    }

    if matches!(operator_trait, BuiltinTraitOperator::Equality) {
        return match type_definitions.get(left_norm) {
            Some(TypeDef::Struct(_)) => Ok(BinaryOperatorResolution::Builtin {
                return_type: "Bool".to_string(),
            }),
            Some(TypeDef::Enum(enum_def)) if !enum_def.is_tagged_union => {
                Ok(BinaryOperatorResolution::Builtin {
                    return_type: "Bool".to_string(),
                })
            }
            Some(TypeDef::Enum(enum_def)) => Err(anyhow::anyhow!(
                "direct {:?} comparison is not supported for tagged enum {} without an Equality impl",
                op,
                enum_def.name
            )),
            _ => Err(anyhow::anyhow!(
                "missing impl Equality for {} required by operator {:?}",
                left_type,
                op
            )),
        };
    }

    Err(anyhow::anyhow!(
        "missing impl {} for {} required by operator {:?}",
        trait_name,
        left_type,
        op
    ))
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub enum TypeDef {
    Struct(StructDef),
    Enum(EnumTypeDef),
    BuiltIn(BuiltInType),
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct EnumTypeDef {
    pub name: String,
    pub variants: Vec<EnumVariant>,
    pub is_tagged_union: bool,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct EnumVariant {
    pub name: String,
    pub payload_ty: Option<TypeRef>,
    pub tag: u32,
}

#[derive(Clone, Debug, Serialize)]
pub struct ResolvedProgram {
    pub ast: Ast,
    pub type_definitions: HashMap<String, TypeDef>,
    pub function_sigs: HashMap<String, FunctionSignature>,
    pub function_definitions: HashMap<String, FunctionDefinition>,
    pub trait_method_signatures: HashMap<String, TraitMethodSignature>,
    pub trait_impl_methods: HashMap<String, String>,
    pub struct_invariants: HashMap<String, Vec<StructInvariantDefinition>>,
    pub function_preconditions: HashMap<String, Vec<FunctionPreconditionDefinition>>,
    pub model_invariants: Vec<ModelInvariantDefinition>,
    pub comptime_function_definitions: HashMap<String, FunctionDefinition>,
    pub comptime_apply_order: Vec<parser::ComptimeApply>,
    pub semantic_expr_metadata: HashMap<String, SemanticExprMetadata>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ResolveMode {
    BootstrapComptime,
    FinalRuntime,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct SemanticExprMetadata {
    pub id: String,
    pub ty: Option<String>,
    pub source_span: Option<SourceSpan>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct StructInvariantDefinition {
    pub struct_name: String,
    pub function_name: String,
    pub key: String,
    pub identifier: Option<String>,
    pub display_name: String,
    pub source_span: Option<SourceSpan>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ModelInvariantDefinition {
    pub function_name: String,
    pub key: String,
    pub identifier: Option<String>,
    pub display_name: String,
    pub source_span: Option<SourceSpan>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct FunctionPreconditionDefinition {
    pub owner_function_name: String,
    pub helper_function_name: String,
    pub clause_ordinal: usize,
    pub source_span: Option<SourceSpan>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct TraitMethodSignature {
    pub trait_name: String,
    pub method_name: String,
    pub parameter_types: Vec<String>,
    pub return_type: String,
}

impl ResolvedProgram {
    fn expression_type(
        &self,
        expr: &Expression,
        var_types: &HashMap<String, TypeRef>,
    ) -> anyhow::Result<TypeRef> {
        get_expression_type(
            expr,
            var_types,
            &self.function_sigs,
            &self.type_definitions,
            &self.trait_method_signatures,
            &self.trait_impl_methods,
        )
    }

    fn type_check(&self, func_def: &FunctionDefinition) -> anyhow::Result<()> {
        let mut var_types: HashMap<String, TypeRef> = HashMap::new();
        for param in &func_def.sig.parameters {
            var_types.insert(param.name.clone(), param.ty.clone());
        }
        if self
            .comptime_function_definitions
            .contains_key(&func_def.name)
        {
            for type_name in self.type_definitions.keys() {
                var_types.insert(type_name.clone(), "Type".to_string());
            }
        }

        for (clause_ordinal, clause) in func_def.preconditions.iter().enumerate() {
            let clause_type = self.expression_type(clause, &var_types)?;
            if clause_type != "Bool" {
                return Err(anyhow::anyhow!(
                    "function {} precondition {} must be Bool, got {}",
                    func_def.name,
                    clause_ordinal,
                    clause_type
                ));
            }
        }

        let mut return_type = None;
        for statement in &func_def.body {
            self.type_check_statement(statement, &mut var_types, &mut return_type)?;
        }

        if let Some(inferred) = return_type {
            let declared = &func_def.sig.return_type;
            if normalize_numeric_alias(&inferred) != normalize_numeric_alias(declared) {
                return Err(anyhow::anyhow!(
                    "function {} return type mismatch: declared {}, inferred {}",
                    func_def.name,
                    declared,
                    inferred
                ));
            }
        }

        Ok(())
    }

    fn type_check_statement(
        &self,
        statement: &parser::Statement,
        var_types: &mut HashMap<String, TypeRef>,
        return_type: &mut Option<TypeRef>,
    ) -> anyhow::Result<()> {
        trace!(?statement, "Type checking statement");

        match statement {
            parser::Statement::StructDef { .. } => {}
            parser::Statement::Match { subject, arms } => {
                let subject_type = self.expression_type(subject, var_types)?;
                let enum_def = match self.type_definitions.get(&subject_type) {
                    Some(TypeDef::Enum(enum_def)) => enum_def,
                    _ => {
                        return Err(anyhow::anyhow!(
                            "match subject must be an enum, got {:?}",
                            subject_type
                        ));
                    }
                };

                let mut seen_variants = HashSet::new();
                for arm in arms {
                    match &arm.pattern {
                        parser::MatchPattern::Variant {
                            type_name,
                            variant_name,
                            binder,
                        } => {
                            if type_name != &subject_type {
                                return Err(anyhow::anyhow!(
                                    "match arm type {:?} does not match subject type {:?}",
                                    type_name,
                                    subject_type
                                ));
                            }
                            if !seen_variants.insert(variant_name.clone()) {
                                return Err(anyhow::anyhow!(
                                    "duplicate match arm for variant {}",
                                    variant_name
                                ));
                            }

                            let variant = enum_def
                                .variants
                                .iter()
                                .find(|v| v.name == *variant_name)
                                .ok_or_else(|| {
                                    anyhow::anyhow!(
                                        "unknown variant {} for enum {}",
                                        variant_name,
                                        enum_def.name
                                    )
                                })?;

                            match (&variant.payload_ty, binder) {
                                (Some(payload_ty), Some(binder_name)) => {
                                    let mut scoped_var_types = var_types.clone();
                                    scoped_var_types
                                        .insert(binder_name.clone(), payload_ty.clone());
                                    for statement in &arm.body {
                                        self.type_check_statement(
                                            statement,
                                            &mut scoped_var_types,
                                            return_type,
                                        )?;
                                    }
                                }
                                (Some(_), None) => {
                                    return Err(anyhow::anyhow!(
                                        "match arm for payload variant {} must bind a payload",
                                        variant_name
                                    ));
                                }
                                (None, Some(_)) => {
                                    return Err(anyhow::anyhow!(
                                        "match arm for non-payload variant {} cannot bind a payload",
                                        variant_name
                                    ));
                                }
                                (None, None) => {
                                    let mut scoped_var_types = var_types.clone();
                                    for statement in &arm.body {
                                        self.type_check_statement(
                                            statement,
                                            &mut scoped_var_types,
                                            return_type,
                                        )?;
                                    }
                                }
                            }
                        }
                    }
                }

                let missing = enum_def
                    .variants
                    .iter()
                    .filter(|v| !seen_variants.contains(&v.name))
                    .map(|v| v.name.clone())
                    .collect::<Vec<_>>();
                if !missing.is_empty() {
                    return Err(anyhow::anyhow!(
                        "non-exhaustive match on {}: missing variants {:?}",
                        enum_def.name,
                        missing
                    ));
                }
            }
            parser::Statement::Conditional {
                condition,
                body,
                else_body,
            } => {
                let condition_type = self.expression_type(condition, var_types)?;
                if condition_type != "Bool" {
                    return Err(anyhow::anyhow!(
                        "expected condition to be of type Bool, but got {:?}",
                        condition_type
                    ));
                }
                for statement in body {
                    self.type_check_statement(statement, var_types, return_type)?;
                }
                if let Some(else_body) = else_body {
                    for statement in else_body {
                        self.type_check_statement(statement, var_types, return_type)?;
                    }
                }
            }
            parser::Statement::Prove { condition } => {
                let condition_type = self.expression_type(condition, var_types)?;
                if condition_type != "Bool" {
                    return Err(anyhow::anyhow!(
                        "prove expects Bool condition, got {:?}",
                        condition_type
                    ));
                }
            }
            parser::Statement::Assert { condition } => {
                let condition_type = self.expression_type(condition, var_types)?;
                if condition_type != "Bool" {
                    return Err(anyhow::anyhow!(
                        "assert expects Bool condition, got {:?}",
                        condition_type
                    ));
                }
            }
            parser::Statement::While { condition, body } => {
                let condition_type = self.expression_type(condition, var_types)?;
                if condition_type != "Bool" {
                    return Err(anyhow::anyhow!(
                        "expected condition to be of type Bool, but got {:?}",
                        condition_type
                    ));
                }
                for statement in body {
                    self.type_check_statement(statement, var_types, return_type)?;
                }
            }
            parser::Statement::Assign { variable, value } => {
                let variable_type = self.expression_type(value, var_types)?;
                if variable_type == "Void" {
                    return Err(anyhow::anyhow!(
                        "cannot assign expression of type Void to variable {}",
                        variable
                    ));
                }
                var_types.insert(variable.clone(), variable_type);
            }
            parser::Statement::Return { expr } => {
                let expr_type = self.expression_type(expr, var_types)?;
                if *return_type == None || *return_type == Some(expr_type.clone()) {
                    *return_type = Some(expr_type);
                } else {
                    return Err(anyhow::anyhow!(
                        "mismatched return type: expected {:?}, but got {:?}",
                        return_type,
                        expr_type
                    ));
                }
            }
            parser::Statement::Expression { expr } => {
                trace!("Type-checking expression inside function body: {:#?}", expr);
                let _ = self.expression_type(expr, var_types)?;
            }
        }

        Ok(())
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct FunctionParameter {
    pub name: String,
    pub ty: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct FunctionSignature {
    pub parameters: Vec<FunctionParameter>,
    pub return_type: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub extern_symbol_name: Option<String>,
}

pub type TypeRef = String;

#[derive(Clone, Debug, Serialize)]
pub struct FunctionDefinition {
    pub name: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub preconditions: Vec<parser::Expression>,
    pub body: Vec<parser::Statement>,
    pub sig: FunctionSignature,
    #[serde(skip)]
    #[allow(dead_code)]
    pub source_span: Option<SourceSpan>,
    #[serde(skip)]
    pub local_source_spans: HashMap<String, SourceSpan>,
    #[serde(skip)]
    #[allow(dead_code)]
    pub precondition_source_spans: Vec<SourceSpan>,
}

#[derive(Clone, Debug)]
struct OwnershipLocal {
    ty: TypeRef,
    state: OwnershipBindingState,
    order: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OwnershipBindingState {
    Initialized,
    Moved,
    Uninitialized,
}

#[derive(Clone, Debug, Default)]
struct OwnershipState {
    locals: HashMap<String, OwnershipLocal>,
    next_order: usize,
}

impl OwnershipState {
    fn with_params(parameters: &[FunctionParameter]) -> Self {
        let mut out = OwnershipState::default();
        for parameter in parameters {
            out.locals.insert(
                parameter.name.clone(),
                OwnershipLocal {
                    ty: parameter.ty.clone(),
                    state: OwnershipBindingState::Initialized,
                    order: out.next_order,
                },
            );
            out.next_order += 1;
        }
        out
    }

    fn as_var_types(&self) -> HashMap<String, TypeRef> {
        self.locals
            .iter()
            .map(|(name, local)| (name.clone(), local.ty.clone()))
            .collect()
    }
}

impl ResolvedProgram {
    fn normalize_method_calls(&mut self) -> anyhow::Result<()> {
        let function_names = self
            .function_definitions
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        for function_name in function_names {
            let (sig, preconditions, body) = {
                let definition =
                    self.function_definitions
                        .get(&function_name)
                        .ok_or_else(|| {
                            anyhow::anyhow!("missing function definition {}", function_name)
                        })?;
                (
                    definition.sig.clone(),
                    definition.preconditions.clone(),
                    definition.body.clone(),
                )
            };
            let normalized_preconditions = self.normalize_method_calls_in_preconditions(
                &preconditions,
                &sig.parameters,
                false,
            )?;
            let normalized_body =
                self.normalize_method_calls_in_body(&body, &sig.parameters, false)?;
            let definition = self
                .function_definitions
                .get_mut(&function_name)
                .ok_or_else(|| anyhow::anyhow!("missing function definition {}", function_name))?;
            definition.preconditions = normalized_preconditions;
            definition.body = normalized_body;
        }

        let comptime_function_names = self
            .comptime_function_definitions
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        for function_name in comptime_function_names {
            let (sig, preconditions, body) = {
                let definition = self
                    .comptime_function_definitions
                    .get(&function_name)
                    .ok_or_else(|| {
                        anyhow::anyhow!("missing comptime function definition {}", function_name)
                    })?;
                (
                    definition.sig.clone(),
                    definition.preconditions.clone(),
                    definition.body.clone(),
                )
            };
            let normalized_preconditions = self.normalize_method_calls_in_preconditions(
                &preconditions,
                &sig.parameters,
                true,
            )?;
            let normalized_body =
                self.normalize_method_calls_in_body(&body, &sig.parameters, true)?;
            let definition = self
                .comptime_function_definitions
                .get_mut(&function_name)
                .ok_or_else(|| {
                    anyhow::anyhow!("missing comptime function definition {}", function_name)
                })?;
            definition.preconditions = normalized_preconditions;
            definition.body = normalized_body;
        }

        Ok(())
    }

    fn build_method_normalization_var_types(
        &self,
        parameters: &[FunctionParameter],
        include_type_names: bool,
    ) -> HashMap<String, TypeRef> {
        let mut var_types = HashMap::new();
        for parameter in parameters {
            var_types.insert(parameter.name.clone(), parameter.ty.clone());
        }
        if include_type_names {
            for type_name in self.type_definitions.keys() {
                var_types.insert(type_name.clone(), "Type".to_string());
            }
        }
        var_types
    }

    fn normalize_method_calls_in_preconditions(
        &self,
        preconditions: &[parser::Expression],
        parameters: &[FunctionParameter],
        include_type_names: bool,
    ) -> anyhow::Result<Vec<parser::Expression>> {
        let var_types = self.build_method_normalization_var_types(parameters, include_type_names);
        preconditions
            .iter()
            .map(|expr| self.normalize_method_calls_in_expression(expr, &var_types))
            .collect()
    }

    fn normalize_method_calls_in_body(
        &self,
        body: &[parser::Statement],
        parameters: &[FunctionParameter],
        include_type_names: bool,
    ) -> anyhow::Result<Vec<parser::Statement>> {
        let mut var_types =
            self.build_method_normalization_var_types(parameters, include_type_names);

        body.iter()
            .map(|statement| self.normalize_method_calls_in_statement(statement, &mut var_types))
            .collect()
    }

    fn normalize_method_calls_in_statement(
        &self,
        statement: &parser::Statement,
        var_types: &mut HashMap<String, TypeRef>,
    ) -> anyhow::Result<parser::Statement> {
        match statement {
            parser::Statement::StructDef { .. } => Ok(statement.clone()),
            parser::Statement::Match { subject, arms } => {
                let normalized_subject =
                    self.normalize_method_calls_in_expression(subject, var_types)?;
                let subject_type = self.expression_type(&normalized_subject, var_types)?;
                let enum_def = match self.type_definitions.get(&subject_type) {
                    Some(TypeDef::Enum(enum_def)) => enum_def,
                    _ => {
                        return Err(anyhow::anyhow!(
                            "match subject must be an enum, got {:?}",
                            subject_type
                        ))
                    }
                };

                let mut normalized_arms = Vec::with_capacity(arms.len());
                for arm in arms {
                    let (variant_name, binder) = match &arm.pattern {
                        parser::MatchPattern::Variant {
                            type_name: _,
                            variant_name,
                            binder,
                        } => (variant_name, binder),
                    };
                    let variant = enum_def
                        .variants
                        .iter()
                        .find(|variant| variant.name == *variant_name)
                        .ok_or_else(|| {
                            anyhow::anyhow!(
                                "unknown variant {} for enum {}",
                                variant_name,
                                enum_def.name
                            )
                        })?;

                    let mut scoped_var_types = var_types.clone();
                    if let (Some(payload_ty), Some(binder_name)) = (&variant.payload_ty, binder) {
                        scoped_var_types.insert(binder_name.clone(), payload_ty.clone());
                    }

                    let normalized_body = arm
                        .body
                        .iter()
                        .map(|statement| {
                            self.normalize_method_calls_in_statement(
                                statement,
                                &mut scoped_var_types,
                            )
                        })
                        .collect::<anyhow::Result<Vec<_>>>()?;
                    normalized_arms.push(parser::MatchArm {
                        pattern: arm.pattern.clone(),
                        body: normalized_body,
                    });
                }

                Ok(parser::Statement::Match {
                    subject: normalized_subject,
                    arms: normalized_arms,
                })
            }
            parser::Statement::Conditional {
                condition,
                body,
                else_body,
            } => {
                let normalized_condition =
                    self.normalize_method_calls_in_expression(condition, var_types)?;
                let normalized_body = body
                    .iter()
                    .map(|statement| self.normalize_method_calls_in_statement(statement, var_types))
                    .collect::<anyhow::Result<Vec<_>>>()?;
                let normalized_else_body = else_body
                    .as_ref()
                    .map(|else_body| {
                        else_body
                            .iter()
                            .map(|statement| {
                                self.normalize_method_calls_in_statement(statement, var_types)
                            })
                            .collect::<anyhow::Result<Vec<_>>>()
                    })
                    .transpose()?;

                Ok(parser::Statement::Conditional {
                    condition: normalized_condition,
                    body: normalized_body,
                    else_body: normalized_else_body,
                })
            }
            parser::Statement::Assign { variable, value } => {
                let normalized_value =
                    self.normalize_method_calls_in_expression(value, var_types)?;
                let variable_type = self.expression_type(&normalized_value, var_types)?;
                if variable_type == "Void" {
                    return Err(anyhow::anyhow!(
                        "cannot assign expression of type Void to variable {}",
                        variable
                    ));
                }
                var_types.insert(variable.clone(), variable_type);
                Ok(parser::Statement::Assign {
                    variable: variable.clone(),
                    value: normalized_value,
                })
            }
            parser::Statement::Return { expr } => Ok(parser::Statement::Return {
                expr: self.normalize_method_calls_in_expression(expr, var_types)?,
            }),
            parser::Statement::Expression { expr } => Ok(parser::Statement::Expression {
                expr: self.normalize_method_calls_in_expression(expr, var_types)?,
            }),
            parser::Statement::Prove { condition } => Ok(parser::Statement::Prove {
                condition: self.normalize_method_calls_in_expression(condition, var_types)?,
            }),
            parser::Statement::Assert { condition } => Ok(parser::Statement::Assert {
                condition: self.normalize_method_calls_in_expression(condition, var_types)?,
            }),
            parser::Statement::While { condition, body } => {
                let normalized_condition =
                    self.normalize_method_calls_in_expression(condition, var_types)?;
                let normalized_body = body
                    .iter()
                    .map(|statement| self.normalize_method_calls_in_statement(statement, var_types))
                    .collect::<anyhow::Result<Vec<_>>>()?;
                Ok(parser::Statement::While {
                    condition: normalized_condition,
                    body: normalized_body,
                })
            }
        }
    }

    fn normalize_method_calls_in_expression(
        &self,
        expression: &Expression,
        var_types: &HashMap<String, TypeRef>,
    ) -> anyhow::Result<Expression> {
        match expression {
            Expression::Match { subject, arms } => {
                let normalized_subject =
                    self.normalize_method_calls_in_expression(subject, var_types)?;
                let subject_type = self.expression_type(&normalized_subject, var_types)?;
                let enum_def = match self.type_definitions.get(&subject_type) {
                    Some(TypeDef::Enum(enum_def)) => enum_def,
                    _ => {
                        return Err(anyhow::anyhow!(
                            "match subject must be an enum, got {:?}",
                            subject_type
                        ))
                    }
                };

                let mut normalized_arms = Vec::with_capacity(arms.len());
                for arm in arms {
                    let (variant_name, binder) = match &arm.pattern {
                        parser::MatchPattern::Variant {
                            type_name: _,
                            variant_name,
                            binder,
                        } => (variant_name, binder),
                    };
                    let variant = enum_def
                        .variants
                        .iter()
                        .find(|variant| variant.name == *variant_name)
                        .ok_or_else(|| {
                            anyhow::anyhow!(
                                "unknown variant {} for enum {}",
                                variant_name,
                                enum_def.name
                            )
                        })?;

                    let mut scoped_var_types = var_types.clone();
                    if let (Some(payload_ty), Some(binder_name)) = (&variant.payload_ty, binder) {
                        scoped_var_types.insert(binder_name.clone(), payload_ty.clone());
                    }

                    normalized_arms.push(parser::MatchExprArm {
                        pattern: arm.pattern.clone(),
                        value: self
                            .normalize_method_calls_in_expression(&arm.value, &scoped_var_types)?,
                    });
                }

                Ok(Expression::Match {
                    subject: Box::new(normalized_subject),
                    arms: normalized_arms,
                })
            }
            Expression::Literal(_) | Expression::Variable(_) | Expression::FieldAccess { .. } => {
                Ok(expression.clone())
            }
            Expression::Call(name, args) => Ok(Expression::Call(
                name.clone(),
                args.iter()
                    .map(|arg| self.normalize_method_calls_in_expression(arg, var_types))
                    .collect::<anyhow::Result<Vec<_>>>()?,
            )),
            Expression::MethodCall {
                receiver,
                method,
                args,
            } => {
                let normalized_receiver =
                    self.normalize_method_calls_in_expression(receiver, var_types)?;
                let normalized_args = args
                    .iter()
                    .map(|arg| self.normalize_method_calls_in_expression(arg, var_types))
                    .collect::<anyhow::Result<Vec<_>>>()?;
                normalize_method_call_expression(
                    &normalized_receiver,
                    method,
                    &normalized_args,
                    var_types,
                    &self.function_sigs,
                    &self.type_definitions,
                    &self.trait_method_signatures,
                    &self.trait_impl_methods,
                )
            }
            Expression::PostfixCall { callee, args } => {
                let normalized_callee =
                    self.normalize_method_calls_in_expression(callee, var_types)?;
                let normalized_args = args
                    .iter()
                    .map(|arg| self.normalize_method_calls_in_expression(arg, var_types))
                    .collect::<anyhow::Result<Vec<_>>>()?;
                if let Expression::FieldAccess {
                    struct_variable,
                    field,
                } = &normalized_callee
                {
                    if self
                        .trait_method_signatures
                        .contains_key(&trait_method_key(struct_variable, field))
                    {
                        let (target, _) = resolve_trait_call_target(
                            struct_variable,
                            field,
                            &normalized_args,
                            var_types,
                            &self.function_sigs,
                            &self.type_definitions,
                            &self.trait_method_signatures,
                            &self.trait_impl_methods,
                        )?;
                        return Ok(match target {
                            TraitCallTarget::Function(target_function) => {
                                Expression::Call(target_function, normalized_args)
                            }
                            TraitCallTarget::BuiltinOperator(_) => Expression::PostfixCall {
                                callee: Box::new(normalized_callee),
                                args: normalized_args,
                            },
                        });
                    }
                }
                Ok(Expression::PostfixCall {
                    callee: Box::new(normalized_callee),
                    args: normalized_args,
                })
            }
            Expression::BinOp(op, left, right) => {
                let normalized_left = self.normalize_method_calls_in_expression(left, var_types)?;
                let normalized_right =
                    self.normalize_method_calls_in_expression(right, var_types)?;
                match resolve_binary_operator(
                    *op,
                    &normalized_left,
                    &normalized_right,
                    var_types,
                    &self.function_sigs,
                    &self.type_definitions,
                    &self.trait_method_signatures,
                    &self.trait_impl_methods,
                )? {
                    BinaryOperatorResolution::Builtin { .. } => Ok(Expression::BinOp(
                        *op,
                        Box::new(normalized_left),
                        Box::new(normalized_right),
                    )),
                    BinaryOperatorResolution::TraitCall {
                        target_function, ..
                    } => {
                        let call = Expression::Call(
                            target_function,
                            vec![normalized_left, normalized_right],
                        );
                        if matches!(op, parser::Op::Neq) {
                            Ok(Expression::UnaryOp(UnaryOp::Not, Box::new(call)))
                        } else {
                            Ok(call)
                        }
                    }
                    BinaryOperatorResolution::ComparisonTraitCall { target_function } => {
                        Ok(Expression::BinOp(
                            *op,
                            Box::new(Expression::Call(
                                target_function,
                                vec![normalized_left, normalized_right],
                            )),
                            Box::new(Expression::Literal(Literal::Int(0))),
                        ))
                    }
                }
            }
            Expression::UnaryOp(op, expr) => Ok(Expression::UnaryOp(
                *op,
                Box::new(self.normalize_method_calls_in_expression(expr, var_types)?),
            )),
            Expression::StructValue {
                struct_name,
                field_values,
            } => Ok(Expression::StructValue {
                struct_name: struct_name.clone(),
                field_values: field_values
                    .iter()
                    .map(|(field_name, value)| {
                        Ok((
                            field_name.clone(),
                            self.normalize_method_calls_in_expression(value, var_types)?,
                        ))
                    })
                    .collect::<anyhow::Result<Vec<_>>>()?,
            }),
        }
    }

    fn has_copy_impl_for_type(&self, ty: &str) -> bool {
        let impl_key = trait_impl_method_key("Copy", normalize_numeric_alias(ty), "copy");
        self.trait_impl_methods.contains_key(&impl_key)
    }

    fn drop_impl_for_type(&self, ty: &str) -> Option<String> {
        let impl_key = trait_impl_method_key("Drop", normalize_numeric_alias(ty), "drop");
        self.trait_impl_methods.get(&impl_key).cloned()
    }

    fn ownership_consume_local(
        &self,
        name: &str,
        state: &mut OwnershipState,
    ) -> anyhow::Result<()> {
        let local = state
            .locals
            .get_mut(name)
            .ok_or_else(|| anyhow::anyhow!("unknown variable {}", name))?;
        match local.state {
            OwnershipBindingState::Initialized => {}
            OwnershipBindingState::Moved => {
                return Err(anyhow::anyhow!("use of moved value {}", name))
            }
            OwnershipBindingState::Uninitialized => {
                return Err(anyhow::anyhow!(
                    "cannot move from uninitialized value {}",
                    name
                ))
            }
        }
        if !self.has_copy_impl_for_type(&local.ty) {
            local.state = OwnershipBindingState::Moved;
        }
        Ok(())
    }

    fn ownership_insert_or_assign_local(&self, state: &mut OwnershipState, name: &str, ty: &str) {
        if let Some(existing) = state.locals.get_mut(name) {
            existing.ty = ty.to_string();
            existing.state = OwnershipBindingState::Initialized;
            return;
        }
        state.locals.insert(
            name.to_string(),
            OwnershipLocal {
                ty: ty.to_string(),
                state: OwnershipBindingState::Initialized,
                order: state.next_order,
            },
        );
        state.next_order += 1;
    }

    fn ownership_analyze_expression(
        &self,
        expr: &Expression,
        state: &mut OwnershipState,
    ) -> anyhow::Result<TypeRef> {
        let var_types = state.as_var_types();
        let expr_ty = self.expression_type(expr, &var_types)?;
        match expr {
            Expression::Literal(_) => {}
            Expression::Variable(name) => {
                self.ownership_consume_local(name, state)?;
            }
            Expression::UnaryOp(_, inner) => {
                let _ = self.ownership_analyze_expression(inner, state)?;
            }
            Expression::BinOp(_, left, right) => {
                let _ = self.ownership_analyze_expression(left, state)?;
                let _ = self.ownership_analyze_expression(right, state)?;
            }
            Expression::Call(_, arguments) => {
                for argument in arguments {
                    let _ = self.ownership_analyze_expression(argument, state)?;
                }
            }
            Expression::MethodCall {
                receiver,
                method: _,
                args,
            } => {
                match receiver.as_ref() {
                    Expression::Variable(name) => {
                        if state.locals.contains_key(name) {
                            self.ownership_consume_local(name, state)?;
                        }
                    }
                    other => {
                        let _ = self.ownership_analyze_expression(other, state)?;
                    }
                }
                for argument in args {
                    let _ = self.ownership_analyze_expression(argument, state)?;
                }
            }
            Expression::PostfixCall { callee, args } => {
                if !matches!(callee.as_ref(), Expression::FieldAccess { .. }) {
                    let _ = self.ownership_analyze_expression(callee, state)?;
                }
                for argument in args {
                    let _ = self.ownership_analyze_expression(argument, state)?;
                }
            }
            Expression::FieldAccess {
                struct_variable, ..
            } => {
                if state.locals.contains_key(struct_variable) {
                    self.ownership_consume_local(struct_variable, state)?;
                }
            }
            Expression::StructValue { field_values, .. } => {
                for (_, value) in field_values {
                    let _ = self.ownership_analyze_expression(value, state)?;
                }
            }
            Expression::Match { subject, arms } => {
                let subject_ty = {
                    let var_types = state.as_var_types();
                    self.expression_type(subject, &var_types)?
                };
                let enum_def = match self.type_definitions.get(&subject_ty) {
                    Some(TypeDef::Enum(enum_def)) => enum_def,
                    _ => {
                        return Err(anyhow::anyhow!(
                            "match subject must be an enum, got {:?}",
                            subject_ty
                        ));
                    }
                };

                let _ = self.ownership_analyze_expression(subject, state)?;
                let base_after_subject = state.clone();

                let mut arm_states = vec![];
                for arm in arms {
                    let mut arm_state = base_after_subject.clone();
                    let (variant_name, binder) = match &arm.pattern {
                        parser::MatchPattern::Variant {
                            type_name,
                            variant_name,
                            binder,
                        } => {
                            if type_name != &subject_ty {
                                return Err(anyhow::anyhow!(
                                    "match arm type {:?} does not match subject type {:?}",
                                    type_name,
                                    subject_ty
                                ));
                            }
                            (variant_name, binder)
                        }
                    };
                    let variant = enum_def
                        .variants
                        .iter()
                        .find(|v| &v.name == variant_name)
                        .ok_or_else(|| {
                            anyhow::anyhow!(
                                "unknown variant {} for enum {}",
                                variant_name,
                                enum_def.name
                            )
                        })?;
                    if let (Some(payload_ty), Some(binder_name)) = (&variant.payload_ty, binder) {
                        self.ownership_insert_or_assign_local(
                            &mut arm_state,
                            binder_name,
                            payload_ty,
                        );
                    }
                    let _ = self.ownership_analyze_expression(&arm.value, &mut arm_state)?;
                    arm_states.push(arm_state);
                }
                *state = self.ownership_merge_states(&base_after_subject, &arm_states)?;
            }
        }
        Ok(expr_ty)
    }

    fn ownership_merge_states(
        &self,
        base: &OwnershipState,
        branch_states: &[OwnershipState],
    ) -> anyhow::Result<OwnershipState> {
        if branch_states.is_empty() {
            return Ok(base.clone());
        }

        let mut merged = OwnershipState::default();
        merged.next_order = branch_states
            .iter()
            .fold(base.next_order, |max_seen, state| {
                std::cmp::max(max_seen, state.next_order)
            });

        let mut all_names = HashSet::new();
        all_names.extend(base.locals.keys().cloned());
        for state in branch_states {
            all_names.extend(state.locals.keys().cloned());
        }

        for name in all_names {
            let mut selected: Option<OwnershipLocal> = base.locals.get(&name).cloned();
            for branch in branch_states {
                if let Some(local) = branch.locals.get(&name) {
                    match &selected {
                        Some(existing) => {
                            if normalize_numeric_alias(&existing.ty)
                                != normalize_numeric_alias(&local.ty)
                            {
                                return Err(anyhow::anyhow!(
                                    "incompatible variable type for {} across control-flow branches: {} vs {}",
                                    name,
                                    existing.ty,
                                    local.ty
                                ));
                            }
                        }
                        None => {
                            selected = Some(local.clone());
                        }
                    }
                }
            }
            if let Some(mut local) = selected {
                let branch_locals = branch_states
                    .iter()
                    .map(|branch| branch.locals.get(&name))
                    .collect::<Vec<_>>();

                local.state = if branch_locals.iter().all(|candidate| {
                    matches!(
                        candidate,
                        Some(candidate) if candidate.state == OwnershipBindingState::Initialized
                    )
                }) {
                    OwnershipBindingState::Initialized
                } else if branch_locals.iter().all(|candidate| {
                    matches!(
                        candidate,
                        Some(candidate) if candidate.state == OwnershipBindingState::Moved
                    )
                }) {
                    OwnershipBindingState::Moved
                } else {
                    OwnershipBindingState::Uninitialized
                };
                local.order = branch_states.iter().fold(local.order, |min_order, branch| {
                    branch
                        .locals
                        .get(&name)
                        .map(|candidate| std::cmp::min(min_order, candidate.order))
                        .unwrap_or(min_order)
                });
                merged.locals.insert(name, local);
            }
        }
        Ok(merged)
    }

    fn ownership_drop_statements_in_reverse(
        &self,
        state: &OwnershipState,
    ) -> Vec<parser::Statement> {
        let mut live = state
            .locals
            .iter()
            .filter_map(|(name, local)| {
                if local.state != OwnershipBindingState::Initialized {
                    return None;
                }
                self.drop_impl_for_type(&local.ty)
                    .map(|drop_impl| (name.clone(), local.order, drop_impl))
            })
            .collect::<Vec<_>>();
        live.sort_by_key(|(_, order, _)| std::cmp::Reverse(*order));
        live.into_iter()
            .map(|(name, _order, drop_impl)| parser::Statement::Expression {
                expr: Expression::Call(drop_impl, vec![Expression::Variable(name)]),
            })
            .collect()
    }

    fn ownership_drop_statements_for_scope_exit(
        &self,
        from: &OwnershipState,
        to: &OwnershipState,
    ) -> Vec<parser::Statement> {
        let mut live = from
            .locals
            .iter()
            .filter_map(|(name, local)| {
                if local.state != OwnershipBindingState::Initialized {
                    return None;
                }
                let destination_is_initialized = to
                    .locals
                    .get(name)
                    .map(|target| target.state == OwnershipBindingState::Initialized)
                    .unwrap_or(false);
                if destination_is_initialized {
                    return None;
                }
                self.drop_impl_for_type(&local.ty)
                    .map(|drop_impl| (name.clone(), local.order, drop_impl))
            })
            .collect::<Vec<_>>();
        live.sort_by_key(|(_, order, _)| std::cmp::Reverse(*order));
        live.into_iter()
            .map(|(name, _order, drop_impl)| parser::Statement::Expression {
                expr: Expression::Call(drop_impl, vec![Expression::Variable(name)]),
            })
            .collect()
    }

    fn ownership_rewrite_block(
        &self,
        body: &[parser::Statement],
        state: &mut OwnershipState,
    ) -> anyhow::Result<Vec<parser::Statement>> {
        let mut out = Vec::new();
        for statement in body {
            let mut rewritten = self.ownership_rewrite_statement(statement, state)?;
            out.append(&mut rewritten);
        }
        Ok(out)
    }

    fn ownership_rewrite_statement(
        &self,
        statement: &parser::Statement,
        state: &mut OwnershipState,
    ) -> anyhow::Result<Vec<parser::Statement>> {
        match statement {
            parser::Statement::StructDef { .. } => Ok(vec![statement.clone()]),
            parser::Statement::Expression { expr } => {
                let _ = self.ownership_analyze_expression(expr, state)?;
                Ok(vec![statement.clone()])
            }
            parser::Statement::Prove { condition } => {
                let condition_ty = self.ownership_analyze_expression(condition, state)?;
                if condition_ty != "Bool" {
                    return Err(anyhow::anyhow!(
                        "prove expects Bool condition, got {:?}",
                        condition_ty
                    ));
                }
                Ok(vec![statement.clone()])
            }
            parser::Statement::Assert { condition } => {
                let condition_ty = self.ownership_analyze_expression(condition, state)?;
                if condition_ty != "Bool" {
                    return Err(anyhow::anyhow!(
                        "assert expects Bool condition, got {:?}",
                        condition_ty
                    ));
                }
                Ok(vec![statement.clone()])
            }
            parser::Statement::Assign { variable, value } => {
                let value_ty = self.ownership_analyze_expression(value, state)?;
                if value_ty == "Void" {
                    return Err(anyhow::anyhow!(
                        "cannot assign expression of type Void to variable {}",
                        variable
                    ));
                }

                let mut out = vec![];
                if let Some(existing) = state.locals.get_mut(variable) {
                    if existing.state == OwnershipBindingState::Initialized {
                        if let Some(drop_impl) = self.drop_impl_for_type(&existing.ty) {
                            out.push(parser::Statement::Expression {
                                expr: Expression::Call(
                                    drop_impl,
                                    vec![Expression::Variable(variable.clone())],
                                ),
                            });
                            existing.state = OwnershipBindingState::Uninitialized;
                        }
                    }
                }

                self.ownership_insert_or_assign_local(state, variable, &value_ty);
                out.push(statement.clone());
                Ok(out)
            }
            parser::Statement::Return { expr } => {
                let _ = self.ownership_analyze_expression(expr, state)?;
                let mut out = self.ownership_drop_statements_in_reverse(state);
                out.push(statement.clone());
                Ok(out)
            }
            parser::Statement::Conditional {
                condition,
                body,
                else_body,
            } => {
                let condition_ty = self.ownership_analyze_expression(condition, state)?;
                if condition_ty != "Bool" {
                    return Err(anyhow::anyhow!(
                        "expected condition to be of type Bool, but got {:?}",
                        condition_ty
                    ));
                }
                let state_after_condition = state.clone();

                let mut then_state = state_after_condition.clone();
                let mut rewritten_then = self.ownership_rewrite_block(body, &mut then_state)?;

                let mut else_state = state_after_condition.clone();
                let mut rewritten_else = if let Some(else_body) = else_body {
                    Some(self.ownership_rewrite_block(else_body, &mut else_state)?)
                } else {
                    None
                };

                let merged = if rewritten_else.is_some() {
                    self.ownership_merge_states(
                        &state_after_condition,
                        &[then_state.clone(), else_state.clone()],
                    )?
                } else {
                    self.ownership_merge_states(
                        &state_after_condition,
                        &[then_state.clone(), state_after_condition.clone()],
                    )?
                };
                rewritten_then
                    .extend(self.ownership_drop_statements_for_scope_exit(&then_state, &merged));
                if let Some(else_body) = rewritten_else.as_mut() {
                    else_body.extend(
                        self.ownership_drop_statements_for_scope_exit(&else_state, &merged),
                    );
                }
                *state = merged;

                Ok(vec![parser::Statement::Conditional {
                    condition: condition.clone(),
                    body: rewritten_then,
                    else_body: rewritten_else,
                }])
            }
            parser::Statement::Match { subject, arms } => {
                let subject_ty = {
                    let var_types = state.as_var_types();
                    self.expression_type(subject, &var_types)?
                };
                let enum_def = match self.type_definitions.get(&subject_ty) {
                    Some(TypeDef::Enum(enum_def)) => enum_def,
                    _ => {
                        return Err(anyhow::anyhow!(
                            "match subject must be an enum, got {:?}",
                            subject_ty
                        ));
                    }
                };
                let _ = self.ownership_analyze_expression(subject, state)?;
                let state_after_subject = state.clone();

                let mut rewritten_arms = vec![];
                let mut arm_states = vec![];
                for arm in arms {
                    let mut arm_state = state_after_subject.clone();
                    let (variant_name, binder) = match &arm.pattern {
                        parser::MatchPattern::Variant {
                            type_name,
                            variant_name,
                            binder,
                        } => {
                            if type_name != &subject_ty {
                                return Err(anyhow::anyhow!(
                                    "match arm type {:?} does not match subject type {:?}",
                                    type_name,
                                    subject_ty
                                ));
                            }
                            (variant_name, binder)
                        }
                    };
                    let variant = enum_def
                        .variants
                        .iter()
                        .find(|v| &v.name == variant_name)
                        .ok_or_else(|| {
                            anyhow::anyhow!(
                                "unknown variant {} for enum {}",
                                variant_name,
                                enum_def.name
                            )
                        })?;
                    if let (Some(payload_ty), Some(binder_name)) = (&variant.payload_ty, binder) {
                        self.ownership_insert_or_assign_local(
                            &mut arm_state,
                            binder_name,
                            payload_ty,
                        );
                    }
                    let rewritten_body = self.ownership_rewrite_block(&arm.body, &mut arm_state)?;
                    arm_states.push(arm_state);
                    rewritten_arms.push(parser::MatchArm {
                        pattern: arm.pattern.clone(),
                        body: rewritten_body,
                    });
                }

                let merged = self.ownership_merge_states(&state_after_subject, &arm_states)?;
                for (rewritten_arm, arm_state) in rewritten_arms.iter_mut().zip(arm_states.iter()) {
                    rewritten_arm
                        .body
                        .extend(self.ownership_drop_statements_for_scope_exit(arm_state, &merged));
                }
                *state = merged;
                Ok(vec![parser::Statement::Match {
                    subject: subject.clone(),
                    arms: rewritten_arms,
                }])
            }
            parser::Statement::While { condition, body } => {
                let condition_ty = self.ownership_analyze_expression(condition, state)?;
                if condition_ty != "Bool" {
                    return Err(anyhow::anyhow!(
                        "expected condition to be of type Bool, but got {:?}",
                        condition_ty
                    ));
                }
                let state_after_condition = state.clone();

                let mut body_state = state_after_condition.clone();
                let mut rewritten_body = self.ownership_rewrite_block(body, &mut body_state)?;
                rewritten_body.extend(
                    self.ownership_drop_statements_for_scope_exit(
                        &body_state,
                        &state_after_condition,
                    ),
                );

                *state = self.ownership_merge_states(
                    &state_after_condition,
                    &[state_after_condition.clone(), body_state],
                )?;

                Ok(vec![parser::Statement::While {
                    condition: condition.clone(),
                    body: rewritten_body,
                }])
            }
        }
    }

    fn apply_ownership_model(
        &mut self,
        ownership_target_functions: &HashSet<String>,
    ) -> anyhow::Result<()> {
        let function_names = self
            .function_definitions
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        for function_name in function_names {
            if !ownership_target_functions.contains(&function_name) {
                continue;
            }
            let (sig, body) = {
                let definition =
                    self.function_definitions
                        .get(&function_name)
                        .ok_or_else(|| {
                            anyhow::anyhow!("missing function definition {}", function_name)
                        })?;
                (definition.sig.clone(), definition.body.clone())
            };

            let mut state = OwnershipState::with_params(&sig.parameters);
            let mut rewritten = self.ownership_rewrite_block(&body, &mut state)?;
            rewritten.extend(self.ownership_drop_statements_in_reverse(&state));

            let definition = self
                .function_definitions
                .get_mut(&function_name)
                .ok_or_else(|| anyhow::anyhow!("missing function definition {}", function_name))?;
            definition.body = rewritten;
        }
        Ok(())
    }
}

#[tracing::instrument(level = "trace", skip_all)]
pub(crate) fn resolve_with_mode(
    mut ast: Ast,
    mode: ResolveMode,
) -> anyhow::Result<ResolvedProgram> {
    let mut ownership_target_functions = ast
        .top_level_functions
        .iter()
        .filter(|f| !f.is_comptime && !f.is_extern)
        .map(|f| f.name.clone())
        .collect::<HashSet<_>>();
    for impl_decl in &ast.impl_declarations {
        for method in &impl_decl.methods {
            ownership_target_functions.insert(trait_impl_function_name(
                &impl_decl.trait_name,
                &impl_decl.for_type,
                &method.name,
            ));
        }
    }

    {
        let stdlib_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src")
            .join("std")
            .join("std.oa");
        let stdlib_ast = flat_imports::parse_and_resolve_file(&stdlib_path)?;

        ast.top_level_functions
            .extend(stdlib_ast.top_level_functions);
        ast.type_definitions.extend(stdlib_ast.type_definitions);
        ast.trait_declarations.extend(stdlib_ast.trait_declarations);
        ast.impl_declarations.extend(stdlib_ast.impl_declarations);
        ast.generic_definitions
            .extend(stdlib_ast.generic_definitions);
        ast.generic_specializations
            .extend(stdlib_ast.generic_specializations);
        ast.invariants.extend(stdlib_ast.invariants);
    }
    let (trait_method_signatures, trait_impl_methods, trait_impl_targets, impl_functions) =
        collect_trait_metadata(&ast)?;
    expand_generics(&mut ast, &trait_method_signatures, &trait_impl_targets)?;

    let mut program = ResolvedProgram {
        ast: ast.clone(),
        function_definitions: HashMap::new(),
        function_sigs: HashMap::new(),
        trait_method_signatures,
        trait_impl_methods,
        type_definitions: HashMap::new(),
        struct_invariants: HashMap::new(),
        function_preconditions: HashMap::new(),
        model_invariants: Vec::new(),
        comptime_function_definitions: HashMap::new(),
        comptime_apply_order: ast.comptime_applies.clone(),
        semantic_expr_metadata: HashMap::new(),
    };

    program
        .type_definitions
        .insert("Int".to_string(), TypeDef::BuiltIn(BuiltInType::I32))
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert Int type definition"))
        })?;
    program
        .type_definitions
        .insert("PtrInt".to_string(), TypeDef::BuiltIn(BuiltInType::I64))
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert PtrInt type definition"))
        })?;
    program
        .type_definitions
        .insert("Bool".to_string(), TypeDef::BuiltIn(BuiltInType::Bool))
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert Bool type definition"))
        })?;
    program
        .type_definitions
        .insert("U8".to_string(), TypeDef::BuiltIn(BuiltInType::U8))
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert U8 type definition"))
        })?;
    program
        .type_definitions
        .insert("I32".to_string(), TypeDef::BuiltIn(BuiltInType::I32))
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert I32 type definition"))
        })?;
    program
        .type_definitions
        .insert("I64".to_string(), TypeDef::BuiltIn(BuiltInType::I64))
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert I64 type definition"))
        })?;
    program
        .type_definitions
        .insert("FP32".to_string(), TypeDef::BuiltIn(BuiltInType::FP32))
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert FP32 type definition"))
        })?;
    program
        .type_definitions
        .insert("FP64".to_string(), TypeDef::BuiltIn(BuiltInType::FP64))
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert FP64 type definition"))
        })?;
    program
        .type_definitions
        .insert("Void".to_string(), TypeDef::BuiltIn(BuiltInType::Void))
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert Void type definition"))
        })?;
    for semantic_ty in SEMANTIC_BUILTIN_TYPES {
        program
            .type_definitions
            .insert(
                semantic_ty.to_string(),
                TypeDef::BuiltIn(BuiltInType::Semantic),
            )
            .map_or(Ok(()), |_| {
                Err(anyhow::anyhow!(
                    "failed to insert semantic builtin type definition for {}",
                    semantic_ty
                ))
            })?;
    }

    // Built-in functions

    program.function_sigs.insert(
        "print".to_string(),
        FunctionSignature {
            parameters: vec![FunctionParameter {
                name: "a".to_string(),
                ty: "I32".to_string(),
            }],
            return_type: "I32".to_string(),
            extern_symbol_name: None,
        },
    );
    program.function_sigs.insert(
        "char_at".to_string(),
        FunctionSignature {
            parameters: vec![
                FunctionParameter {
                    name: "s".to_string(),
                    ty: "String".to_string(),
                },
                FunctionParameter {
                    name: "index".to_string(),
                    ty: "I32".to_string(),
                },
            ],
            return_type: "I32".to_string(),
            extern_symbol_name: None,
        },
    );
    program.function_sigs.insert(
        "load_u8".to_string(),
        FunctionSignature {
            parameters: vec![FunctionParameter {
                name: "addr".to_string(),
                ty: "PtrInt".to_string(),
            }],
            return_type: "U8".to_string(),
            extern_symbol_name: None,
        },
    );
    program.function_sigs.insert(
        "load_i32".to_string(),
        FunctionSignature {
            parameters: vec![FunctionParameter {
                name: "addr".to_string(),
                ty: "PtrInt".to_string(),
            }],
            return_type: "I32".to_string(),
            extern_symbol_name: None,
        },
    );
    program.function_sigs.insert(
        "load_i64".to_string(),
        FunctionSignature {
            parameters: vec![FunctionParameter {
                name: "addr".to_string(),
                ty: "PtrInt".to_string(),
            }],
            return_type: "I64".to_string(),
            extern_symbol_name: None,
        },
    );
    program.function_sigs.insert(
        "load_bool".to_string(),
        FunctionSignature {
            parameters: vec![FunctionParameter {
                name: "addr".to_string(),
                ty: "PtrInt".to_string(),
            }],
            return_type: "Bool".to_string(),
            extern_symbol_name: None,
        },
    );
    program.function_sigs.insert(
        "store_u8".to_string(),
        FunctionSignature {
            parameters: vec![
                FunctionParameter {
                    name: "addr".to_string(),
                    ty: "PtrInt".to_string(),
                },
                FunctionParameter {
                    name: "value".to_string(),
                    ty: "U8".to_string(),
                },
            ],
            return_type: "Void".to_string(),
            extern_symbol_name: None,
        },
    );
    program.function_sigs.insert(
        "store_i32".to_string(),
        FunctionSignature {
            parameters: vec![
                FunctionParameter {
                    name: "addr".to_string(),
                    ty: "PtrInt".to_string(),
                },
                FunctionParameter {
                    name: "value".to_string(),
                    ty: "I32".to_string(),
                },
            ],
            return_type: "Void".to_string(),
            extern_symbol_name: None,
        },
    );
    program.function_sigs.insert(
        "store_i64".to_string(),
        FunctionSignature {
            parameters: vec![
                FunctionParameter {
                    name: "addr".to_string(),
                    ty: "PtrInt".to_string(),
                },
                FunctionParameter {
                    name: "value".to_string(),
                    ty: "I64".to_string(),
                },
            ],
            return_type: "Void".to_string(),
            extern_symbol_name: None,
        },
    );
    program.function_sigs.insert(
        "store_bool".to_string(),
        FunctionSignature {
            parameters: vec![
                FunctionParameter {
                    name: "addr".to_string(),
                    ty: "PtrInt".to_string(),
                },
                FunctionParameter {
                    name: "value".to_string(),
                    ty: "Bool".to_string(),
                },
            ],
            return_type: "Void".to_string(),
            extern_symbol_name: None,
        },
    );
    program.function_sigs.insert(
        "i32_to_i64".to_string(),
        FunctionSignature {
            parameters: vec![FunctionParameter {
                name: "a".to_string(),
                ty: "I32".to_string(),
            }],
            return_type: "I64".to_string(),
            extern_symbol_name: None,
        },
    );

    for type_def in ast.type_definitions.iter() {
        match type_def {
            parser::TypeDefDecl::Struct(struct_def) => {
                program
                    .type_definitions
                    .insert(struct_def.name.clone(), TypeDef::Struct(struct_def.clone()))
                    .map_or(Ok(()), |_| {
                        Err(anyhow::anyhow!(
                            "failed to insert type definition for {}",
                            struct_def.name
                        ))
                    })?;
            }
            parser::TypeDefDecl::Enum(enum_def) => {
                let mut seen_variant_names = HashSet::new();
                let mut variants = vec![];
                for (i, variant) in enum_def.variants.iter().enumerate() {
                    if !seen_variant_names.insert(variant.name.clone()) {
                        return Err(anyhow::anyhow!(
                            "duplicate variant {} in enum {}",
                            variant.name,
                            enum_def.name
                        ));
                    }
                    variants.push(EnumVariant {
                        name: variant.name.clone(),
                        payload_ty: variant.payload_ty.clone(),
                        tag: i as u32,
                    });
                }

                let enum_ty = EnumTypeDef {
                    name: enum_def.name.clone(),
                    is_tagged_union: variants.iter().any(|v| v.payload_ty.is_some()),
                    variants,
                };
                program
                    .type_definitions
                    .insert(enum_def.name.clone(), TypeDef::Enum(enum_ty))
                    .map_or(Ok(()), |_| {
                        Err(anyhow::anyhow!(
                            "failed to insert type definition for {}",
                            enum_def.name
                        ))
                    })?;
            }
        }
    }

    for type_def in ast.type_definitions.iter() {
        if let parser::TypeDefDecl::Enum(enum_def) = type_def {
            for variant in &enum_def.variants {
                if let Some(payload_ty) = &variant.payload_ty {
                    if !program.type_definitions.contains_key(payload_ty) {
                        return Err(anyhow::anyhow!(
                            "unknown payload type {} in enum {} variant {}",
                            payload_ty,
                            enum_def.name,
                            variant.name
                        ));
                    }
                }
            }
        }
    }

    let user_extern_functions = ast
        .top_level_functions
        .iter()
        .filter(|f| f.is_extern)
        .cloned()
        .collect::<Vec<_>>();
    let user_runtime_functions = ast
        .top_level_functions
        .iter()
        .filter(|f| !f.is_comptime && !f.is_extern)
        .cloned()
        .collect::<Vec<_>>();
    let user_comptime_functions = ast
        .top_level_functions
        .iter()
        .filter(|f| f.is_comptime && !f.is_extern)
        .cloned()
        .collect::<Vec<_>>();

    if program.function_sigs.contains_key(META_EXPR_OPT_FUNCTION) {
        return Err(anyhow::anyhow!(
            "function name {} is reserved for compiler metadata introspection",
            META_EXPR_OPT_FUNCTION
        ));
    }
    program.function_sigs.insert(
        META_EXPR_OPT_FUNCTION.to_string(),
        FunctionSignature {
            parameters: vec![FunctionParameter {
                name: "expr".to_string(),
                ty: "Type".to_string(),
            }],
            return_type: "SemanticExprOpt".to_string(),
            extern_symbol_name: None,
        },
    );

    for function in &user_extern_functions {
        if function.is_comptime {
            return Err(anyhow::anyhow!(
                "extern function {} cannot be comptime",
                function.name
            ));
        }
        if !function.body.is_empty() {
            return Err(anyhow::anyhow!(
                "extern function {} must not have a body",
                function.name
            ));
        }
        if RESERVED_BUILTIN_FUNCTION_NAMES.contains(&function.name.as_str()) {
            return Err(anyhow::anyhow!(
                "function name {} is reserved for builtin assertion semantics",
                function.name
            ));
        }
        let sig = FunctionSignature {
            parameters: function
                .parameters
                .iter()
                .map(|p| FunctionParameter {
                    name: p.name.clone(),
                    ty: p.ty.clone(),
                })
                .collect::<Vec<_>>(),
            return_type: function.return_type.clone(),
            extern_symbol_name: function.extern_symbol_name.clone(),
        };
        validate_function_signature_types(&function.name, &sig, &program.type_definitions, true)?;
        program
            .function_sigs
            .insert(function.name.clone(), sig)
            .map_or(Ok(()), |_| {
                Err(anyhow::anyhow!(
                    "failed to insert function signature for {}",
                    function.name
                ))
            })?;
    }

    let mut all_functions = user_runtime_functions.clone();
    all_functions.extend(impl_functions);
    let synthesized_invariants = synthesize_invariant_functions(
        &ast.invariants,
        &program.type_definitions,
        &ast.top_level_functions,
        &mut program.struct_invariants,
        &mut program.model_invariants,
    )?;
    all_functions.extend(synthesized_invariants);
    let synthesized_preconditions =
        synthesize_precondition_functions(&all_functions, &mut program.function_preconditions)?;
    all_functions.extend(synthesized_preconditions);

    // Pass 1: register signatures for all top-level functions and synthesized invariants.
    for function in all_functions.iter() {
        if RESERVED_BUILTIN_FUNCTION_NAMES.contains(&function.name.as_str()) {
            return Err(anyhow::anyhow!(
                "function name {} is reserved for builtin assertion semantics",
                function.name
            ));
        }

        let mut parameters = Vec::new();
        for parameter in function.parameters.clone() {
            parameters.push(parameter);
        }
        let sig = FunctionSignature {
            parameters: parameters
                .into_iter()
                .map(|p| {
                    Ok(FunctionParameter {
                        name: p.name,
                        ty: p.ty,
                    })
                })
                .collect::<anyhow::Result<Vec<_>>>()?,
            return_type: function.return_type.clone(),
            extern_symbol_name: None,
        };
        validate_function_signature_types(&function.name, &sig, &program.type_definitions, false)?;

        program
            .function_sigs
            .insert(function.name.clone(), sig)
            .map_or(Ok(()), |_| {
                Err(anyhow::anyhow!(
                    "failed to insert function signature for {}",
                    function.name
                ))
            })?;
    }

    for function in user_comptime_functions.iter() {
        if program.function_sigs.contains_key(&function.name) {
            return Err(anyhow::anyhow!(
                "duplicate function signature for {}",
                function.name
            ));
        }
        let sig = FunctionSignature {
            parameters: function
                .parameters
                .iter()
                .map(|p| FunctionParameter {
                    name: p.name.clone(),
                    ty: p.ty.clone(),
                })
                .collect::<Vec<_>>(),
            return_type: function.return_type.clone(),
            extern_symbol_name: None,
        };
        validate_function_signature_types(&function.name, &sig, &program.type_definitions, false)?;
        program.function_sigs.insert(function.name.clone(), sig);
    }

    // Pass 2: register function bodies.
    for function in all_functions.iter() {
        let sig = program
            .function_sigs
            .get(&function.name)
            .ok_or_else(|| anyhow::anyhow!("missing function signature for {}", function.name))?
            .clone();
        let func_def = FunctionDefinition {
            name: function.name.clone(),
            preconditions: function.preconditions.clone(),
            sig,
            body: function.body.clone(),
            source_span: function.source_span.clone(),
            local_source_spans: function.local_source_spans.clone(),
            precondition_source_spans: function.precondition_source_spans.clone(),
        };

        program
            .function_definitions
            .insert(function.name.clone(), func_def)
            .map_or(Ok(()), |_| {
                Err(anyhow::anyhow!(
                    "failed to insert function definition for {}",
                    function.name
                ))
            })?;
    }

    for function in user_comptime_functions.iter() {
        let sig = FunctionSignature {
            parameters: function
                .parameters
                .iter()
                .map(|p| FunctionParameter {
                    name: p.name.clone(),
                    ty: p.ty.clone(),
                })
                .collect::<Vec<_>>(),
            return_type: function.return_type.clone(),
            extern_symbol_name: None,
        };
        let definition = FunctionDefinition {
            name: function.name.clone(),
            preconditions: function.preconditions.clone(),
            body: function.body.clone(),
            sig,
            source_span: function.source_span.clone(),
            local_source_spans: function.local_source_spans.clone(),
            precondition_source_spans: function.precondition_source_spans.clone(),
        };
        program
            .comptime_function_definitions
            .insert(function.name.clone(), definition)
            .map_or(Ok(()), |_| {
                Err(anyhow::anyhow!(
                    "duplicate comptime function definition {}",
                    function.name
                ))
            })?;
    }

    register_legacy_struct_invariants(
        &all_functions,
        &program.type_definitions,
        &program.function_sigs,
        &mut program.struct_invariants,
    )?;

    // Pass 3: type-check with all signatures available.
    type_check_program_functions(&program, true)?;
    program.normalize_method_calls()?;
    type_check_program_functions(&program, true)?;

    if mode == ResolveMode::FinalRuntime {
        program.apply_ownership_model(&ownership_target_functions)?;
        type_check_program_functions(&program, false)?;

        prune_compile_time_only_runtime_artifacts(&mut program);
        reject_runtime_semantic_builtin_usage(&program)?;
        reject_model_invariant_impurity(&program)?;

        if !program.function_definitions.contains_key("main") {
            return Err(anyhow::anyhow!("main function not defined"));
        }
        validate_main_signature(&program)?;
    }
    program.semantic_expr_metadata = index_semantic_expression_metadata(&program);

    Ok(program)
}

#[tracing::instrument(level = "trace", skip_all)]
pub fn resolve(ast: Ast) -> anyhow::Result<ResolvedProgram> {
    resolve_with_mode(ast, ResolveMode::FinalRuntime)
}

fn type_check_program_functions(
    program: &ResolvedProgram,
    include_comptime_functions: bool,
) -> anyhow::Result<()> {
    for func_def in program.function_definitions.values() {
        program.type_check(func_def)?;
    }
    if include_comptime_functions {
        for func_def in program.comptime_function_definitions.values() {
            program.type_check(func_def)?;
        }
    }
    Ok(())
}

fn type_ref_is_runtime_lowerable(
    type_ref: &str,
    program: &ResolvedProgram,
    memo: &mut HashMap<String, bool>,
    visiting: &mut HashSet<String>,
) -> bool {
    if let Some(cached) = memo.get(type_ref) {
        return *cached;
    }
    if !visiting.insert(type_ref.to_string()) {
        return true;
    }

    let result = match program.type_definitions.get(type_ref) {
        Some(TypeDef::BuiltIn(BuiltInType::Semantic)) => false,
        Some(TypeDef::BuiltIn(_)) => true,
        Some(TypeDef::Struct(struct_def)) => struct_def
            .struct_fields
            .iter()
            .all(|field| type_ref_is_runtime_lowerable(&field.ty, program, memo, visiting)),
        Some(TypeDef::Enum(enum_def)) => enum_def.variants.iter().all(|variant| {
            variant
                .payload_ty
                .as_ref()
                .map(|ty| type_ref_is_runtime_lowerable(ty, program, memo, visiting))
                .unwrap_or(true)
        }),
        None => false,
    };

    visiting.remove(type_ref);
    memo.insert(type_ref.to_string(), result);
    result
}

fn function_signature_is_runtime_lowerable(
    sig: &FunctionSignature,
    program: &ResolvedProgram,
    memo: &mut HashMap<String, bool>,
    visiting: &mut HashSet<String>,
) -> bool {
    sig.parameters
        .iter()
        .all(|param| type_ref_is_runtime_lowerable(&param.ty, program, memo, visiting))
        && type_ref_is_runtime_lowerable(&sig.return_type, program, memo, visiting)
}

fn prune_compile_time_only_runtime_artifacts(program: &mut ResolvedProgram) {
    let mut memo = HashMap::new();
    let mut visiting = HashSet::new();
    let removed_functions = program
        .function_definitions
        .iter()
        .filter_map(|(name, definition)| {
            if function_signature_is_runtime_lowerable(
                &definition.sig,
                program,
                &mut memo,
                &mut visiting,
            ) {
                None
            } else {
                Some(name.clone())
            }
        })
        .collect::<HashSet<_>>();

    if removed_functions.is_empty() {
        return;
    }

    for function_name in &removed_functions {
        program.function_definitions.remove(function_name);
        program.function_sigs.remove(function_name);
        program.function_preconditions.remove(function_name);
    }

    for definitions in program.struct_invariants.values_mut() {
        definitions.retain(|definition| !removed_functions.contains(&definition.function_name));
    }
    program
        .struct_invariants
        .retain(|_, definitions| !definitions.is_empty());
    program
        .model_invariants
        .retain(|definition| !removed_functions.contains(&definition.function_name));
}

fn type_def_name(type_def: &parser::TypeDefDecl) -> &str {
    match type_def {
        parser::TypeDefDecl::Struct(s) => &s.name,
        parser::TypeDefDecl::Enum(e) => &e.name,
    }
}

fn validate_function_signature_types(
    function_name: &str,
    sig: &FunctionSignature,
    type_definitions: &HashMap<String, TypeDef>,
    allow_void_return: bool,
) -> anyhow::Result<()> {
    let is_extern = allow_void_return;
    for param in &sig.parameters {
        let Some(param_type) = type_definitions.get(&param.ty) else {
            return Err(anyhow::anyhow!(
                "function {} has parameter {} with unknown type {}",
                function_name,
                param.name,
                param.ty
            ));
        };
        if param.ty == "Void" {
            return Err(anyhow::anyhow!(
                "function {} cannot use Void as parameter type ({})",
                function_name,
                param.name
            ));
        }
        if is_extern && matches!(param_type, TypeDef::Struct(_)) {
            return Err(anyhow::anyhow!(
                "extern function {} cannot use struct parameter type {} ({}) in v2 ABI; use PtrInt wrappers for C interop",
                function_name,
                param.ty,
                param.name
            ));
        }
    }

    let Some(return_type) = type_definitions.get(&sig.return_type) else {
        return Err(anyhow::anyhow!(
            "function {} has unknown return type {}",
            function_name,
            sig.return_type
        ));
    };

    if is_extern && matches!(return_type, TypeDef::Struct(_)) {
        return Err(anyhow::anyhow!(
            "extern function {} cannot return struct type {} in v2 ABI; use PtrInt wrappers for C interop",
            function_name,
            sig.return_type
        ));
    }

    Ok(())
}

fn validate_main_signature(program: &ResolvedProgram) -> anyhow::Result<()> {
    let main = program
        .function_definitions
        .get("main")
        .ok_or_else(|| anyhow::anyhow!("main function not defined"))?;

    if main.sig.return_type != "I32" {
        return Err(anyhow::anyhow!(
            "unsupported main signature: return type must be I32, got {}",
            main.sig.return_type
        ));
    }

    match main.sig.parameters.as_slice() {
        [] => Ok(()),
        [argc, argv]
            if argc.ty == "I32" && normalize_numeric_alias(&argv.ty) == "I64" =>
        {
            Ok(())
        }
        _ => Err(anyhow::anyhow!(
            "unsupported main signature: expected `fun main() -> I32`, `fun main(argc: I32, argv: I64) -> I32`, or `fun main(argc: I32, argv: PtrInt) -> I32`"
        )),
    }
}

fn reject_runtime_semantic_builtin_usage(program: &ResolvedProgram) -> anyhow::Result<()> {
    for function in program.function_definitions.values() {
        for statement in &function.body {
            let mut calls = Vec::new();
            collect_called_functions_in_statement(statement, program, &mut calls);
            for call in calls {
                if SEMANTIC_EMISSION_BUILTINS.contains(&call.as_str()) {
                    return Err(anyhow::anyhow!(
                        "runtime function {} cannot call semantic emission builtin {}",
                        function.name,
                        call
                    ));
                }
                if SEMANTIC_INTROSPECTION_BUILTINS.contains(&call.as_str()) {
                    return Err(anyhow::anyhow!(
                        "runtime function {} cannot call semantic introspection builtin {}",
                        function.name,
                        call
                    ));
                }
                if program.comptime_function_definitions.contains_key(&call) {
                    return Err(anyhow::anyhow!(
                        "runtime function {} cannot call comptime function {}",
                        function.name,
                        call
                    ));
                }
            }
        }
    }
    Ok(())
}

fn reject_model_invariant_impurity(program: &ResolvedProgram) -> anyhow::Result<()> {
    for model_invariant in &program.model_invariants {
        let mut visited = HashSet::new();
        let mut queue = vec![model_invariant.function_name.clone()];
        while let Some(function_name) = queue.pop() {
            if !visited.insert(function_name.clone()) {
                continue;
            }

            let function = program
                .function_definitions
                .get(&function_name)
                .ok_or_else(|| {
                    anyhow::anyhow!("missing function definition for {}", function_name)
                })?;
            for statement in &function.body {
                reject_model_invariant_impure_statement(
                    statement,
                    &function_name,
                    model_invariant,
                )?;
                reject_model_invariant_trait_static_calls(
                    statement,
                    &function_name,
                    model_invariant,
                    &program.trait_method_signatures,
                )?;

                let mut calls = Vec::new();
                collect_called_functions_in_statement(statement, program, &mut calls);
                for call in calls {
                    if MODEL_INVARIANT_SIDE_EFFECT_BUILTINS.contains(&call.as_str()) {
                        return Err(anyhow::anyhow!(
                            "model invariant \"{}\" must be pure: function {} calls side-effect builtin {}",
                            render_model_invariant_label(model_invariant),
                            function_name,
                            call
                        ));
                    }

                    let signature = program.function_sigs.get(&call).ok_or_else(|| {
                        anyhow::anyhow!(
                            "model invariant \"{}\" must be pure: function {} calls unknown function {}",
                            render_model_invariant_label(model_invariant),
                            function_name,
                            call
                        )
                    })?;
                    if signature.extern_symbol_name.is_some() {
                        return Err(anyhow::anyhow!(
                            "model invariant \"{}\" must be pure: function {} calls extern function {}",
                            render_model_invariant_label(model_invariant),
                            function_name,
                            call
                        ));
                    }

                    if program.function_definitions.contains_key(&call) {
                        queue.push(call);
                    }
                }
            }
        }
    }

    Ok(())
}

fn render_model_invariant_label(model_invariant: &ModelInvariantDefinition) -> String {
    if let Some(identifier) = &model_invariant.identifier {
        format!("{} (id={})", model_invariant.display_name, identifier)
    } else {
        model_invariant.display_name.clone()
    }
}

fn reject_model_invariant_impure_statement(
    statement: &parser::Statement,
    function_name: &str,
    model_invariant: &ModelInvariantDefinition,
) -> anyhow::Result<()> {
    match statement {
        parser::Statement::Prove { .. } => Err(anyhow::anyhow!(
            "model invariant \"{}\" must be pure: function {} contains prove(...) statement",
            render_model_invariant_label(model_invariant),
            function_name
        )),
        parser::Statement::Assert { .. } => Err(anyhow::anyhow!(
            "model invariant \"{}\" must be pure: function {} contains assert(...) statement",
            render_model_invariant_label(model_invariant),
            function_name
        )),
        parser::Statement::Conditional {
            body, else_body, ..
        } => {
            for nested in body {
                reject_model_invariant_impure_statement(nested, function_name, model_invariant)?;
            }
            if let Some(else_body) = else_body {
                for nested in else_body {
                    reject_model_invariant_impure_statement(
                        nested,
                        function_name,
                        model_invariant,
                    )?;
                }
            }
            Ok(())
        }
        parser::Statement::While { body, .. } => {
            for nested in body {
                reject_model_invariant_impure_statement(nested, function_name, model_invariant)?;
            }
            Ok(())
        }
        parser::Statement::Match { arms, .. } => {
            for arm in arms {
                for nested in &arm.body {
                    reject_model_invariant_impure_statement(
                        nested,
                        function_name,
                        model_invariant,
                    )?;
                }
            }
            Ok(())
        }
        parser::Statement::StructDef { .. }
        | parser::Statement::Assign { .. }
        | parser::Statement::Return { .. }
        | parser::Statement::Expression { .. } => Ok(()),
    }
}

fn reject_model_invariant_trait_static_calls(
    statement: &parser::Statement,
    function_name: &str,
    model_invariant: &ModelInvariantDefinition,
    trait_method_signatures: &HashMap<String, TraitMethodSignature>,
) -> anyhow::Result<()> {
    let mut trait_call = None::<String>;
    ast_walk::walk_statement_expressions(statement, "", AstPathStyle::Ir, &mut |_path, expr| {
        let parser::Expression::PostfixCall { callee, .. } = expr else {
            return;
        };
        let parser::Expression::FieldAccess {
            struct_variable,
            field,
        } = callee.as_ref()
        else {
            return;
        };
        if trait_method_signatures.contains_key(&trait_method_key(struct_variable, field)) {
            trait_call = Some(format!("{struct_variable}.{field}"));
        }
    });

    if let Some(trait_call) = trait_call {
        return Err(anyhow::anyhow!(
            "model invariant \"{}\" must be pure: function {} uses trait static call {} which is unsupported by purity policy",
            render_model_invariant_label(model_invariant),
            function_name,
            trait_call
        ));
    }
    Ok(())
}

fn collect_called_functions_in_statement(
    statement: &parser::Statement,
    program: &ResolvedProgram,
    out: &mut Vec<String>,
) {
    ast_walk::walk_statement_calls(statement, "", AstPathStyle::Ir, &mut |_path, call_name| {
        if call_name.contains(parser::NAMESPACE_FUNCTION_SEPARATOR)
            && !program.function_sigs.contains_key(call_name)
        {
            return;
        }
        out.push(call_name.to_string());
    });
}

fn index_semantic_expression_metadata(
    program: &ResolvedProgram,
) -> HashMap<String, SemanticExprMetadata> {
    let mut out = HashMap::new();
    for (name, function) in &program.function_definitions {
        for (precondition_index, expression) in function.preconditions.iter().enumerate() {
            index_expression_metadata(
                expression,
                &format!("fn:{name}/{}", local_precondition_key(precondition_index)),
                &local_precondition_key(precondition_index),
                &function.local_source_spans,
                &mut out,
            );
        }
        for (statement_index, statement) in function.body.iter().enumerate() {
            index_statement_expression_metadata(
                statement,
                &format!("fn:{name}"),
                &local_statement_key(statement_index),
                &function.local_source_spans,
                &mut out,
            );
        }
    }
    for (name, function) in &program.comptime_function_definitions {
        for (precondition_index, expression) in function.preconditions.iter().enumerate() {
            index_expression_metadata(
                expression,
                &format!(
                    "comptime_fn:{name}/{}",
                    local_precondition_key(precondition_index)
                ),
                &local_precondition_key(precondition_index),
                &function.local_source_spans,
                &mut out,
            );
        }
        for (statement_index, statement) in function.body.iter().enumerate() {
            index_statement_expression_metadata(
                statement,
                &format!("comptime_fn:{name}"),
                &local_statement_key(statement_index),
                &function.local_source_spans,
                &mut out,
            );
        }
    }
    out
}

fn index_expression_metadata(
    expression: &parser::Expression,
    full_expr_path: &str,
    local_expr_path: &str,
    local_source_spans: &HashMap<String, SourceSpan>,
    out: &mut HashMap<String, SemanticExprMetadata>,
) {
    ast_walk::walk_expression_tree(
        expression,
        local_expr_path,
        AstPathStyle::Ir,
        &mut |local_expr_path, _| {
            let expr_path = format!(
                "{}/{}",
                full_expr_path
                    .rsplit_once('/')
                    .map(|(prefix, _)| prefix)
                    .unwrap_or_default(),
                local_expr_path
            );
            out.insert(
                expr_path.clone(),
                SemanticExprMetadata {
                    id: expr_path,
                    ty: None,
                    source_span: local_source_spans.get(local_expr_path).cloned(),
                },
            );
        },
    );
}

fn index_statement_expression_metadata(
    statement: &parser::Statement,
    function_prefix: &str,
    local_statement_path: &str,
    local_source_spans: &HashMap<String, SourceSpan>,
    out: &mut HashMap<String, SemanticExprMetadata>,
) {
    ast_walk::walk_statement_expressions(
        statement,
        local_statement_path,
        AstPathStyle::Ir,
        &mut |local_expr_path, _| {
            let expr_path = format!("{function_prefix}/{local_expr_path}");
            out.insert(
                expr_path.clone(),
                SemanticExprMetadata {
                    id: expr_path,
                    ty: None,
                    source_span: local_source_spans.get(local_expr_path).cloned(),
                },
            );
        },
    );
}

fn parse_legacy_invariant_name(name: &str) -> Option<&str> {
    if !name.starts_with(LEGACY_INVARIANT_PREFIX) || !name.ends_with(LEGACY_INVARIANT_SUFFIX) {
        return None;
    }
    let middle = &name[LEGACY_INVARIANT_PREFIX.len()..name.len() - LEGACY_INVARIANT_SUFFIX.len()];
    if middle.is_empty() {
        None
    } else {
        Some(middle)
    }
}

fn sanitize_invariant_key(raw: &str) -> String {
    let mut key = String::with_capacity(raw.len());
    for ch in raw.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            key.push(ch);
        } else {
            key.push('_');
        }
    }
    if key.is_empty() {
        key.push_str("anon");
    }
    if key
        .chars()
        .next()
        .map(|ch| ch.is_ascii_digit())
        .unwrap_or(false)
    {
        key.insert(0, '_');
    }
    key
}

fn generated_invariant_function_name(struct_name: &str, key: &str) -> String {
    format!(
        "{}{}{}__{}",
        LEGACY_INVARIANT_PREFIX, struct_name, LEGACY_INVARIANT_SUFFIX, key
    )
}

fn generated_model_invariant_function_name(key: &str) -> String {
    format!("{MODEL_INVARIANT_PREFIX}{key}")
}

fn generated_precondition_function_name(function_name: &str, clause_ordinal: usize) -> String {
    format!("__pre__{}__clause_{}", function_name, clause_ordinal)
}

fn synthesize_precondition_functions(
    functions: &[parser::Function],
    out_function_preconditions: &mut HashMap<String, Vec<FunctionPreconditionDefinition>>,
) -> anyhow::Result<Vec<parser::Function>> {
    let mut out = Vec::new();
    let existing_function_names = functions
        .iter()
        .map(|function| function.name.clone())
        .collect::<HashSet<_>>();
    let mut generated_function_names = HashSet::<String>::new();

    for function in functions {
        if function.preconditions.is_empty() {
            continue;
        }
        if function.is_extern {
            return Err(anyhow::anyhow!(
                "extern function {} cannot use pre blocks in v1",
                function.name
            ));
        }
        if function.is_comptime {
            return Err(anyhow::anyhow!(
                "comptime function {} cannot use pre blocks in v1",
                function.name
            ));
        }

        let entry = out_function_preconditions
            .entry(function.name.clone())
            .or_default();
        for (clause_ordinal, expression) in function.preconditions.iter().enumerate() {
            let helper_function_name =
                generated_precondition_function_name(&function.name, clause_ordinal);
            if existing_function_names.contains(&helper_function_name)
                || !generated_function_names.insert(helper_function_name.clone())
            {
                return Err(anyhow::anyhow!(
                    "function {} precondition clause {} conflicts with existing function {}",
                    function.name,
                    clause_ordinal,
                    helper_function_name
                ));
            }

            entry.push(FunctionPreconditionDefinition {
                owner_function_name: function.name.clone(),
                helper_function_name: helper_function_name.clone(),
                clause_ordinal,
                source_span: function
                    .precondition_source_spans
                    .get(clause_ordinal)
                    .cloned(),
            });
            out.push(parser::Function {
                name: helper_function_name,
                extern_symbol_name: None,
                parameters: function.parameters.clone(),
                preconditions: vec![],
                body: vec![parser::Statement::Return {
                    expr: expression.clone(),
                }],
                return_type: "Bool".to_string(),
                is_comptime: false,
                is_extern: false,
                source_span: function
                    .precondition_source_spans
                    .get(clause_ordinal)
                    .cloned(),
                local_source_spans: HashMap::new(),
                precondition_source_spans: Vec::new(),
            });
        }
    }

    for definitions in out_function_preconditions.values_mut() {
        definitions.sort_by(|lhs, rhs| lhs.clause_ordinal.cmp(&rhs.clause_ordinal));
    }

    Ok(out)
}

fn synthesize_invariant_functions(
    invariants: &[parser::StructInvariantDecl],
    type_definitions: &HashMap<String, TypeDef>,
    existing_functions: &[parser::Function],
    out_struct_invariants: &mut HashMap<String, Vec<StructInvariantDefinition>>,
    out_model_invariants: &mut Vec<ModelInvariantDefinition>,
) -> anyhow::Result<Vec<parser::Function>> {
    let mut out = Vec::new();
    let mut seen_struct_explicit_identifiers = HashMap::<String, HashSet<String>>::new();
    let mut seen_model_explicit_identifiers = HashSet::<String>::new();
    let mut next_struct_anonymous_ordinal = HashMap::<String, usize>::new();
    let mut next_model_anonymous_ordinal = 0usize;
    let mut seen_model_keys = HashSet::<String>::new();
    let mut generated_function_names = HashSet::<String>::new();

    for invariant in invariants {
        if invariant.parameters.is_empty() {
            return Err(anyhow::anyhow!(
                "invariant \"{}\" requires at least one parameter",
                invariant.display_name
            ));
        }

        let key;
        let function_name;
        if invariant.parameters.len() == 1 {
            let struct_name = invariant.parameters[0].ty.clone();
            let type_def = type_definitions
                .get(&struct_name)
                .ok_or_else(|| anyhow::anyhow!("invariant targets unknown type {}", struct_name))?;
            if !matches!(type_def, TypeDef::Struct(_)) {
                return Err(anyhow::anyhow!(
                    "invariant \"{}\" must target a struct type, but {} is not a struct",
                    invariant.display_name,
                    struct_name
                ));
            }

            key = if let Some(identifier) = &invariant.identifier {
                let seen = seen_struct_explicit_identifiers
                    .entry(struct_name.clone())
                    .or_default();
                if !seen.insert(identifier.clone()) {
                    return Err(anyhow::anyhow!(
                        "struct {} has duplicate invariant identifier `{}`",
                        struct_name,
                        identifier
                    ));
                }
                sanitize_invariant_key(identifier)
            } else {
                let next = next_struct_anonymous_ordinal
                    .entry(struct_name.clone())
                    .or_insert(0);
                let key = format!("anon_{}", *next);
                *next += 1;
                key
            };

            function_name = generated_invariant_function_name(&struct_name, &key);
            if existing_functions.iter().any(|f| f.name == function_name)
                || !generated_function_names.insert(function_name.clone())
            {
                return Err(anyhow::anyhow!(
                    "invariant \"{}\" for {} conflicts with existing function {}",
                    invariant.display_name,
                    struct_name,
                    function_name
                ));
            }

            let entry = out_struct_invariants
                .entry(struct_name.clone())
                .or_default();
            if let Some(existing) = entry.iter().find(|existing| existing.key == key) {
                return Err(anyhow::anyhow!(
                    "struct {} has duplicate invariant key `{}`: \"{}\" and \"{}\"",
                    struct_name,
                    key,
                    existing.display_name,
                    invariant.display_name
                ));
            }
            entry.push(StructInvariantDefinition {
                struct_name,
                function_name: function_name.clone(),
                key: key.clone(),
                identifier: invariant.identifier.clone(),
                display_name: invariant.display_name.clone(),
                source_span: invariant.source_span.clone(),
            });
        } else {
            key = if let Some(identifier) = &invariant.identifier {
                if !seen_model_explicit_identifiers.insert(identifier.clone()) {
                    return Err(anyhow::anyhow!(
                        "model invariants have duplicate identifier `{}`",
                        identifier
                    ));
                }
                sanitize_invariant_key(identifier)
            } else {
                let key = format!("anon_{}", next_model_anonymous_ordinal);
                next_model_anonymous_ordinal += 1;
                key
            };
            if !seen_model_keys.insert(key.clone()) {
                return Err(anyhow::anyhow!(
                    "model invariants have duplicate key `{}`",
                    key
                ));
            }

            function_name = generated_model_invariant_function_name(&key);
            if existing_functions.iter().any(|f| f.name == function_name)
                || !generated_function_names.insert(function_name.clone())
            {
                return Err(anyhow::anyhow!(
                    "model invariant \"{}\" conflicts with existing function {}",
                    invariant.display_name,
                    function_name
                ));
            }

            out_model_invariants.push(ModelInvariantDefinition {
                function_name: function_name.clone(),
                key: key.clone(),
                identifier: invariant.identifier.clone(),
                display_name: invariant.display_name.clone(),
                source_span: invariant.source_span.clone(),
            });
        }

        out.push(parser::Function {
            name: function_name,
            extern_symbol_name: None,
            parameters: invariant.parameters.clone(),
            preconditions: vec![],
            body: invariant.body.clone(),
            return_type: "Bool".to_string(),
            is_comptime: false,
            is_extern: false,
            source_span: invariant.source_span.clone(),
            local_source_spans: invariant.local_source_spans.clone(),
            precondition_source_spans: Vec::new(),
        });
    }
    Ok(out)
}

fn register_legacy_struct_invariants(
    functions: &[parser::Function],
    type_definitions: &HashMap<String, TypeDef>,
    function_sigs: &HashMap<String, FunctionSignature>,
    out_struct_invariants: &mut HashMap<String, Vec<StructInvariantDefinition>>,
) -> anyhow::Result<()> {
    for function in functions {
        let Some(struct_name) = parse_legacy_invariant_name(&function.name) else {
            continue;
        };

        let Some(type_def) = type_definitions.get(struct_name) else {
            return Err(anyhow::anyhow!(
                "invariant {} targets unknown type {}",
                function.name,
                struct_name
            ));
        };
        if !matches!(type_def, TypeDef::Struct(_)) {
            return Err(anyhow::anyhow!(
                "invariant {} must target a struct type, but {} is not a struct",
                function.name,
                struct_name
            ));
        }

        let sig = function_sigs
            .get(&function.name)
            .ok_or_else(|| anyhow::anyhow!("missing signature for {}", function.name))?;
        if sig.parameters.len() != 1
            || sig.parameters[0].ty != struct_name
            || sig.return_type != "Bool"
        {
            return Err(anyhow::anyhow!(
                "invariant {} must have signature fun {}(v: {}) -> Bool",
                function.name,
                function.name,
                struct_name
            ));
        }

        let entry = out_struct_invariants
            .entry(struct_name.to_string())
            .or_default();
        if entry
            .iter()
            .any(|existing| existing.function_name == function.name)
        {
            continue;
        }
        if let Some(existing) = entry
            .iter()
            .find(|existing| existing.key == LEGACY_INVARIANT_KEY)
        {
            if existing.function_name != function.name {
                return Err(anyhow::anyhow!(
                    "struct {} has duplicate invariant key `{}`: \"{}\" and \"{}\"",
                    struct_name,
                    LEGACY_INVARIANT_KEY,
                    existing.display_name,
                    function.name
                ));
            }
            continue;
        }

        entry.push(StructInvariantDefinition {
            struct_name: struct_name.to_string(),
            function_name: function.name.clone(),
            key: LEGACY_INVARIANT_KEY.to_string(),
            identifier: None,
            display_name: function.name.clone(),
            source_span: function.source_span.clone(),
        });
    }
    Ok(())
}

fn replace_self_type(ty: &str, concrete_self: &str) -> String {
    let mut substitutions = HashMap::new();
    substitutions.insert("Self".to_string(), concrete_self.to_string());
    rewrite_type_ref(ty, &substitutions, &HashMap::new())
}

fn normalize_method_call_expression(
    receiver: &Expression,
    method: &str,
    args: &[Expression],
    var_types: &HashMap<String, TypeRef>,
    fns: &HashMap<String, FunctionSignature>,
    type_definitions: &HashMap<String, TypeDef>,
    trait_method_signatures: &HashMap<String, TraitMethodSignature>,
    trait_impl_methods: &HashMap<String, String>,
) -> anyhow::Result<Expression> {
    if let Expression::Variable(receiver_name) = receiver {
        if let Some(TypeDef::Enum(enum_def)) = type_definitions.get(receiver_name) {
            if enum_def
                .variants
                .iter()
                .any(|variant| variant.name == method)
            {
                return Ok(Expression::PostfixCall {
                    callee: Box::new(Expression::FieldAccess {
                        struct_variable: receiver_name.clone(),
                        field: method.to_string(),
                    }),
                    args: args.to_vec(),
                });
            }

            let namespaced_call = parser::qualify_namespace_function_name(receiver_name, method);
            if fns.contains_key(&namespaced_call) {
                return Ok(Expression::Call(namespaced_call, args.to_vec()));
            }

            return Err(anyhow::anyhow!(
                "variant {} not found in enum {}",
                method,
                receiver_name
            ));
        }

        if trait_method_signatures.contains_key(&trait_method_key(receiver_name, method)) {
            let (target, _) = resolve_trait_call_target(
                receiver_name,
                method,
                args,
                var_types,
                fns,
                type_definitions,
                trait_method_signatures,
                trait_impl_methods,
            )?;
            return Ok(match target {
                TraitCallTarget::Function(target_function) => {
                    Expression::Call(target_function, args.to_vec())
                }
                TraitCallTarget::BuiltinOperator(_) => Expression::PostfixCall {
                    callee: Box::new(Expression::FieldAccess {
                        struct_variable: receiver_name.clone(),
                        field: method.to_string(),
                    }),
                    args: args.to_vec(),
                },
            });
        }

        let namespaced_call = parser::qualify_namespace_function_name(receiver_name, method);
        if fns.contains_key(&namespaced_call) {
            return Ok(Expression::Call(namespaced_call, args.to_vec()));
        }
    }

    let receiver_type = get_expression_type(
        receiver,
        var_types,
        fns,
        type_definitions,
        trait_method_signatures,
        trait_impl_methods,
    )?;
    let namespaced_call = parser::qualify_namespace_function_name(&receiver_type, method);
    if !fns.contains_key(&namespaced_call) {
        return Err(anyhow::anyhow!(
            "method {}.{} not found for receiver type {}",
            receiver_type,
            method,
            receiver_type
        ));
    }

    let mut call_args = Vec::with_capacity(args.len() + 1);
    call_args.push(receiver.clone());
    call_args.extend(args.iter().cloned());
    Ok(Expression::Call(namespaced_call, call_args))
}

fn validate_special_trait_shape(trait_decl: &parser::TraitDecl) -> anyhow::Result<()> {
    let expect_binary_trait =
        |trait_name: &str, method_name: &str, return_type: &str| -> anyhow::Result<()> {
            if trait_decl.methods.len() != 1 {
                return Err(anyhow::anyhow!(
                    "trait {} must define {}(lhs: Self, rhs: Self) -> {}",
                    trait_name,
                    method_name,
                    return_type
                ));
            }
            let method = &trait_decl.methods[0];
            if method.name != method_name
                || method.parameters.len() != 2
                || method.parameters[0].ty != "Self"
                || method.parameters[1].ty != "Self"
                || method.return_type != return_type
            {
                return Err(anyhow::anyhow!(
                    "trait {} must define {}(lhs: Self, rhs: Self) -> {}",
                    trait_name,
                    method_name,
                    return_type
                ));
            }
            Ok(())
        };

    if trait_decl.name == "Copy" {
        if trait_decl.methods.len() != 1 {
            return Err(anyhow::anyhow!(
                "trait Copy must define copy(v: Ref[Self]) -> Self"
            ));
        }
        let method = &trait_decl.methods[0];
        if method.name != "copy"
            || method.parameters.len() != 1
            || method.parameters[0].ty != "Ref[Self]"
            || method.return_type != "Self"
        {
            return Err(anyhow::anyhow!(
                "trait Copy must define copy(v: Ref[Self]) -> Self"
            ));
        }
    }
    if trait_decl.name == "Drop" {
        if trait_decl.methods.len() != 1 {
            return Err(anyhow::anyhow!(
                "trait Drop must define drop(v: Self) -> Void"
            ));
        }
        let method = &trait_decl.methods[0];
        if method.name != "drop"
            || method.parameters.len() != 1
            || method.parameters[0].ty != "Self"
            || method.return_type != "Void"
        {
            return Err(anyhow::anyhow!(
                "trait Drop must define drop(v: Self) -> Void"
            ));
        }
    }
    if trait_decl.name == "Addition" {
        expect_binary_trait("Addition", "add", "Self")?;
    }
    if trait_decl.name == "Subtraction" {
        expect_binary_trait("Subtraction", "sub", "Self")?;
    }
    if trait_decl.name == "Multiplication" {
        expect_binary_trait("Multiplication", "mul", "Self")?;
    }
    if trait_decl.name == "Division" {
        expect_binary_trait("Division", "div", "Self")?;
    }
    if trait_decl.name == "Equality" {
        expect_binary_trait("Equality", "equals", "Bool")?;
    }
    if trait_decl.name == "Comparison" {
        expect_binary_trait("Comparison", "compare", "I32")?;
    }
    Ok(())
}

fn collect_trait_metadata(
    ast: &Ast,
) -> anyhow::Result<(
    HashMap<String, TraitMethodSignature>,
    HashMap<String, String>,
    HashSet<String>,
    Vec<parser::Function>,
)> {
    let mut trait_method_signatures = HashMap::new();
    let mut trait_methods_by_trait: HashMap<String, Vec<TraitMethodSignature>> = HashMap::new();

    for trait_decl in &ast.trait_declarations {
        validate_special_trait_shape(trait_decl)?;
        if trait_methods_by_trait.contains_key(&trait_decl.name) {
            return Err(anyhow::anyhow!(
                "duplicate trait declaration {}",
                trait_decl.name
            ));
        }
        let mut seen_method_names = HashSet::new();
        let mut methods = vec![];
        for method in &trait_decl.methods {
            if !seen_method_names.insert(method.name.clone()) {
                return Err(anyhow::anyhow!(
                    "duplicate method {} in trait {}",
                    method.name,
                    trait_decl.name
                ));
            }
            if method.parameters.is_empty() {
                return Err(anyhow::anyhow!(
                    "trait method {}.{} must take Self as the first parameter",
                    trait_decl.name,
                    method.name
                ));
            }
            if trait_decl.name != "Copy" && method.parameters[0].ty != "Self" {
                return Err(anyhow::anyhow!(
                    "trait method {}.{} must use Self as first parameter type in v1",
                    trait_decl.name,
                    method.name
                ));
            }
            let signature = TraitMethodSignature {
                trait_name: trait_decl.name.clone(),
                method_name: method.name.clone(),
                parameter_types: method.parameters.iter().map(|p| p.ty.clone()).collect(),
                return_type: method.return_type.clone(),
            };
            trait_method_signatures.insert(
                trait_method_key(&trait_decl.name, &method.name),
                signature.clone(),
            );
            methods.push(signature);
        }
        trait_methods_by_trait.insert(trait_decl.name.clone(), methods);
    }

    let mut trait_impl_methods = HashMap::new();
    let mut trait_impl_targets = HashSet::new();
    let mut impl_functions = vec![];

    for impl_decl in &ast.impl_declarations {
        if is_reserved_builtin_operator_impl(&impl_decl.trait_name, &impl_decl.for_type) {
            return Err(anyhow::anyhow!(
                "impl {} for {} is reserved to compiler builtin operator semantics",
                impl_decl.trait_name,
                impl_decl.for_type
            ));
        }
        let trait_methods = trait_methods_by_trait
            .get(&impl_decl.trait_name)
            .ok_or_else(|| anyhow::anyhow!("unknown trait {} in impl", impl_decl.trait_name))?;
        let target_key = trait_impl_target_key(&impl_decl.trait_name, &impl_decl.for_type);
        if !trait_impl_targets.insert(target_key) {
            return Err(anyhow::anyhow!(
                "duplicate impl for trait {} and type {}",
                impl_decl.trait_name,
                impl_decl.for_type
            ));
        }

        let mut impl_methods_by_name: HashMap<String, &parser::Function> = HashMap::new();
        for method in &impl_decl.methods {
            if method.is_comptime {
                return Err(anyhow::anyhow!(
                    "impl method {}.{} cannot be comptime in v1",
                    impl_decl.trait_name,
                    method.name
                ));
            }
            if method.is_extern {
                return Err(anyhow::anyhow!(
                    "impl method {}.{} cannot be extern in v1",
                    impl_decl.trait_name,
                    method.name
                ));
            }
            if impl_methods_by_name
                .insert(method.name.clone(), method)
                .is_some()
            {
                return Err(anyhow::anyhow!(
                    "duplicate impl method {} for trait {} and type {}",
                    method.name,
                    impl_decl.trait_name,
                    impl_decl.for_type
                ));
            }
        }

        for trait_method in trait_methods {
            let method = impl_methods_by_name
                .remove(&trait_method.method_name)
                .ok_or_else(|| {
                    anyhow::anyhow!(
                        "impl {} for {} is missing required method {}",
                        impl_decl.trait_name,
                        impl_decl.for_type,
                        trait_method.method_name
                    )
                })?;

            if method.parameters.len() != trait_method.parameter_types.len() {
                return Err(anyhow::anyhow!(
                    "impl method {}.{} has wrong arity: expected {}, got {}",
                    impl_decl.trait_name,
                    trait_method.method_name,
                    trait_method.parameter_types.len(),
                    method.parameters.len()
                ));
            }

            for (parameter, expected_ty) in method
                .parameters
                .iter()
                .zip(trait_method.parameter_types.iter())
            {
                let expected = replace_self_type(expected_ty, &impl_decl.for_type);
                let matches_expected =
                    normalize_numeric_alias(&parameter.ty) == normalize_numeric_alias(&expected);
                let matches_legacy_copy_by_value = impl_decl.trait_name == "Copy"
                    && trait_method.method_name == "copy"
                    && normalize_numeric_alias(&parameter.ty)
                        == normalize_numeric_alias(&impl_decl.for_type);
                let matches_copy_ref_alias = impl_decl.trait_name == "Copy"
                    && trait_method.method_name == "copy"
                    && parameter.ty.ends_with("Ref");
                if !matches_expected && !matches_legacy_copy_by_value && !matches_copy_ref_alias {
                    return Err(anyhow::anyhow!(
                        "impl method {}.{} parameter {} type mismatch: expected {}, got {}",
                        impl_decl.trait_name,
                        trait_method.method_name,
                        parameter.name,
                        expected,
                        parameter.ty
                    ));
                }
            }
            let expected_return = replace_self_type(&trait_method.return_type, &impl_decl.for_type);
            if normalize_numeric_alias(&method.return_type)
                != normalize_numeric_alias(&expected_return)
            {
                return Err(anyhow::anyhow!(
                    "impl method {}.{} return type mismatch: expected {}, got {}",
                    impl_decl.trait_name,
                    trait_method.method_name,
                    expected_return,
                    method.return_type
                ));
            }

            let function_name = trait_impl_function_name(
                &impl_decl.trait_name,
                &impl_decl.for_type,
                &trait_method.method_name,
            );
            trait_impl_methods.insert(
                trait_impl_method_key(
                    &impl_decl.trait_name,
                    &impl_decl.for_type,
                    &trait_method.method_name,
                ),
                function_name.clone(),
            );
            impl_functions.push(parser::Function {
                name: function_name,
                extern_symbol_name: None,
                parameters: method.parameters.clone(),
                preconditions: method.preconditions.clone(),
                body: method.body.clone(),
                return_type: method.return_type.clone(),
                is_comptime: false,
                is_extern: false,
                source_span: method.source_span.clone(),
                local_source_spans: method.local_source_spans.clone(),
                precondition_source_spans: method.precondition_source_spans.clone(),
            });
        }

        if let Some(extra_method_name) = impl_methods_by_name.keys().next() {
            return Err(anyhow::anyhow!(
                "impl {} for {} has unknown method {}",
                impl_decl.trait_name,
                impl_decl.for_type,
                extra_method_name
            ));
        }
    }

    seed_builtin_operator_trait_impl_targets(&trait_methods_by_trait, &mut trait_impl_targets);

    Ok((
        trait_method_signatures,
        trait_impl_methods,
        trait_impl_targets,
        impl_functions,
    ))
}

fn rewrite_identifier(
    identifier: &str,
    type_substitution_map: &HashMap<String, String>,
    local_type_name_map: &HashMap<String, String>,
) -> String {
    if let Some(mapped) = local_type_name_map.get(identifier) {
        mapped.clone()
    } else if let Some(mapped) = type_substitution_map.get(identifier) {
        mapped.clone()
    } else {
        identifier.to_string()
    }
}

fn rewrite_type_ref(
    ty: &str,
    type_substitution_map: &HashMap<String, String>,
    local_type_name_map: &HashMap<String, String>,
) -> String {
    let mut out = String::new();
    let mut identifier = String::new();
    for ch in ty.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            identifier.push(ch);
            continue;
        }
        if !identifier.is_empty() {
            out.push_str(&rewrite_identifier(
                &identifier,
                type_substitution_map,
                local_type_name_map,
            ));
            identifier.clear();
        }
        if !ch.is_whitespace() {
            out.push(ch);
        }
    }
    if !identifier.is_empty() {
        out.push_str(&rewrite_identifier(
            &identifier,
            type_substitution_map,
            local_type_name_map,
        ));
    }
    out
}

fn rewrite_expression(
    expr: &Expression,
    type_substitution_map: &HashMap<String, String>,
    local_type_name_map: &HashMap<String, String>,
    local_function_name_map: &HashMap<String, String>,
) -> Expression {
    match expr {
        Expression::Match { subject, arms } => Expression::Match {
            subject: Box::new(rewrite_expression(
                subject,
                type_substitution_map,
                local_type_name_map,
                local_function_name_map,
            )),
            arms: arms
                .iter()
                .map(|arm| parser::MatchExprArm {
                    pattern: match &arm.pattern {
                        parser::MatchPattern::Variant {
                            type_name,
                            variant_name,
                            binder,
                        } => parser::MatchPattern::Variant {
                            type_name: rewrite_identifier(
                                type_name,
                                type_substitution_map,
                                local_type_name_map,
                            ),
                            variant_name: variant_name.clone(),
                            binder: binder.clone(),
                        },
                    },
                    value: rewrite_expression(
                        &arm.value,
                        type_substitution_map,
                        local_type_name_map,
                        local_function_name_map,
                    ),
                })
                .collect(),
        },
        Expression::Literal(lit) => Expression::Literal(lit.clone()),
        Expression::Variable(name) => Expression::Variable(name.clone()),
        Expression::Call(name, args) => {
            let mapped_name = local_function_name_map
                .get(name)
                .cloned()
                .unwrap_or_else(|| name.clone());
            Expression::Call(
                mapped_name,
                args.iter()
                    .map(|arg| {
                        rewrite_expression(
                            arg,
                            type_substitution_map,
                            local_type_name_map,
                            local_function_name_map,
                        )
                    })
                    .collect(),
            )
        }
        Expression::MethodCall {
            receiver,
            method,
            args,
        } => Expression::MethodCall {
            receiver: Box::new(match receiver.as_ref() {
                Expression::Variable(name)
                    if local_type_name_map.contains_key(name)
                        || type_substitution_map.contains_key(name) =>
                {
                    Expression::Variable(rewrite_identifier(
                        name,
                        type_substitution_map,
                        local_type_name_map,
                    ))
                }
                _ => rewrite_expression(
                    receiver,
                    type_substitution_map,
                    local_type_name_map,
                    local_function_name_map,
                ),
            }),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| {
                    rewrite_expression(
                        arg,
                        type_substitution_map,
                        local_type_name_map,
                        local_function_name_map,
                    )
                })
                .collect(),
        },
        Expression::PostfixCall { callee, args } => Expression::PostfixCall {
            callee: Box::new(rewrite_expression(
                callee,
                type_substitution_map,
                local_type_name_map,
                local_function_name_map,
            )),
            args: args
                .iter()
                .map(|arg| {
                    rewrite_expression(
                        arg,
                        type_substitution_map,
                        local_type_name_map,
                        local_function_name_map,
                    )
                })
                .collect(),
        },
        Expression::BinOp(op, left, right) => Expression::BinOp(
            *op,
            Box::new(rewrite_expression(
                left,
                type_substitution_map,
                local_type_name_map,
                local_function_name_map,
            )),
            Box::new(rewrite_expression(
                right,
                type_substitution_map,
                local_type_name_map,
                local_function_name_map,
            )),
        ),
        Expression::UnaryOp(op, expr) => Expression::UnaryOp(
            *op,
            Box::new(rewrite_expression(
                expr,
                type_substitution_map,
                local_type_name_map,
                local_function_name_map,
            )),
        ),
        Expression::FieldAccess {
            struct_variable,
            field,
        } => Expression::FieldAccess {
            struct_variable: rewrite_identifier(
                struct_variable,
                type_substitution_map,
                local_type_name_map,
            ),
            field: field.clone(),
        },
        Expression::StructValue {
            struct_name,
            field_values,
        } => Expression::StructValue {
            struct_name: rewrite_identifier(
                struct_name,
                type_substitution_map,
                local_type_name_map,
            ),
            field_values: field_values
                .iter()
                .map(|(name, expr)| {
                    (
                        name.clone(),
                        rewrite_expression(
                            expr,
                            type_substitution_map,
                            local_type_name_map,
                            local_function_name_map,
                        ),
                    )
                })
                .collect(),
        },
    }
}

fn rewrite_statement(
    statement: &parser::Statement,
    type_substitution_map: &HashMap<String, String>,
    local_type_name_map: &HashMap<String, String>,
    local_function_name_map: &HashMap<String, String>,
) -> parser::Statement {
    match statement {
        parser::Statement::StructDef { def } => parser::Statement::StructDef { def: def.clone() },
        parser::Statement::Match { subject, arms } => parser::Statement::Match {
            subject: rewrite_expression(
                subject,
                type_substitution_map,
                local_type_name_map,
                local_function_name_map,
            ),
            arms: arms
                .iter()
                .map(|arm| parser::MatchArm {
                    pattern: match &arm.pattern {
                        parser::MatchPattern::Variant {
                            type_name,
                            variant_name,
                            binder,
                        } => parser::MatchPattern::Variant {
                            type_name: rewrite_identifier(
                                type_name,
                                type_substitution_map,
                                local_type_name_map,
                            ),
                            variant_name: variant_name.clone(),
                            binder: binder.clone(),
                        },
                    },
                    body: arm
                        .body
                        .iter()
                        .map(|statement| {
                            rewrite_statement(
                                statement,
                                type_substitution_map,
                                local_type_name_map,
                                local_function_name_map,
                            )
                        })
                        .collect(),
                })
                .collect(),
        },
        parser::Statement::Conditional {
            condition,
            body,
            else_body,
        } => parser::Statement::Conditional {
            condition: rewrite_expression(
                condition,
                type_substitution_map,
                local_type_name_map,
                local_function_name_map,
            ),
            body: body
                .iter()
                .map(|statement| {
                    rewrite_statement(
                        statement,
                        type_substitution_map,
                        local_type_name_map,
                        local_function_name_map,
                    )
                })
                .collect(),
            else_body: else_body.as_ref().map(|body| {
                body.iter()
                    .map(|statement| {
                        rewrite_statement(
                            statement,
                            type_substitution_map,
                            local_type_name_map,
                            local_function_name_map,
                        )
                    })
                    .collect()
            }),
        },
        parser::Statement::Assign { variable, value } => parser::Statement::Assign {
            variable: variable.clone(),
            value: rewrite_expression(
                value,
                type_substitution_map,
                local_type_name_map,
                local_function_name_map,
            ),
        },
        parser::Statement::Return { expr } => parser::Statement::Return {
            expr: rewrite_expression(
                expr,
                type_substitution_map,
                local_type_name_map,
                local_function_name_map,
            ),
        },
        parser::Statement::Expression { expr } => parser::Statement::Expression {
            expr: rewrite_expression(
                expr,
                type_substitution_map,
                local_type_name_map,
                local_function_name_map,
            ),
        },
        parser::Statement::Prove { condition } => parser::Statement::Prove {
            condition: rewrite_expression(
                condition,
                type_substitution_map,
                local_type_name_map,
                local_function_name_map,
            ),
        },
        parser::Statement::Assert { condition } => parser::Statement::Assert {
            condition: rewrite_expression(
                condition,
                type_substitution_map,
                local_type_name_map,
                local_function_name_map,
            ),
        },
        parser::Statement::While { condition, body } => parser::Statement::While {
            condition: rewrite_expression(
                condition,
                type_substitution_map,
                local_type_name_map,
                local_function_name_map,
            ),
            body: body
                .iter()
                .map(|statement| {
                    rewrite_statement(
                        statement,
                        type_substitution_map,
                        local_type_name_map,
                        local_function_name_map,
                    )
                })
                .collect(),
        },
    }
}

fn expand_generics(
    ast: &mut Ast,
    trait_method_signatures: &HashMap<String, TraitMethodSignature>,
    trait_impl_targets: &HashSet<String>,
) -> anyhow::Result<()> {
    let mut generics_by_name: HashMap<String, parser::GenericDef> = HashMap::new();
    for generic in &ast.generic_definitions {
        if generics_by_name
            .insert(generic.name.clone(), generic.clone())
            .is_some()
        {
            return Err(anyhow::anyhow!(
                "duplicate generic definition {}",
                generic.name
            ));
        }
    }

    let declared_traits = ast
        .trait_declarations
        .iter()
        .map(|trait_decl| trait_decl.name.clone())
        .collect::<HashSet<_>>();
    if declared_traits.is_empty() && !trait_method_signatures.is_empty() {
        return Err(anyhow::anyhow!(
            "internal trait metadata mismatch: method signatures exist without trait declarations"
        ));
    }

    let mut used_type_names = HashSet::new();
    for type_def in &ast.type_definitions {
        used_type_names.insert(type_def_name(type_def).to_string());
    }
    let mut used_function_names = HashSet::new();
    for function in &ast.top_level_functions {
        used_function_names.insert(function.name.clone());
    }

    let mut generated_type_defs = vec![];
    let mut generated_functions = vec![];
    let mut generated_invariants = vec![];

    for specialization in &ast.generic_specializations {
        let generic = generics_by_name
            .get(&specialization.generic_name)
            .ok_or_else(|| {
                anyhow::anyhow!(
                    "unknown generic {} in specialization {}",
                    specialization.generic_name,
                    specialization.alias
                )
            })?;
        let mut active_generic_stack = Vec::new();
        expand_one_generic_specialization(
            generic,
            &specialization.alias,
            &specialization.concrete_types,
            &generics_by_name,
            &declared_traits,
            trait_impl_targets,
            &mut used_type_names,
            &mut used_function_names,
            &mut generated_type_defs,
            &mut generated_functions,
            &mut generated_invariants,
            &mut active_generic_stack,
        )?;
    }

    ast.type_definitions.extend(generated_type_defs);
    ast.top_level_functions.extend(generated_functions);
    ast.invariants.extend(generated_invariants);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn expand_one_generic_specialization(
    generic: &parser::GenericDef,
    specialization_alias: &str,
    concrete_types: &[String],
    generics_by_name: &HashMap<String, parser::GenericDef>,
    declared_traits: &HashSet<String>,
    trait_impl_targets: &HashSet<String>,
    used_type_names: &mut HashSet<String>,
    used_function_names: &mut HashSet<String>,
    generated_type_defs: &mut Vec<parser::TypeDefDecl>,
    generated_functions: &mut Vec<parser::Function>,
    generated_invariants: &mut Vec<parser::StructInvariantDecl>,
    active_generic_stack: &mut Vec<String>,
) -> anyhow::Result<()> {
    if generic.params.len() != concrete_types.len() {
        return Err(anyhow::anyhow!(
            "generic {} expects {} type arguments in specialization {}, got {}",
            generic.name,
            generic.params.len(),
            specialization_alias,
            concrete_types.len()
        ));
    }

    if active_generic_stack.contains(&generic.name) {
        let mut cycle = active_generic_stack.clone();
        cycle.push(generic.name.clone());
        return Err(anyhow::anyhow!(
            "generic specialization cycle detected: {}",
            cycle.join(" -> ")
        ));
    }
    active_generic_stack.push(generic.name.clone());

    let mut type_substitution_map: HashMap<String, String> = HashMap::new();
    for (parameter, concrete_type) in generic.params.iter().zip(concrete_types) {
        type_substitution_map.insert(parameter.name.clone(), concrete_type.clone());
        for bound in &parameter.bounds {
            if !declared_traits.contains(bound) {
                return Err(anyhow::anyhow!(
                    "unknown trait bound {} for parameter {} in generic {}",
                    bound,
                    parameter.name,
                    generic.name
                ));
            }
            let impl_target = trait_impl_target_key(bound, concrete_type);
            if !trait_impl_targets.contains(&impl_target) {
                return Err(anyhow::anyhow!(
                    "missing impl {} for {} required by generic {} parameter {} in specialization {}",
                    bound,
                    concrete_type,
                    generic.name,
                    parameter.name,
                    specialization_alias
                ));
            }
        }
    }

    let mut local_type_name_map: HashMap<String, String> = HashMap::new();
    for type_def in &generic.type_definitions {
        let local_name = type_def_name(type_def).to_string();
        let mapped_name = if local_name == generic.name {
            specialization_alias.to_string()
        } else {
            format!("{specialization_alias}__{local_name}")
        };
        local_type_name_map.insert(local_name, mapped_name);
    }

    for local_specialization in &generic.generic_specializations {
        let mapped_name = format!("{specialization_alias}__{}", local_specialization.alias);
        if local_type_name_map
            .insert(local_specialization.alias.clone(), mapped_name)
            .is_some()
        {
            return Err(anyhow::anyhow!(
                "duplicate local specialization alias {} in generic {}",
                local_specialization.alias,
                generic.name
            ));
        }
    }

    if !local_type_name_map.contains_key(&generic.name) {
        return Err(anyhow::anyhow!(
            "generic {} must define a primary type named {}",
            generic.name,
            generic.name
        ));
    }

    let mut local_function_name_map: HashMap<String, String> = HashMap::new();
    for function in &generic.top_level_functions {
        local_function_name_map.insert(
            function.name.clone(),
            format!("{specialization_alias}__{}", function.name),
        );
    }

    for type_def in &generic.type_definitions {
        let local_name = type_def_name(type_def);
        let Some(mapped_name) = local_type_name_map.get(local_name) else {
            return Err(anyhow::anyhow!(
                "internal generic expansion error: missing mapped type name {} in specialization {}",
                local_name,
                specialization_alias
            ));
        };
        if !used_type_names.insert(mapped_name.clone()) {
            return Err(anyhow::anyhow!(
                "duplicate generated type name {} from specialization {}",
                mapped_name,
                specialization_alias
            ));
        }
    }
    for mapped_name in local_function_name_map.values() {
        if !used_function_names.insert(mapped_name.clone()) {
            return Err(anyhow::anyhow!(
                "duplicate generated function name {} from specialization {}",
                mapped_name,
                specialization_alias
            ));
        }
    }

    for type_def in &generic.type_definitions {
        let rewritten = match type_def {
            parser::TypeDefDecl::Struct(struct_def) => {
                parser::TypeDefDecl::Struct(parser::StructDef {
                    name: local_type_name_map
                        .get(&struct_def.name)
                        .cloned()
                        .unwrap_or_else(|| struct_def.name.clone()),
                    struct_fields: struct_def
                        .struct_fields
                        .iter()
                        .map(|field| parser::StructField {
                            name: field.name.clone(),
                            ty: rewrite_type_ref(
                                &field.ty,
                                &type_substitution_map,
                                &local_type_name_map,
                            ),
                        })
                        .collect(),
                })
            }
            parser::TypeDefDecl::Enum(enum_def) => parser::TypeDefDecl::Enum(parser::EnumDef {
                name: local_type_name_map
                    .get(&enum_def.name)
                    .cloned()
                    .unwrap_or_else(|| enum_def.name.clone()),
                variants: enum_def
                    .variants
                    .iter()
                    .map(|variant| parser::EnumVariantDef {
                        name: variant.name.clone(),
                        payload_ty: variant.payload_ty.as_ref().map(|payload_ty| {
                            rewrite_type_ref(
                                payload_ty,
                                &type_substitution_map,
                                &local_type_name_map,
                            )
                        }),
                    })
                    .collect(),
            }),
        };
        generated_type_defs.push(rewritten);
    }

    for function in &generic.top_level_functions {
        generated_functions.push(parser::Function {
            name: local_function_name_map
                .get(&function.name)
                .cloned()
                .unwrap_or_else(|| function.name.clone()),
            extern_symbol_name: function.extern_symbol_name.clone(),
            parameters: function
                .parameters
                .iter()
                .map(|param| parser::Parameter {
                    name: param.name.clone(),
                    ty: rewrite_type_ref(&param.ty, &type_substitution_map, &local_type_name_map),
                })
                .collect(),
            preconditions: function
                .preconditions
                .iter()
                .map(|expression| {
                    rewrite_expression(
                        expression,
                        &type_substitution_map,
                        &local_type_name_map,
                        &local_function_name_map,
                    )
                })
                .collect(),
            body: function
                .body
                .iter()
                .map(|statement| {
                    rewrite_statement(
                        statement,
                        &type_substitution_map,
                        &local_type_name_map,
                        &local_function_name_map,
                    )
                })
                .collect(),
            return_type: rewrite_type_ref(
                &function.return_type,
                &type_substitution_map,
                &local_type_name_map,
            ),
            is_comptime: function.is_comptime,
            is_extern: function.is_extern,
            source_span: function.source_span.clone(),
            local_source_spans: function.local_source_spans.clone(),
            precondition_source_spans: function.precondition_source_spans.clone(),
        });
    }

    for invariant in &generic.invariants {
        generated_invariants.push(parser::StructInvariantDecl {
            identifier: invariant.identifier.clone(),
            display_name: invariant.display_name.clone(),
            parameters: invariant
                .parameters
                .iter()
                .map(|parameter| parser::Parameter {
                    name: parameter.name.clone(),
                    ty: rewrite_type_ref(
                        &parameter.ty,
                        &type_substitution_map,
                        &local_type_name_map,
                    ),
                })
                .collect(),
            body: invariant
                .body
                .iter()
                .map(|statement| {
                    rewrite_statement(
                        statement,
                        &type_substitution_map,
                        &local_type_name_map,
                        &local_function_name_map,
                    )
                })
                .collect(),
            source_span: invariant.source_span.clone(),
            local_source_spans: invariant.local_source_spans.clone(),
        });
    }

    for local_specialization in &generic.generic_specializations {
        let local_generic = generics_by_name
            .get(&local_specialization.generic_name)
            .ok_or_else(|| {
                anyhow::anyhow!(
                    "unknown generic {} in local specialization {} inside generic {}",
                    local_specialization.generic_name,
                    local_specialization.alias,
                    generic.name
                )
            })?;
        let local_alias = local_type_name_map
            .get(&local_specialization.alias)
            .cloned()
            .ok_or_else(|| {
                anyhow::anyhow!(
                    "internal generic expansion error: unresolved local specialization alias {} in generic {}",
                    local_specialization.alias,
                    generic.name
                )
            })?;
        let rewritten_concrete_types = local_specialization
            .concrete_types
            .iter()
            .map(|ty| rewrite_type_ref(ty, &type_substitution_map, &local_type_name_map))
            .collect::<Vec<_>>();
        expand_one_generic_specialization(
            local_generic,
            &local_alias,
            &rewritten_concrete_types,
            generics_by_name,
            declared_traits,
            trait_impl_targets,
            used_type_names,
            used_function_names,
            generated_type_defs,
            generated_functions,
            generated_invariants,
            active_generic_stack,
        )?;
    }

    active_generic_stack.pop();
    Ok(())
}

pub(crate) fn get_expression_type(
    expr: &Expression,
    var_types: &HashMap<String, TypeRef>,
    fns: &HashMap<String, FunctionSignature>,
    type_definitions: &HashMap<String, TypeDef>,
    trait_method_signatures: &HashMap<String, TraitMethodSignature>,
    trait_impl_methods: &HashMap<String, String>,
) -> anyhow::Result<TypeRef> {
    match expr {
        Expression::Match { subject, arms } => {
            let subject_type = get_expression_type(
                subject,
                var_types,
                fns,
                type_definitions,
                trait_method_signatures,
                trait_impl_methods,
            )?;
            let enum_def = match type_definitions.get(&subject_type) {
                Some(TypeDef::Enum(enum_def)) => enum_def,
                _ => {
                    return Err(anyhow::anyhow!(
                        "match subject must be an enum, got {:?}",
                        subject_type
                    ));
                }
            };

            let mut seen_variants = HashSet::new();
            let mut arm_value_type: Option<TypeRef> = None;
            for arm in arms {
                let (type_name, variant_name, binder) = match &arm.pattern {
                    parser::MatchPattern::Variant {
                        type_name,
                        variant_name,
                        binder,
                    } => (type_name, variant_name, binder),
                };

                if type_name != &subject_type {
                    return Err(anyhow::anyhow!(
                        "match arm type {:?} does not match subject type {:?}",
                        type_name,
                        subject_type
                    ));
                }
                if !seen_variants.insert(variant_name.clone()) {
                    return Err(anyhow::anyhow!(
                        "duplicate match arm for variant {}",
                        variant_name
                    ));
                }

                let variant = enum_def
                    .variants
                    .iter()
                    .find(|v| v.name == *variant_name)
                    .ok_or_else(|| {
                        anyhow::anyhow!(
                            "unknown variant {} for enum {}",
                            variant_name,
                            enum_def.name
                        )
                    })?;

                let mut scoped_var_types = var_types.clone();
                match (&variant.payload_ty, binder) {
                    (Some(payload_ty), Some(binder_name)) => {
                        scoped_var_types.insert(binder_name.clone(), payload_ty.clone());
                    }
                    (Some(_), None) => {
                        return Err(anyhow::anyhow!(
                            "match arm for payload variant {} must bind a payload",
                            variant_name
                        ));
                    }
                    (None, Some(_)) => {
                        return Err(anyhow::anyhow!(
                            "match arm for non-payload variant {} cannot bind a payload",
                            variant_name
                        ));
                    }
                    (None, None) => {}
                }

                let ty = get_expression_type(
                    &arm.value,
                    &scoped_var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if let Some(expected_ty) = arm_value_type.as_ref() {
                    if expected_ty != &ty {
                        return Err(anyhow::anyhow!(
                            "match expression arm type mismatch: expected {:?}, got {:?}",
                            expected_ty,
                            ty
                        ));
                    }
                } else {
                    arm_value_type = Some(ty);
                }
            }

            let missing = enum_def
                .variants
                .iter()
                .filter(|v| !seen_variants.contains(&v.name))
                .map(|v| v.name.clone())
                .collect::<Vec<_>>();
            if !missing.is_empty() {
                return Err(anyhow::anyhow!(
                    "non-exhaustive match on {}: missing variants {:?}",
                    enum_def.name,
                    missing
                ));
            }

            arm_value_type
                .ok_or_else(|| anyhow::anyhow!("match expression must have at least one arm"))
        }
        Expression::FieldAccess {
            struct_variable,
            field: field_name,
        } => {
            if var_types.contains_key(struct_variable) {
                let struct_type = get_expression_type(
                    &Expression::Variable(struct_variable.clone()),
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let type_def = type_definitions
                    .get(&struct_type)
                    .ok_or_else(|| anyhow::anyhow!("unknown type {}", struct_type))?;
                if let TypeDef::Struct(struct_def) = type_def {
                    let field = struct_def
                        .struct_fields
                        .iter()
                        .find(|field| field.name == *field_name)
                        .ok_or_else(|| {
                            anyhow::anyhow!(
                                "field {} not found in struct {}",
                                field_name,
                                struct_type
                            )
                        })?;
                    Ok(field.ty.clone())
                } else {
                    Err(anyhow::anyhow!("expected struct, but got {}", struct_type))
                }
            } else {
                let enum_def = match type_definitions.get(struct_variable) {
                    Some(TypeDef::Enum(enum_def)) => enum_def,
                    _ => return Err(anyhow::anyhow!("unknown variable {}", struct_variable)),
                };
                let variant = enum_def
                    .variants
                    .iter()
                    .find(|v| v.name == *field_name)
                    .ok_or_else(|| {
                        anyhow::anyhow!(
                            "variant {} not found in enum {}",
                            field_name,
                            struct_variable
                        )
                    })?;
                if variant.payload_ty.is_some() {
                    return Err(anyhow::anyhow!(
                        "variant {}.{} requires payload constructor call",
                        struct_variable,
                        field_name
                    ));
                }
                Ok(enum_def.name.clone())
            }
        }
        Expression::MethodCall {
            receiver,
            method,
            args,
        } => {
            let normalized = normalize_method_call_expression(
                receiver,
                method,
                args,
                var_types,
                fns,
                type_definitions,
                trait_method_signatures,
                trait_impl_methods,
            )?;
            get_expression_type(
                &normalized,
                var_types,
                fns,
                type_definitions,
                trait_method_signatures,
                trait_impl_methods,
            )
        }
        Expression::PostfixCall { callee, args } => match callee.as_ref() {
            Expression::FieldAccess {
                struct_variable,
                field,
            } => {
                if let Some(TypeDef::Enum(enum_def)) = type_definitions.get(struct_variable) {
                    if let Some(variant) = enum_def.variants.iter().find(|v| v.name == *field) {
                        let payload_ty = variant.payload_ty.as_ref().ok_or_else(|| {
                            anyhow::anyhow!(
                                "tag-only variant {}.{} does not accept payload",
                                struct_variable,
                                field
                            )
                        })?;
                        if args.len() != 1 {
                            return Err(anyhow::anyhow!(
                                "expected 1 payload argument for constructor {}.{}, got {}",
                                struct_variable,
                                field,
                                args.len()
                            ));
                        }
                        let arg_ty = get_expression_type(
                            &args[0],
                            var_types,
                            fns,
                            type_definitions,
                            trait_method_signatures,
                            trait_impl_methods,
                        )?;
                        if &arg_ty != payload_ty {
                            return Err(anyhow::anyhow!(
                                "mismatched payload type for {}.{}: expected {}, got {}",
                                struct_variable,
                                field,
                                payload_ty,
                                arg_ty
                            ));
                        }
                        return Ok(enum_def.name.clone());
                    }

                    let namespaced_call =
                        parser::qualify_namespace_function_name(struct_variable, field);
                    if fns.contains_key(&namespaced_call) {
                        return get_expression_type(
                            &Expression::Call(namespaced_call, args.clone()),
                            var_types,
                            fns,
                            type_definitions,
                            trait_method_signatures,
                            trait_impl_methods,
                        );
                    }

                    return Err(anyhow::anyhow!(
                        "variant {} not found in enum {}",
                        field,
                        struct_variable
                    ));
                }

                if trait_method_signatures.contains_key(&trait_method_key(struct_variable, field)) {
                    let (_, return_type) = resolve_trait_call_target(
                        struct_variable,
                        field,
                        args,
                        var_types,
                        fns,
                        type_definitions,
                        trait_method_signatures,
                        trait_impl_methods,
                    )?;
                    return Ok(return_type);
                }

                let namespaced_call =
                    parser::qualify_namespace_function_name(struct_variable, field);
                if fns.contains_key(&namespaced_call) {
                    return get_expression_type(
                        &Expression::Call(namespaced_call, args.clone()),
                        var_types,
                        fns,
                        type_definitions,
                        trait_method_signatures,
                        trait_impl_methods,
                    );
                }

                Err(anyhow::anyhow!(
                    "{}",
                    format_unsupported_call_target_message(callee.as_ref())
                ))
            }
            _ => Err(anyhow::anyhow!(
                "{}",
                format_unsupported_call_target_message(callee.as_ref())
            )),
        },
        Expression::StructValue {
            struct_name,
            field_values,
        } => {
            let type_def = type_definitions
                .get(struct_name)
                .ok_or_else(|| anyhow::anyhow!("unknown type {}", struct_name))?;
            if let TypeDef::Struct(struct_def) = type_def {
                for (name, value) in field_values {
                    let field = struct_def
                        .struct_fields
                        .iter()
                        .find(|field| &field.name == name)
                        .ok_or_else(|| {
                            anyhow::anyhow!("field {} not found in struct {}", name, struct_name)
                        })?;
                    let value_type = get_expression_type(
                        value,
                        var_types,
                        fns,
                        type_definitions,
                        trait_method_signatures,
                        trait_impl_methods,
                    )?;
                    if field.ty != value_type {
                        return Err(anyhow::anyhow!(
                            "mismatched types for field {}: expected {}, but got {}",
                            name,
                            field.ty,
                            value_type
                        ));
                    }
                }
                Ok(struct_name.clone())
            } else {
                Err(anyhow::anyhow!("expected struct, but got {}", struct_name))
            }
        }
        Expression::Literal(Literal::Int(_)) => Ok("I32".to_string()),
        Expression::Literal(Literal::Float32(_)) => Ok("FP32".to_string()),
        Expression::Literal(Literal::Float64(_)) => Ok("FP64".to_string()),
        Expression::Literal(Literal::String(_)) => Ok("String".to_string()),
        Expression::Literal(Literal::Bool(_)) => Ok("Bool".to_string()),
        Expression::Variable(name) => var_types
            .get(name)
            .ok_or_else(|| anyhow::anyhow!("unknown variable {}", name))
            .map(|ty| ty.clone()),
        Expression::Call(function, arguments) => {
            if function == "prove" || function == "assert" {
                return Err(anyhow::anyhow!(
                    "{}(...) is statement-only and cannot be used as an expression",
                    function
                ));
            }
            if function == META_TYPE_NAME_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one Type argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if arg_ty != "Type" {
                    return Err(anyhow::anyhow!(
                        "{} expects Type argument, got {}",
                        function,
                        arg_ty
                    ));
                }
                return Ok("String".to_string());
            }
            if function == META_RESOLVE_TYPE_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one String argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if arg_ty != "String" {
                    return Err(anyhow::anyhow!(
                        "{} expects String argument, got {}",
                        function,
                        arg_ty
                    ));
                }
                return Ok("Type".to_string());
            }
            if function == META_EXPR_OPT_FUNCTION || function == META_EXPR_METADATA_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                return Ok("SemanticExprOpt".to_string());
            }
            if function == META_DEFINITION_LOCATION_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                return Ok("SourceSpanOpt".to_string());
            }
            if function == META_IS_STRUCT_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one Type argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if arg_ty != "Type" {
                    return Err(anyhow::anyhow!(
                        "{} expects Type argument, got {}",
                        function,
                        arg_ty
                    ));
                }
                return Ok("Bool".to_string());
            }
            if function == META_IS_ENUM_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one Type argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if arg_ty != "Type" {
                    return Err(anyhow::anyhow!(
                        "{} expects Type argument, got {}",
                        function,
                        arg_ty
                    ));
                }
                return Ok("Bool".to_string());
            }
            if function == META_AS_STRUCT_OPT_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one Type argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if arg_ty != "Type" {
                    return Err(anyhow::anyhow!(
                        "{} expects Type argument, got {}",
                        function,
                        arg_ty
                    ));
                }
                return Ok("StructInfoOpt".to_string());
            }
            if function == META_AS_ENUM_OPT_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one Type argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if arg_ty != "Type" {
                    return Err(anyhow::anyhow!(
                        "{} expects Type argument, got {}",
                        function,
                        arg_ty
                    ));
                }
                return Ok("EnumInfoOpt".to_string());
            }
            if function == META_STRUCT_FIELD_COUNT_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one StructInfo argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if arg_ty != "StructInfo" {
                    return Err(anyhow::anyhow!(
                        "{} expects StructInfo argument, got {}",
                        function,
                        arg_ty
                    ));
                }
                return Ok("I32".to_string());
            }
            if function == META_ENUM_VARIANT_COUNT_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one EnumInfo argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if arg_ty != "EnumInfo" {
                    return Err(anyhow::anyhow!(
                        "{} expects EnumInfo argument, got {}",
                        function,
                        arg_ty
                    ));
                }
                return Ok("I32".to_string());
            }
            if function == META_STRUCT_FIELD_AT_INTRINSIC {
                if arguments.len() != 2 {
                    return Err(anyhow::anyhow!(
                        "{} expects (StructInfo, I32), got {} arguments",
                        function,
                        arguments.len()
                    ));
                }
                let a = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let b = get_expression_type(
                    &arguments[1],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if a != "StructInfo" || b != "I32" {
                    return Err(anyhow::anyhow!(
                        "{} expects (StructInfo, I32), got ({}, {})",
                        function,
                        a,
                        b
                    ));
                }
                return Ok("FieldInfoOpt".to_string());
            }
            if function == META_ENUM_VARIANT_AT_INTRINSIC {
                if arguments.len() != 2 {
                    return Err(anyhow::anyhow!(
                        "{} expects (EnumInfo, I32), got {} arguments",
                        function,
                        arguments.len()
                    ));
                }
                let a = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let b = get_expression_type(
                    &arguments[1],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if a != "EnumInfo" || b != "I32" {
                    return Err(anyhow::anyhow!(
                        "{} expects (EnumInfo, I32), got ({}, {})",
                        function,
                        a,
                        b
                    ));
                }
                return Ok("VariantInfoOpt".to_string());
            }
            if function == META_FIELD_NAME_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one FieldInfo argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if arg_ty != "FieldInfo" {
                    return Err(anyhow::anyhow!(
                        "{} expects FieldInfo argument, got {}",
                        function,
                        arg_ty
                    ));
                }
                return Ok("String".to_string());
            }
            if function == META_VARIANT_NAME_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one VariantInfo argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if arg_ty != "VariantInfo" {
                    return Err(anyhow::anyhow!(
                        "{} expects VariantInfo argument, got {}",
                        function,
                        arg_ty
                    ));
                }
                return Ok("String".to_string());
            }
            if function == META_FIELD_TYPE_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one FieldInfo argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if arg_ty != "FieldInfo" {
                    return Err(anyhow::anyhow!(
                        "{} expects FieldInfo argument, got {}",
                        function,
                        arg_ty
                    ));
                }
                return Ok("Type".to_string());
            }
            if function == META_VARIANT_PAYLOAD_TYPE_OPT_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one VariantInfo argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if arg_ty != "VariantInfo" {
                    return Err(anyhow::anyhow!(
                        "{} expects VariantInfo argument, got {}",
                        function,
                        arg_ty
                    ));
                }
                return Ok("TypeOpt".to_string());
            }
            if function == META_SOURCE_SPAN_DISPLAY_INTRINSIC {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "{} expects exactly one SourceSpan argument, got {}",
                        function,
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if arg_ty != "SourceSpan" {
                    return Err(anyhow::anyhow!(
                        "{} expects SourceSpan argument, got {}",
                        function,
                        arg_ty
                    ));
                }
                return Ok("String".to_string());
            }
            if function == EMIT_DECLSET_NEW_INTRINSIC {
                if !arguments.is_empty() {
                    return Err(anyhow::anyhow!(
                        "{} expects zero arguments, got {}",
                        function,
                        arguments.len()
                    ));
                }
                return Ok("DeclSet".to_string());
            }
            if function == EMIT_ADD_EMPTY_ENUM_INTRINSIC {
                if arguments.len() != 2 {
                    return Err(anyhow::anyhow!(
                        "{} expects (DeclSet, String), got {} arguments",
                        function,
                        arguments.len()
                    ));
                }
                let a = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let b = get_expression_type(
                    &arguments[1],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if a != "DeclSet" || b != "String" {
                    return Err(anyhow::anyhow!(
                        "{} expects (DeclSet, String), got ({}, {})",
                        function,
                        a,
                        b
                    ));
                }
                return Ok("DeclSet".to_string());
            }
            if function == EMIT_ADD_ENUM_TAG_VARIANT_INTRINSIC {
                if arguments.len() != 3 {
                    return Err(anyhow::anyhow!(
                        "{} expects (DeclSet, String, String), got {} arguments",
                        function,
                        arguments.len()
                    ));
                }
                let a = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let b = get_expression_type(
                    &arguments[1],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let c = get_expression_type(
                    &arguments[2],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if a != "DeclSet" || b != "String" || c != "String" {
                    return Err(anyhow::anyhow!(
                        "{} expects (DeclSet, String, String), got ({}, {}, {})",
                        function,
                        a,
                        b,
                        c
                    ));
                }
                return Ok("DeclSet".to_string());
            }
            if function == EMIT_ADD_ENUM_PAYLOAD_VARIANT_INTRINSIC {
                if arguments.len() != 4 {
                    return Err(anyhow::anyhow!(
                        "{} expects (DeclSet, String, String, Type), got {} arguments",
                        function,
                        arguments.len()
                    ));
                }
                let a = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let b = get_expression_type(
                    &arguments[1],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let c = get_expression_type(
                    &arguments[2],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let d = get_expression_type(
                    &arguments[3],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if a != "DeclSet" || b != "String" || c != "String" || d != "Type" {
                    return Err(anyhow::anyhow!(
                        "{} expects (DeclSet, String, String, Type), got ({}, {}, {}, {})",
                        function,
                        a,
                        b,
                        c,
                        d
                    ));
                }
                return Ok("DeclSet".to_string());
            }
            if function == EMIT_ADD_DERIVED_STRUCT_INTRINSIC {
                if arguments.len() != 3 {
                    return Err(anyhow::anyhow!(
                        "{} expects (DeclSet, StructInfo, String), got {} arguments",
                        function,
                        arguments.len()
                    ));
                }
                let a = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let b = get_expression_type(
                    &arguments[1],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let c = get_expression_type(
                    &arguments[2],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if a != "DeclSet" || b != "StructInfo" || c != "String" {
                    return Err(anyhow::anyhow!(
                        "{} expects (DeclSet, StructInfo, String), got ({}, {}, {})",
                        function,
                        a,
                        b,
                        c
                    ));
                }
                return Ok("DeclSet".to_string());
            }
            if function == EMIT_ADD_INVARIANT_FIELD_GT_I32_INTRINSIC {
                if arguments.len() != 5 {
                    return Err(anyhow::anyhow!(
                        "{} expects (DeclSet, Type, String, String, I32), got {} arguments",
                        function,
                        arguments.len()
                    ));
                }
                let a = get_expression_type(
                    &arguments[0],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let b = get_expression_type(
                    &arguments[1],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let c = get_expression_type(
                    &arguments[2],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let d = get_expression_type(
                    &arguments[3],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let e = get_expression_type(
                    &arguments[4],
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                if a != "DeclSet" || b != "Type" || c != "String" || d != "String" || e != "I32" {
                    return Err(anyhow::anyhow!(
                        "{} expects (DeclSet, Type, String, String, I32), got ({}, {}, {}, {}, {})",
                        function,
                        a,
                        b,
                        c,
                        d,
                        e
                    ));
                }
                return Ok("DeclSet".to_string());
            }
            let func = fns
                .get(function)
                .ok_or_else(|| anyhow::anyhow!("unknown function {}", function))?;
            if func.parameters.len() != arguments.len() {
                return Err(anyhow::anyhow!(
                    "expected {} arguments, but got {}",
                    func.parameters.len(),
                    arguments.len()
                ));
            }
            for (param, arg) in func.parameters.iter().zip(arguments) {
                let param_type = &param.ty;
                let arg_type = get_expression_type(
                    arg,
                    var_types,
                    fns,
                    type_definitions,
                    trait_method_signatures,
                    trait_impl_methods,
                )?;
                let compatible =
                    normalize_numeric_alias(param_type) == normalize_numeric_alias(&arg_type);
                if !compatible {
                    return Err(anyhow::anyhow!(
                        "mismatched types: expected {:?}, but got {:?}",
                        param_type,
                        arg_type
                    ));
                }
            }
            Ok(func.return_type.clone())
        }
        Expression::UnaryOp(op, expr) => {
            let expr_type = get_expression_type(
                expr,
                var_types,
                fns,
                type_definitions,
                trait_method_signatures,
                trait_impl_methods,
            )?;
            match op {
                UnaryOp::Not => {
                    if expr_type == "Bool" {
                        Ok("Bool".to_string())
                    } else {
                        Err(anyhow::anyhow!(
                            "expected Bool operand for unary {:?}, got {:?}",
                            op,
                            expr_type
                        ))
                    }
                }
            }
        }
        Expression::BinOp(op, left, right) => {
            match resolve_binary_operator(
                *op,
                left,
                right,
                var_types,
                fns,
                type_definitions,
                trait_method_signatures,
                trait_impl_methods,
            )? {
                BinaryOperatorResolution::Builtin { return_type }
                | BinaryOperatorResolution::TraitCall { return_type, .. } => Ok(return_type),
                BinaryOperatorResolution::ComparisonTraitCall { .. } => Ok("Bool".to_string()),
            }
        }
    }
}

fn format_unsupported_call_target_message(callee: &Expression) -> String {
    match callee {
        Expression::FieldAccess {
            struct_variable,
            field,
        } => format!(
            "unsupported call target {}.{}(...): expected a namespaced function call, enum variant constructor call, or trait static call",
            struct_variable, field
        ),
        Expression::Variable(name) => format!(
            "unsupported call target {}(...): expected a declared function call",
            name
        ),
        Expression::MethodCall { .. } => {
            "unsupported method call target: expected method calls to be normalized".to_string()
        }
        _ => format!(
            "unsupported call target expression of kind {}: expected a function-style call target",
            expression_kind(callee)
        ),
    }
}

fn expression_kind(expr: &Expression) -> &'static str {
    match expr {
        Expression::Variable(_) => "variable",
        Expression::Literal(_) => "literal",
        Expression::Call(_, _) => "call",
        Expression::MethodCall { .. } => "method-call",
        Expression::PostfixCall { .. } => "postfix-call",
        Expression::BinOp(_, _, _) => "binary-op",
        Expression::UnaryOp(_, _) => "unary-op",
        Expression::FieldAccess { .. } => "field-access",
        Expression::StructValue { .. } => "struct-literal",
        Expression::Match { .. } => "match-expression",
    }
}

#[cfg(test)]
mod tests {
    use super::{resolve, TypeDef};
    use crate::builtins::BuiltInType;
    use crate::parser::UnaryOp;
    use crate::{parser, tokenizer};

    #[test]
    fn resolve_loads_split_stdlib_files() {
        let source = r#"
fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");

        assert!(
            resolved.type_definitions.contains_key("ParseErr"),
            "missing ParseErr type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("AsciiChar"),
            "missing AsciiChar type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("Char"),
            "missing Char type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("Null"),
            "missing Null type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("Bytes"),
            "missing Bytes type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("String"),
            "missing String type from split stdlib"
        );
        assert!(
            matches!(
                resolved.type_definitions.get("String"),
                Some(TypeDef::Enum(_))
            ),
            "String should be a std-defined enum"
        );
        assert!(
            resolved.type_definitions.contains_key("PtrInt"),
            "missing PtrInt type alias from standard definitions"
        );
        assert!(
            resolved.type_definitions.contains_key("U8"),
            "missing U8 type from standard definitions"
        );
        assert!(
            resolved.type_definitions.contains_key("Void"),
            "missing Void type from standard definitions"
        );
        assert!(
            resolved
                .function_sigs
                .contains_key("Json__parse_json_document"),
            "missing Json__parse_json_document function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("AsciiChar__from_code"),
            "missing AsciiChar__from_code function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("Char__from_code"),
            "missing Char__from_code function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("Null__value"),
            "missing Null__value function from split stdlib"
        );
        assert!(
            resolved
                .comptime_function_definitions
                .contains_key("derive_enum_tags"),
            "missing derive_enum_tags comptime helper from split stdlib"
        );
        assert!(
            resolved.trait_method_signatures.contains_key("Hash::hash"),
            "missing Hash::hash trait method from split stdlib"
        );
        assert!(
            resolved
                .trait_method_signatures
                .contains_key("Equality::equals"),
            "missing Equality::equals trait method from split stdlib"
        );
        assert!(
            resolved
                .trait_method_signatures
                .contains_key("Addition::add"),
            "missing Addition::add trait method from split stdlib"
        );
        assert!(
            resolved
                .trait_method_signatures
                .contains_key("Comparison::compare"),
            "missing Comparison::compare trait method from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("Hash__I32__hash"),
            "missing synthesized Hash__I32__hash impl function from split stdlib"
        );
        assert!(
            resolved
                .function_sigs
                .contains_key("Equality__Char__equals"),
            "missing synthesized Equality__Char__equals impl function from split stdlib"
        );
        assert!(
            resolved
                .function_sigs
                .contains_key("Comparison__Char__compare"),
            "missing synthesized Comparison__Char__compare impl function from split stdlib"
        );
        assert!(
            resolved
                .function_sigs
                .contains_key("String__from_literal_parts"),
            "missing String__from_literal_parts function from split stdlib"
        );
        assert!(
            resolved
                .function_sigs
                .contains_key("String__from_heap_parts"),
            "missing String__from_heap_parts function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("String__equals"),
            "missing String__equals function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("String__starts_with"),
            "missing String__starts_with function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("String__ends_with"),
            "missing String__ends_with function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("String__slice_clamped"),
            "missing String__slice_clamped function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("string_len"),
            "missing string_len top-level function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("slice"),
            "missing slice top-level function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("print_str"),
            "missing print_str top-level function from split stdlib"
        );
        assert!(
            resolved
                .ast
                .generic_definitions
                .iter()
                .any(|def| def.name == "Option"),
            "missing Option generic from split stdlib"
        );
        assert!(
            resolved
                .ast
                .generic_definitions
                .iter()
                .any(|def| def.name == "Result"),
            "missing Result generic from split stdlib"
        );
        assert!(
            resolved
                .ast
                .generic_definitions
                .iter()
                .any(|def| def.name == "HashSet"),
            "missing HashSet generic from split stdlib"
        );
        assert!(
            resolved
                .ast
                .generic_definitions
                .iter()
                .any(|def| def.name == "Vec"),
            "missing Vec generic from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("IoError"),
            "missing IoError type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("IoReadResult"),
            "missing IoReadResult type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("IoWriteResult"),
            "missing IoWriteResult type from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("Io__read_all"),
            "missing Io__read_all function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("Io__write_all"),
            "missing Io__write_all function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("Io__read_file"),
            "missing Io__read_file function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("Io__write_file"),
            "missing Io__write_file function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("Clib__malloc"),
            "missing Clib__malloc extern function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("Clib__free"),
            "missing Clib__free extern function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("Clib__memcmp"),
            "missing Clib__memcmp extern function from split stdlib"
        );
        assert_eq!(
            resolved
                .function_sigs
                .get("Clib__free")
                .and_then(|sig| sig.extern_symbol_name.as_deref()),
            Some("free"),
            "missing extern link symbol metadata for Clib__free"
        );
        assert_eq!(
            resolved
                .function_sigs
                .get("Clib__memcmp")
                .and_then(|sig| sig.extern_symbol_name.as_deref()),
            Some("memcmp"),
            "missing extern link symbol metadata for Clib__memcmp"
        );
        assert!(
            resolved.function_sigs.contains_key("load_u8"),
            "missing load_u8 builtin signature"
        );
        assert!(
            resolved.function_sigs.contains_key("load_i32"),
            "missing load_i32 builtin signature"
        );
        assert!(
            resolved.function_sigs.contains_key("load_i64"),
            "missing load_i64 builtin signature"
        );
        assert!(
            resolved.function_sigs.contains_key("load_bool"),
            "missing load_bool builtin signature"
        );
        assert!(
            resolved.function_sigs.contains_key("store_u8"),
            "missing store_u8 builtin signature"
        );
        assert!(
            resolved.function_sigs.contains_key("store_i32"),
            "missing store_i32 builtin signature"
        );
        assert!(
            resolved.function_sigs.contains_key("store_i64"),
            "missing store_i64 builtin signature"
        );
        assert!(
            resolved.function_sigs.contains_key("store_bool"),
            "missing store_bool builtin signature"
        );
        assert!(
            resolved.type_definitions.contains_key("U8Ref"),
            "missing U8Ref type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("I32Ref"),
            "missing I32Ref type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("I64Ref"),
            "missing I64Ref type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("PtrIntRef"),
            "missing PtrIntRef type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("BoolRef"),
            "missing BoolRef type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("U8Mut"),
            "missing U8Mut type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("I32Mut"),
            "missing I32Mut type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("I64Mut"),
            "missing I64Mut type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("PtrIntMut"),
            "missing PtrIntMut type from split stdlib"
        );
        assert!(
            resolved.type_definitions.contains_key("BoolMut"),
            "missing BoolMut type from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("U8Ref__read"),
            "missing U8Ref__read function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("I32Ref__read"),
            "missing I32Ref__read function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("I64Ref__read"),
            "missing I64Ref__read function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("PtrIntRef__read"),
            "missing PtrIntRef__read function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("BoolRef__read"),
            "missing BoolRef__read function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("U8Mut__write"),
            "missing U8Mut__write function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("I32Mut__write"),
            "missing I32Mut__write function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("I64Mut__write"),
            "missing I64Mut__write function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("PtrIntMut__write"),
            "missing PtrIntMut__write function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("BoolMut__write"),
            "missing BoolMut__write function from split stdlib"
        );
        assert!(
            resolved.struct_invariants.contains_key("AsciiChar"),
            "missing AsciiChar invariant metadata from split stdlib"
        );
        assert!(
            resolved
                .function_definitions
                .contains_key("__struct__AsciiChar__invariant__code_in_ascii_range"),
            "missing __struct__AsciiChar__invariant__code_in_ascii_range function from split stdlib"
        );
        assert!(
            resolved.struct_invariants.contains_key("Bytes"),
            "missing Bytes invariant metadata from split stdlib"
        );
        assert!(
            resolved
                .function_definitions
                .contains_key("__struct__Bytes__invariant__non_negative_length"),
            "missing __struct__Bytes__invariant__non_negative_length function from split stdlib"
        );
    }

    #[test]
    fn resolve_accepts_main_with_argc_argv_signature() {
        let source = r#"
fun main(argc: I32, argv: I64) -> I32 {
	return argc
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        resolve(ast).expect("resolve source");
    }

    #[test]
    fn resolve_accepts_extern_void_function_and_statement_call() {
        let source = r#"
fun main() -> I32 {
	Clib.free(i32_to_i64(0))
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        resolve(ast).expect("resolve source");
    }

    #[test]
    fn resolve_rejects_void_parameter_type() {
        let source = r#"
extern fun bad(v: Void) -> I32

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("Void parameter type should fail");
        assert!(err
            .to_string()
            .contains("cannot use Void as parameter type"));
    }

    #[test]
    fn resolve_accepts_non_extern_void_return() {
        let source = r#"
fun helper() -> Void {
	Clib.free(i32_to_i64(0))
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        resolve(ast).expect("non-extern Void return should be accepted");
    }

    #[test]
    fn resolve_rejects_invalid_copy_trait_shape() {
        let source = r#"
trait Copy {
	fun clone(v: Self) -> Self
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("invalid Copy trait shape should fail");
        assert!(err
            .to_string()
            .contains("trait Copy must define copy(v: Ref[Self]) -> Self"));
    }

    #[test]
    fn resolve_rejects_invalid_drop_trait_shape() {
        let source = r#"
trait Drop {
	fun drop(v: Self) -> Self
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("invalid Drop trait shape should fail");
        assert!(err
            .to_string()
            .contains("trait Drop must define drop(v: Self) -> Void"));
    }

    #[test]
    fn resolve_copy_type_can_be_read_multiple_times() {
        let source = r#"
fun main() -> I32 {
	a = 7
	b = a
	c = a
	return b + c
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        resolve(ast).expect("Copy-backed scalar reads should compile");
    }

    #[test]
    fn resolve_rejects_use_after_move() {
        let source = r#"
struct Box {
	value: I32,
}

fun consume(v: Box) -> I32 {
	return v.value
}

fun main() -> I32 {
	a = Box struct { value: 1 }
	x = consume(a)
	y = consume(a)
	return x + y
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("use-after-move should fail");
        assert!(err.to_string().contains("use of moved value a"));
    }

    #[test]
    fn resolve_rejects_move_from_uninitialized_binding() {
        let source = r#"
struct Box {
	value: I32,
}

fun consume(v: Box) -> I32 {
	return v.value
}

fun main() -> I32 {
	if 1 == 1 {
		a = Box struct { value: 1 }
	}
	return consume(a)
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("uninitialized move should fail");
        assert!(err
            .to_string()
            .contains("cannot move from uninitialized value a"));
    }

    #[test]
    fn resolve_rejects_extern_struct_parameter_type() {
        let source = r#"
struct Packet {
	value: I32,
}

extern fun read_packet(packet: Packet) -> I32

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("extern struct parameter should fail");
        assert!(err.to_string().contains(
            "cannot use struct parameter type Packet (packet) in v2 ABI; use PtrInt wrappers for C interop"
        ));
    }

    #[test]
    fn resolve_rejects_extern_struct_return_type() {
        let source = r#"
struct Packet {
	value: I32,
}

extern fun read_packet() -> Packet

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("extern struct return should fail");
        assert!(err.to_string().contains(
            "cannot return struct type Packet in v2 ABI; use PtrInt wrappers for C interop"
        ));
    }

    #[test]
    fn resolve_rejects_main_with_unsupported_parameters() {
        let source = r#"
fun main(argc: I64, argv: I64) -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("resolve should fail");
        assert!(err.to_string().contains("unsupported main signature"));
    }

    #[test]
    fn resolve_accepts_ptr_int_alias_for_i64_positions() {
        let source = r#"
fun take_i64(v: I64) -> I64 {
	return v
}

fun take_ptr(v: PtrInt) -> PtrInt {
	return v
}

fun main(argc: I32, argv: PtrInt) -> I32 {
	v = take_i64(argv)
	w = take_ptr(v)
	if w == argv {
		return argc
	}
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");

        assert!(matches!(
            resolved.type_definitions.get("PtrInt"),
            Some(TypeDef::BuiltIn(BuiltInType::I64))
        ));
    }

    #[test]
    fn resolve_rejects_main_with_non_i32_return_type() {
        let source = r#"
fun main() -> I64 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("resolve should fail");
        let message = err.to_string();
        assert!(
            message.contains("return type must be I32")
                || message.contains("function main return type mismatch"),
            "unexpected error: {message}"
        );
    }

    #[test]
    fn resolve_synthesizes_struct_invariant_function_from_declaration() {
        let source = r#"
struct Counter {
	value: I32,
}

invariant positive_value "counter value must be non-negative" for (v: Counter) {
	return v.value >= 0
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");

        let invariant = resolved
            .struct_invariants
            .get("Counter")
            .expect("missing Counter invariant metadata");
        assert_eq!(invariant.len(), 1);
        assert_eq!(
            invariant[0].function_name,
            "__struct__Counter__invariant__positive_value"
        );
        assert_eq!(invariant[0].key, "positive_value");
        assert_eq!(
            invariant[0].display_name,
            "counter value must be non-negative"
        );
        assert_eq!(invariant[0].identifier.as_deref(), Some("positive_value"));

        let function = resolved
            .function_definitions
            .get("__struct__Counter__invariant__positive_value")
            .expect("missing synthesized invariant function");
        assert_eq!(function.sig.parameters.len(), 1);
        assert_eq!(function.sig.parameters[0].ty, "Counter");
        assert_eq!(function.sig.return_type, "Bool");
    }

    #[test]
    fn resolve_expands_generic_invariant_to_concrete_struct() {
        let source = r#"
generic Box[T] {
	struct Box {
		value: T,
	}

	invariant "value must be non-negative" for (v: Box) {
		return v.value >= 0
	}
}

specialize BoxI32 = Box[I32]

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");

        let invariant = resolved
            .struct_invariants
            .get("BoxI32")
            .expect("missing BoxI32 invariant metadata");
        assert_eq!(invariant.len(), 1);
        assert_eq!(
            invariant[0].function_name,
            "__struct__BoxI32__invariant__anon_0"
        );
        assert_eq!(invariant[0].key, "anon_0");
        assert_eq!(invariant[0].display_name, "value must be non-negative");
        assert_eq!(invariant[0].identifier, None);

        let function = resolved
            .function_definitions
            .get("__struct__BoxI32__invariant__anon_0")
            .expect("missing synthesized BoxI32 invariant function");
        assert_eq!(function.sig.parameters.len(), 1);
        assert_eq!(function.sig.parameters[0].ty, "BoxI32");
        assert_eq!(function.sig.return_type, "Bool");
    }

    #[test]
    fn resolve_allows_multiple_invariants_for_same_struct() {
        let source = r#"
struct Counter {
	value: I32,
	max: I32,
}

invariant for (v: Counter) {
	non_negative_value "counter value must be non-negative" {
		return v.value >= 0
	}
	"counter max must be non-negative" {
		return v.max >= 0
	}
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");

        let invariants = resolved
            .struct_invariants
            .get("Counter")
            .expect("missing Counter invariant metadata");
        assert_eq!(invariants.len(), 2);
        assert_eq!(
            invariants[0].function_name,
            "__struct__Counter__invariant__non_negative_value"
        );
        assert_eq!(invariants[0].key, "non_negative_value");
        assert_eq!(
            invariants[1].function_name,
            "__struct__Counter__invariant__anon_0"
        );
        assert_eq!(invariants[1].key, "anon_0");
    }

    #[test]
    fn resolve_synthesizes_function_precondition_helpers_and_metadata() {
        let source = r#"
fun guarded(x: I32) -> I32 pre {
	x > 5
	x < 20
} {
	return x
}

fun main() -> I32 {
	return guarded(7)
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");

        let metadata = resolved
            .function_preconditions
            .get("guarded")
            .expect("missing function precondition metadata");
        assert_eq!(metadata.len(), 2);
        assert_eq!(metadata[0].owner_function_name, "guarded");
        assert_eq!(metadata[0].helper_function_name, "__pre__guarded__clause_0");
        assert_eq!(metadata[0].clause_ordinal, 0);
        assert_eq!(metadata[1].helper_function_name, "__pre__guarded__clause_1");
        assert_eq!(metadata[1].clause_ordinal, 1);

        let helper = resolved
            .function_definitions
            .get("__pre__guarded__clause_0")
            .expect("missing synthesized precondition helper");
        assert_eq!(helper.sig.parameters.len(), 1);
        assert_eq!(helper.sig.parameters[0].ty, "I32");
        assert_eq!(helper.sig.return_type, "Bool");
    }

    #[test]
    fn resolve_rewrites_generic_function_preconditions_to_specialized_types() {
        let source = r#"
generic Box[T] {
	struct Box {
		value: T,
	}

	fun unwrap(v: Box) -> T pre {
		v.value == v.value
	} {
		return v.value
	}
}

specialize BoxI32 = Box[I32]

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");

        let metadata = resolved
            .function_preconditions
            .get("BoxI32__unwrap")
            .expect("missing specialized function precondition metadata");
        assert_eq!(metadata.len(), 1);
        assert_eq!(
            metadata[0].helper_function_name,
            "__pre__BoxI32__unwrap__clause_0"
        );

        let helper = resolved
            .function_definitions
            .get("__pre__BoxI32__unwrap__clause_0")
            .expect("missing specialized precondition helper");
        assert_eq!(helper.sig.parameters.len(), 1);
        assert_eq!(helper.sig.parameters[0].ty, "BoxI32");
        assert_eq!(helper.sig.return_type, "Bool");
    }

    #[test]
    fn resolve_rejects_duplicate_invariant_identifier_for_same_struct() {
        let source = r#"
struct Counter {
	value: I32,
}

invariant first "counter value must be non-negative" for (v: Counter) {
	return v.value >= 0
}

invariant first "counter value must stay non-negative" for (v: Counter) {
	return v.value >= 0
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("duplicate identifier should fail");
        assert!(err
            .to_string()
            .contains("duplicate invariant identifier `first`"));
    }

    #[test]
    fn resolve_synthesizes_model_invariant_function_from_multi_parameter_declaration() {
        let source = r#"
struct Counter {
	value: I32,
}

invariant "counter ordering is reflexive" for (lhs: Counter, rhs: Counter) {
	return lhs.value <= rhs.value
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");

        assert!(
            !resolved.struct_invariants.contains_key("Counter"),
            "multi-parameter invariants should not register as struct invariants"
        );
        let model = resolved
            .model_invariants
            .iter()
            .find(|model| model.display_name == "counter ordering is reflexive")
            .expect("missing synthesized model invariant metadata");
        assert!(model.function_name.starts_with("__model__invariant__"));
        let function = resolved
            .function_definitions
            .get(&model.function_name)
            .expect("missing synthesized model invariant function");
        assert_eq!(function.sig.parameters.len(), 2);
        assert_eq!(function.sig.parameters[0].ty, "Counter");
        assert_eq!(function.sig.parameters[1].ty, "Counter");
        assert_eq!(function.sig.return_type, "Bool");
    }

    #[test]
    fn resolve_rejects_duplicate_model_invariant_identifier() {
        let source = r#"
invariant stable_pair "stable pair" for (lhs: I32, rhs: I32) {
	return lhs <= rhs
}

invariant stable_pair "stable pair duplicate" for (lhs: I32, rhs: I32) {
	return lhs <= rhs
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("duplicate model invariant identifier should fail");
        assert!(err
            .to_string()
            .contains("model invariants have duplicate identifier `stable_pair`"));
    }

    #[test]
    fn resolve_rewrites_all_generic_model_invariant_parameter_types() {
        let source = r#"
generic Box[T] {
	struct Box {
		value: T,
	}

	invariant "specialized boxes compare by value" for (lhs: Box, rhs: Box) {
		return lhs.value == rhs.value
	}
}

specialize BoxI32 = Box[I32]

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");
        let model = resolved
            .model_invariants
            .iter()
            .find(|model| model.display_name == "specialized boxes compare by value")
            .expect("missing synthesized model invariant metadata");
        let function = resolved
            .function_definitions
            .get(&model.function_name)
            .expect("missing synthesized model invariant function");
        assert_eq!(function.sig.parameters.len(), 2);
        assert_eq!(function.sig.parameters[0].ty, "BoxI32");
        assert_eq!(function.sig.parameters[1].ty, "BoxI32");
    }

    #[test]
    fn resolve_rejects_unary_invariant_targeting_non_struct_type() {
        let source = r#"
invariant "i32 invariant is invalid" for (v: I32) {
	return v >= 0
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("unary invariant over non-struct should fail");
        assert!(err.to_string().contains("must target a struct type"));
    }

    #[test]
    fn resolve_rejects_model_invariant_with_side_effect_builtin_call() {
        let source = r#"
invariant "printing is disallowed" for (v: I32, w: I32) {
	printed = print(v)
	return printed == printed
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("side-effect calls in model invariants should fail");
        assert!(err.to_string().contains("calls side-effect builtin print"));
    }

    #[test]
    fn resolve_rejects_model_invariant_with_print_str_call() {
        let source = r#"
invariant "print_str is disallowed" for (v: I32, w: I32) {
	print_str("hello")
	return v == w
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("print_str in model invariants should fail");
        assert!(err
            .to_string()
            .contains("calls extern function Clib__write"));
    }

    #[test]
    fn resolve_rejects_model_invariant_with_prove_statement() {
        let source = r#"
invariant "prove is disallowed" for (v: I32, w: I32) {
	prove(v <= w)
	return true
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("prove statements in model invariants should fail");
        assert!(err.to_string().contains("contains prove(...) statement"));
    }

    #[test]
    fn resolve_rejects_model_invariant_with_assert_statement() {
        let source = r#"
invariant "assert is disallowed" for (v: I32, w: I32) {
	assert(v <= w)
	return true
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("assert statements in model invariants should fail");
        assert!(err.to_string().contains("contains assert(...) statement"));
    }

    #[test]
    fn resolve_rejects_model_invariant_with_direct_extern_call() {
        let source = r#"
invariant "extern calls are disallowed" for (fd: I32, value: I32) {
	code = Clib.close(fd)
	return code == 0 || code == (0 - 1)
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("extern calls in model invariants should fail");
        assert!(err
            .to_string()
            .contains("calls extern function Clib__close"));
    }

    #[test]
    fn resolve_rejects_model_invariant_with_pointer_memory_builtin_call() {
        let source = r#"
invariant "pointer loads are disallowed" for (addr: PtrInt, value: I32) {
	loaded = load_i32(addr)
	return loaded == value
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("pointer memory builtins should fail");
        assert!(err
            .to_string()
            .contains("calls side-effect builtin load_i32"));
    }

    #[test]
    fn resolve_rejects_model_invariant_with_transitive_extern_call() {
        let source = r#"
fun helper(fd: I32) -> Bool {
	code = Clib.close(fd)
	return code == 0 || code == (0 - 1)
}

invariant "transitive extern calls are disallowed" for (fd: I32, value: I32) {
	return helper(fd)
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err =
            resolve(ast).expect_err("transitive extern calls in model invariants should fail");
        assert!(err
            .to_string()
            .contains("calls extern function Clib__close"));
    }

    #[test]
    fn resolve_rejects_non_bool_prove_condition() {
        let source = r#"
fun main() -> I32 {
	prove(1)
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("resolve should fail");
        assert!(err.to_string().contains("prove expects Bool condition"));
    }

    #[test]
    fn resolve_rejects_assert_as_expression() {
        let source = r#"
fun main() -> I32 {
	x = assert(true)
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("resolve should fail");
        assert!(err
            .to_string()
            .contains("assert(...) is statement-only and cannot be used as an expression"));
    }

    #[test]
    fn resolve_rejects_reserved_builtin_function_name() {
        let source = r#"
fun prove(a: Bool) -> Bool {
	return a
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("resolve should fail");
        assert!(err.to_string().contains("function name prove is reserved"));
    }

    #[test]
    fn resolve_tracks_comptime_registry_and_apply_order() {
        let source = r#"
struct Counter {
	value: I32,
}

comptime fun build_counter(T: Type) -> DeclSet {
	return DeclSet.new()
}

comptime apply build_counter(Counter)

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");

        assert!(resolved
            .comptime_function_definitions
            .contains_key("build_counter"));
        assert_eq!(resolved.comptime_apply_order.len(), 1);
        assert_eq!(
            resolved.comptime_apply_order[0].function_name,
            "build_counter"
        );
    }

    #[test]
    fn resolve_accepts_namespaced_function_calls() {
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

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");
        assert!(resolved.function_sigs.contains_key("Option__is_some"));
        assert!(resolved
            .function_definitions
            .contains_key("Option__is_some"));
        let main = resolved
            .function_definitions
            .get("main")
            .expect("missing main definition");
        let parser::Statement::Return { expr } = &main.body[1] else {
            panic!("expected normalized return expression");
        };
        let parser::Expression::Call(function_name, args) = expr else {
            panic!("expected normalized direct call");
        };
        assert_eq!(function_name, "Option__is_some");
        assert_eq!(args.len(), 1);
        assert!(matches!(args[0], parser::Expression::Variable(_)));
    }

    #[test]
    fn resolve_accepts_method_calls_on_value_and_temporary_receivers() {
        let source = r#"
struct Option {
	value: I32,
}

namespace Option {
	fun is_some(v: Option) -> I32 {
		return v.value
	}
}

fun make_option() -> Option {
	return Option struct { value: 11 }
}

fun main() -> I32 {
	v = Option struct { value: 7 }
	x = v.is_some()
	return make_option().is_some()
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");
        let main = resolved
            .function_definitions
            .get("main")
            .expect("missing main definition");

        let parser::Statement::Assign { value, .. } = &main.body[1] else {
            panic!("expected normalized assignment");
        };
        let parser::Expression::Call(function_name, args) = value else {
            panic!("expected normalized method call");
        };
        assert_eq!(function_name, "Option__is_some");
        assert_eq!(args.len(), 1);
        assert!(matches!(args[0], parser::Expression::Variable(_)));

        let parser::Statement::Return { expr } = &main.body[2] else {
            panic!("expected return statement");
        };
        let parser::Expression::Call(function_name, args) = expr else {
            panic!("expected normalized method call on temporary receiver");
        };
        assert_eq!(function_name, "Option__is_some");
        assert_eq!(args.len(), 1);
        assert!(matches!(args[0], parser::Expression::Call(_, _)));
    }

    #[test]
    fn resolve_reports_user_facing_message_for_missing_method() {
        let source = r#"
struct Option {
	value: I32,
}

fun main() -> I32 {
	v = Option struct { value: 7 }
	return v.missing()
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("resolve should fail");
        let message = err.to_string();
        assert!(
            message.contains("method Option.missing not found for receiver type Option"),
            "unexpected error: {message}"
        );
    }

    #[test]
    fn resolve_does_not_treat_receiver_method_sugar_as_trait_dispatch() {
        let source = r#"
trait MyReceiverHash {
	fun hash(v: Self) -> I32
}

impl MyReceiverHash for I32 {
	fun hash(v: I32) -> I32 {
		return v
	}
}

fun main() -> I32 {
	v = 7
	return v.hash()
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err =
            resolve(ast).expect_err("receiver method sugar should not dispatch through traits");
        let message = err.to_string();
        assert!(
            message.contains("method I32.hash not found for receiver type I32"),
            "unexpected error: {message}"
        );
    }

    #[test]
    fn resolve_accepts_namespaced_calls_to_generic_specialized_helpers() {
        let source = r#"
generic Identity[T] {
	struct Identity {
		value: T,
	}

	fun value(v: T) -> T {
		return v
	}
}

specialize IntIdentity = Identity[I32]

fun main() -> I32 {
	return IntIdentity.value(7)
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");
        assert!(resolved.function_sigs.contains_key("IntIdentity__value"));
        assert!(resolved
            .function_definitions
            .contains_key("IntIdentity__value"));
        let main = resolved
            .function_definitions
            .get("main")
            .expect("missing main definition");
        let parser::Statement::Return { expr } = &main.body[0] else {
            panic!("expected normalized return");
        };
        let parser::Expression::Call(function_name, args) = expr else {
            panic!("expected normalized namespaced call");
        };
        assert_eq!(function_name, "IntIdentity__value");
        assert_eq!(args.len(), 1);
    }

    #[test]
    fn resolve_accepts_method_calls_on_generic_specialized_receivers() {
        let source = r#"
generic Wrapper[T] {
	struct Wrapper {
		value: T,
	}

	fun get(v: Wrapper) -> T {
		return v.value
	}
}

specialize IntWrapper = Wrapper[I32]

fun main() -> I32 {
	w = IntWrapper struct { value: 7 }
	return w.get()
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");
        let main = resolved
            .function_definitions
            .get("main")
            .expect("missing main definition");
        let parser::Statement::Return { expr } = &main.body[1] else {
            panic!("expected normalized return");
        };
        let parser::Expression::Call(function_name, args) = expr else {
            panic!("expected normalized method call on generic specialization");
        };
        assert_eq!(function_name, "IntWrapper__get");
        assert_eq!(args.len(), 1);
        assert!(matches!(args[0], parser::Expression::Variable(_)));
    }

    #[test]
    fn resolve_accepts_method_calls_on_std_string_helpers() {
        let source = r#"
impl Copy for String {
	fun copy(v: String) -> String {
		return v
	}
}

fun main() -> I32 {
	s = "alpha-beta"
	s.starts_with("alpha")
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");
        let main = resolved
            .function_definitions
            .get("main")
            .expect("missing main definition");
        let parser::Statement::Expression { expr } = &main.body[1] else {
            panic!("expected normalized expression statement");
        };
        let parser::Expression::Call(function_name, args) = expr else {
            panic!("expected normalized std string method call");
        };
        assert_eq!(function_name, "String__starts_with");
        assert_eq!(args.len(), 2);
        assert!(matches!(args[0], parser::Expression::Variable(_)));
    }

    #[test]
    fn resolve_normalizes_custom_addition_operator_to_call() {
        let source = r#"
struct Counter {
	value: I32,
}

impl Addition for Counter {
	fun add(lhs: Counter, rhs: Counter) -> Counter {
		return Counter struct { value: lhs.value + rhs.value }
	}
}

fun main() -> I32 {
	a = Counter struct { value: 7 }
	b = Counter struct { value: 2 }
	sum = a + b
	return sum.value
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");
        let main = resolved
            .function_definitions
            .get("main")
            .expect("missing main definition");
        let parser::Statement::Assign { value, .. } = &main.body[2] else {
            panic!("expected normalized assignment");
        };
        let parser::Expression::Call(function_name, args) = value else {
            panic!("expected custom operator to normalize to a direct call");
        };
        assert_eq!(function_name, "Addition__Counter__add");
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn resolve_keeps_struct_equality_fallback_as_builtin_binop() {
        let source = r#"
struct Pair {
	left: I32,
	right: I32,
}

fun main() -> I32 {
	a = Pair struct { left: 1, right: 2 }
	b = Pair struct { left: 1, right: 2 }
	same = a == b
	if same {
		return 1
	}
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");
        let main = resolved
            .function_definitions
            .get("main")
            .expect("missing main definition");
        let parser::Statement::Assign { value, .. } = &main.body[2] else {
            panic!("expected normalized assignment");
        };
        let parser::Expression::BinOp(parser::Op::Eq, _, _) = value else {
            panic!("expected struct equality fallback to stay as a builtin binop");
        };
    }

    #[test]
    fn resolve_prefers_explicit_equality_impl_over_struct_fallback() {
        let source = r#"
struct Pair {
	value: I32,
}

impl Copy for Pair {
	fun copy(v: Pair) -> Pair {
		return v
	}
}

impl Equality for Pair {
	fun equals(a: Pair, b: Pair) -> Bool {
		return a.value == b.value
	}
}

fun main() -> I32 {
	a = Pair struct { value: 7 }
	b = Pair struct { value: 7 }
	same = a == b
	diff = a != b
	if same && diff == false {
		return 1
	}
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");
        let main = resolved
            .function_definitions
            .get("main")
            .expect("missing main definition");
        let parser::Statement::Assign { value, .. } = &main.body[2] else {
            panic!("expected normalized equality assignment");
        };
        let parser::Expression::Call(function_name, args) = value else {
            panic!("expected explicit Equality impl to win over struct fallback");
        };
        assert_eq!(function_name, "Equality__Pair__equals");
        assert_eq!(args.len(), 2);

        let parser::Statement::Assign { value, .. } = &main.body[3] else {
            panic!("expected normalized inequality assignment");
        };
        let parser::Expression::UnaryOp(UnaryOp::Not, inner) = value else {
            panic!("expected != to normalize through unary not");
        };
        let parser::Expression::Call(function_name, args) = inner.as_ref() else {
            panic!("expected != to normalize through Equality impl call");
        };
        assert_eq!(function_name, "Equality__Pair__equals");
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn resolve_normalizes_custom_comparison_operator_to_compare_call() {
        let source = r#"
struct Rank {
	value: I32,
}

impl Copy for Rank {
	fun copy(v: Rank) -> Rank {
		return v
	}
}

impl Comparison for Rank {
	fun compare(a: Rank, b: Rank) -> I32 {
		if a.value < b.value {
			return 0 - 1
		}
		if a.value > b.value {
			return 1
		}
		return 0
	}
}

fun main() -> I32 {
	a = Rank struct { value: 1 }
	b = Rank struct { value: 2 }
	lt = a < b
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");
        let main = resolved
            .function_definitions
            .get("main")
            .expect("missing main definition");
        let parser::Statement::Assign { value, .. } = &main.body[2] else {
            panic!("expected normalized assignment");
        };
        let parser::Expression::BinOp(parser::Op::Lt, left, right) = value else {
            panic!("expected comparison operator to stay as compare-call < 0");
        };
        let parser::Expression::Call(function_name, args) = left.as_ref() else {
            panic!("expected comparison operator left side to be compare call");
        };
        assert_eq!(function_name, "Comparison__Rank__compare");
        assert_eq!(args.len(), 2);
        let parser::Expression::Literal(parser::Literal::Int(0)) = right.as_ref() else {
            panic!("expected comparison operator right side to be literal 0");
        };
    }

    #[test]
    fn resolve_expands_local_specialization_in_generic_body() {
        let source = r#"
generic Wrapper[T] {
	struct Wrapper {
		value: T,
	}

	specialize MaybeValue = Option[T]

	fun wrap(value: T) -> MaybeValue {
		return MaybeValue.Some(value)
	}

	fun unwrap_or(v: MaybeValue, fallback: T) -> T {
		return match v {
			MaybeValue.None => fallback
			MaybeValue.Some(value) => value
		}
	}
}

specialize I32Wrapper = Wrapper[I32]

fun main() -> I32 {
	maybe = I32Wrapper.wrap(7)
	return I32Wrapper.unwrap_or(maybe, 1)
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");

        assert!(resolved
            .type_definitions
            .contains_key("I32Wrapper__MaybeValue"));
        assert!(resolved.function_sigs.contains_key("I32Wrapper__wrap"));
        assert!(resolved
            .function_sigs
            .contains_key("I32Wrapper__MaybeValue__unwrap_or"));
    }

    #[test]
    fn resolve_rejects_missing_impl_for_generic_bound() {
        let source = r#"
generic Table[K: Hash + Equality] {
	struct Table {
		k: K,
	}
}

struct BadKey {
	x: I32,
}

specialize BadTable = Table[BadKey]

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("resolve should fail");
        assert!(err.to_string().contains("missing impl Hash for BadKey"));
    }

    #[test]
    fn resolve_rejects_duplicate_impl_for_trait_and_type() {
        let source = r#"
trait MyEq {
	fun equals(a: Self, b: Self) -> Bool
}

impl MyEq for I32 {
	fun equals(a: I32, b: I32) -> Bool {
		return a == b
	}
}

impl MyEq for I32 {
	fun equals(a: I32, b: I32) -> Bool {
		return a == b
	}
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("resolve should fail");
        assert!(err
            .to_string()
            .contains("duplicate impl for trait MyEq and type I32"));
    }

    #[test]
    fn resolve_rejects_reserved_builtin_operator_impl() {
        let source = r#"
impl Addition for I32 {
	fun add(lhs: I32, rhs: I32) -> I32 {
		return lhs + rhs
	}
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("builtin primitive operator impl should fail");
        assert!(err
            .to_string()
            .contains("impl Addition for I32 is reserved to compiler builtin operator semantics"));
    }

    #[test]
    fn resolve_rejects_impl_signature_mismatch() {
        let source = r#"
trait MyHash {
	fun hash(v: Self) -> I32
}

impl MyHash for I32 {
	fun hash(v: I32) -> Bool {
		return true
	}
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("resolve should fail");
        assert!(err
            .to_string()
            .contains("impl method MyHash.hash return type mismatch: expected I32, got Bool"));
    }

    #[test]
    fn resolve_accepts_trait_dispatch_in_generic_specialization() {
        let source = r#"
generic Wrapper[T: Hash] {
	struct Wrapper {
		value: T,
	}

	fun hash_of(v: T) -> I32 {
		return Hash.hash(v)
	}
}

specialize IntWrapper = Wrapper[I32]

fun main() -> I32 {
	return IntWrapper.hash_of(7)
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");

        assert!(resolved.function_sigs.contains_key("Hash__I32__hash"));
        assert!(resolved.function_sigs.contains_key("IntWrapper__hash_of"));
    }

    #[test]
    fn resolve_accepts_std_ascii_char_api_usage() {
        let source = r#"
fun main() -> I32 {
	match AsciiChar.from_string_at("A", 0) {
		AsciiCharResult.Ok(ch) => {
			if AsciiChar.equals(ch, ch) && AsciiChar.is_whitespace(ch) == false {
				return AsciiChar.code(ch)
			}
			return 0
		}
		AsciiCharResult.OutOfRange => {
			return 0
		}
	}
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        resolve(ast).expect("resolve source");
    }

    #[test]
    fn resolve_accepts_std_null_api_usage() {
        let source = r#"
fun takes_null(v: Null) -> I32 {
	if v == Null.value() {
		return 1
	}
	return 0
}

fun main() -> I32 {
	v = Null.value()
	return takes_null(v)
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        resolve(ast).expect("resolve source");
    }

    #[test]
    fn resolve_accepts_std_char_api_usage_and_char_literals() {
        let source = r#"
fun main() -> I32 {
	ch = 'x'
	if Char.equals(ch, Char.from_code(120)) {
		return Char.code(ch)
	}
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        resolve(ast).expect("resolve source");
    }

    #[test]
    fn resolve_accepts_fp32_arithmetic_and_comparison() {
        let source = r#"
fun main() -> I32 {
	a = 1.25
	b = 2.5
	c = a + b
	if c > b {
		return 1
	}
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        resolve(ast).expect("resolve source");
    }

    #[test]
    fn resolve_accepts_fp64_arithmetic_and_comparison() {
        let source = r#"
fun main() -> I32 {
	a = 1.25f64
	b = 2.5f64
	c = a + b
	if c > b {
		return 1
	}
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        resolve(ast).expect("resolve source");
    }

    #[test]
    fn resolve_accepts_u8_arithmetic_and_comparison() {
        let source = r#"
fun add_u8(a: U8, b: U8) -> U8 {
	c = a + b
	if c < b {
		return c
	}
	return c
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        resolve(ast).expect("resolve source");
    }

    #[test]
    fn resolve_accepts_pointer_load_and_store_builtins() {
        let source = r#"
fun main(argc: I32, argv: PtrInt) -> I32 {
	b = load_u8(argv)
	w = load_i32(argv)
	l = load_i64(argv)
	flag = load_bool(argv)
	store_u8(argv, b)
	store_i32(argv, w)
	store_i64(argv, l)
	store_bool(argv, flag)
	if flag {
		return w
	}
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        resolve(ast).expect("resolve source");
    }

    #[test]
    fn resolve_rejects_mixed_u8_and_i32_arithmetic() {
        let source = r#"
fun bad(a: U8, b: I32) -> U8 {
	c = a + b
	return c
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("mixed U8/I32 arithmetic should fail");
        assert!(err
            .to_string()
            .contains("expected both operands of Add to have the same type"));
    }

    #[test]
    fn resolve_rejects_tagged_enum_equality_without_impl() {
        let source = r#"
enum Token {
	End,
	Int: I32,
}

fun main() -> I32 {
	a = Token.Int(1)
	b = Token.Int(1)
	if a == b {
		return 1
	}
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("tagged enum equality should require an impl");
        assert!(err.to_string().contains(
            "direct Eq comparison is not supported for tagged enum Token without an Equality impl"
        ));
    }

    #[test]
    fn resolve_accepts_tagged_enum_equality_with_impl() {
        let source = r#"
enum Token {
	End,
	Int: I32,
}

impl Equality for Token {
	fun equals(a: Token, b: Token) -> Bool {
		return match a {
			Token.End => match b {
				Token.End => true
				Token.Int(_) => false
			}
			Token.Int(av) => match b {
				Token.End => false
				Token.Int(bv) => av == bv
			}
		}
	}
}

fun main() -> I32 {
	a = Token.Int(1)
	b = Token.Int(1)
	same = a == b
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = resolve(ast).expect("resolve source");
        let main = resolved
            .function_definitions
            .get("main")
            .expect("missing main definition");
        let parser::Statement::Assign { value, .. } = &main.body[2] else {
            panic!("expected normalized assignment");
        };
        let parser::Expression::Call(function_name, args) = value else {
            panic!("expected tagged enum equality to normalize to explicit impl call");
        };
        assert_eq!(function_name, "Equality__Token__equals");
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn resolve_accepts_enum_semantic_introspection_in_comptime() {
        let source = r#"
struct Payload {
	value: I32,
}

enum Token {
	Int: I32,
	Plus,
	Wrapped: Payload,
}

comptime fun reflect(T: Type) -> DeclSet {
	enum_opt = T.as_enum_opt()
	if enum_opt.is_some() {
		info = enum_opt.unwrap()
		ds = DeclSet.new().add_empty_enum(T.name().concat("Clone"))
		i = 0
		while i < info.variant_count() {
			variant = info.variant_at(i).unwrap()
			payload_opt = variant.payload_type_opt()
			if payload_opt.is_some() {
				payload_ty = payload_opt.unwrap()
				same = payload_ty == I32
				ds = ds.add_enum_payload_variant(T.name().concat("Clone"), variant.name(), payload_ty)
			} else {
				ds = ds.add_enum_tag_variant(T.name().concat("Clone"), variant.name())
			}
			i = i + 1
		}
		return ds
	}
	return DeclSet.new()
}

comptime apply reflect(Token)

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        resolve(ast).expect("resolve source");
    }

    #[test]
    fn resolve_rejects_runtime_enum_semantic_introspection_builtin_call() {
        let source = r#"
enum Token {
	Int: I32,
	Plus,
}

fun main() -> I32 {
	info = Type.resolve("Token").as_enum_opt()
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("resolve should fail");
        assert!(
            err.to_string()
                .contains("runtime function main cannot call comptime function Type__"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn resolve_rejects_runtime_enum_semantic_emission_builtin_call() {
        let source = r#"
fun main() -> I32 {
	ds = DeclSet.new().add_empty_enum("TokenTags")
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("resolve should fail");
        assert!(
            err.to_string()
                .contains("runtime function main cannot call comptime function DeclSet__"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn resolve_rejects_runtime_semantic_emission_builtin_call() {
        let source = r#"
fun main() -> I32 {
	ds = DeclSet.new()
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("resolve should fail");
        assert!(
            err.to_string()
                .contains("runtime function main cannot call comptime function DeclSet__new"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn resolve_rejects_runtime_calling_comptime_function() {
        let source = r#"
comptime fun build_counter(name: String) -> DeclSet {
	return DeclSet.new()
}

fun main() -> I32 {
	x = build_counter("I32")
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("resolve should fail");
        assert!(
            err.to_string()
                .contains("runtime function main cannot call comptime function build_counter"),
            "unexpected error: {err}"
        );
    }
}
