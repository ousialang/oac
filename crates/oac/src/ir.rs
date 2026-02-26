//! Type-checking and IR generation.

use std::collections::{HashMap, HashSet};

use serde::Serialize;
use tracing::trace;

use crate::{
    builtins::BuiltInType,
    flat_imports,
    parser::{self, Ast, Expression, Literal, StructDef, UnaryOp},
};

const LEGACY_INVARIANT_PREFIX: &str = "__struct__";
const LEGACY_INVARIANT_SUFFIX: &str = "__invariant";
const RESERVED_BUILTIN_FUNCTION_NAMES: [&str; 2] = ["prove", "assert"];
const SEMANTIC_BUILTIN_TYPES: [&str; 6] = [
    "Type",
    "DeclSet",
    "SemanticExpr",
    "SourceSpan",
    "StructInfo",
    "FieldInfo",
];
const SEMANTIC_EMISSION_BUILTINS: [&str; 3] = [
    "declset_new",
    "declset_add_derived_struct",
    "declset_add_invariant_field_gt_i32",
];
const SEMANTIC_INTROSPECTION_BUILTINS: [&str; 13] = [
    "expr_meta_opt",
    "definition_location_opt",
    "is_struct",
    "as_struct_opt",
    "struct_field_count",
    "struct_field_at",
    "field_name",
    "field_type",
    "type_name",
    "resolve_type",
    "is_some",
    "unwrap",
    "concat",
];

fn normalize_numeric_alias(ty: &str) -> &str {
    match ty {
        "Int" => "I32",
        "PtrInt" => "I64",
        _ => ty,
    }
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
    pub struct_invariants: HashMap<String, StructInvariantDefinition>,
    pub comptime_function_definitions: HashMap<String, FunctionDefinition>,
    pub comptime_apply_order: Vec<parser::ComptimeApply>,
    pub semantic_expr_metadata: HashMap<String, SemanticExprMetadata>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct SourceSpan {
    pub file: Option<String>,
    pub start_line: Option<u32>,
    pub start_column: Option<u32>,
    pub end_line: Option<u32>,
    pub end_column: Option<u32>,
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
    pub identifier: Option<String>,
    pub display_name: String,
}

impl ResolvedProgram {
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
                let subject_type = get_expression_type(
                    subject,
                    var_types,
                    &self.function_sigs,
                    &self.type_definitions,
                )?;
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
                let condition_type = get_expression_type(
                    condition,
                    var_types,
                    &self.function_sigs,
                    &self.type_definitions,
                )?;
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
                let condition_type = get_expression_type(
                    condition,
                    var_types,
                    &self.function_sigs,
                    &self.type_definitions,
                )?;
                if condition_type != "Bool" {
                    return Err(anyhow::anyhow!(
                        "prove expects Bool condition, got {:?}",
                        condition_type
                    ));
                }
            }
            parser::Statement::Assert { condition } => {
                let condition_type = get_expression_type(
                    condition,
                    var_types,
                    &self.function_sigs,
                    &self.type_definitions,
                )?;
                if condition_type != "Bool" {
                    return Err(anyhow::anyhow!(
                        "assert expects Bool condition, got {:?}",
                        condition_type
                    ));
                }
            }
            parser::Statement::While { condition, body } => {
                let condition_type = get_expression_type(
                    condition,
                    var_types,
                    &self.function_sigs,
                    &self.type_definitions,
                )?;
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
                let variable_type = get_expression_type(
                    value,
                    &var_types,
                    &self.function_sigs,
                    &self.type_definitions,
                )?;
                if variable_type == "Void" {
                    return Err(anyhow::anyhow!(
                        "cannot assign expression of type Void to variable {}",
                        variable
                    ));
                }
                var_types.insert(variable.clone(), variable_type);
            }
            parser::Statement::Return { expr } => {
                let expr_type = get_expression_type(
                    expr,
                    &var_types,
                    &self.function_sigs,
                    &self.type_definitions,
                )?;
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
                let _ = get_expression_type(
                    expr,
                    &var_types,
                    &self.function_sigs,
                    &self.type_definitions,
                )?;
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
}

pub type TypeRef = String;

#[derive(Clone, Debug, Serialize)]
pub struct FunctionDefinition {
    pub name: String,
    pub body: Vec<parser::Statement>,
    pub sig: FunctionSignature,
}

#[tracing::instrument(level = "trace", skip_all)]
pub fn resolve(mut ast: Ast) -> anyhow::Result<ResolvedProgram> {
    {
        let stdlib_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src")
            .join("std.oa");
        let stdlib_ast = flat_imports::parse_and_resolve_file(&stdlib_path)?;

        ast.top_level_functions
            .extend(stdlib_ast.top_level_functions);
        ast.type_definitions.extend(stdlib_ast.type_definitions);
        ast.template_definitions
            .extend(stdlib_ast.template_definitions);
        ast.template_instantiations
            .extend(stdlib_ast.template_instantiations);
        ast.invariants.extend(stdlib_ast.invariants);
    }
    expand_templates(&mut ast)?;

    let mut program = ResolvedProgram {
        ast: ast.clone(),
        function_definitions: HashMap::new(),
        function_sigs: HashMap::new(),
        type_definitions: HashMap::new(),
        struct_invariants: HashMap::new(),
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
        .insert("String".to_string(), TypeDef::BuiltIn(BuiltInType::String))
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert String type definition"))
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
                TypeDef::BuiltIn(BuiltInType::String),
            )
            .map_or(Ok(()), |_| {
                Err(anyhow::anyhow!(
                    "failed to insert semantic builtin type definition for {}",
                    semantic_ty
                ))
            })?;
    }

    // Built-in functions

    program
        .function_sigs
        .insert(
            "sub".to_string(),
            FunctionSignature {
                parameters: vec![
                    FunctionParameter {
                        name: "a".to_string(),
                        ty: "I32".to_string(),
                    },
                    FunctionParameter {
                        name: "b".to_string(),
                        ty: "I32".to_string(),
                    },
                ],
                return_type: "I32".to_string(),
            },
        )
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert sub function signature"))
        })?;

    program
        .function_sigs
        .insert(
            "eq".to_string(),
            FunctionSignature {
                parameters: vec![
                    FunctionParameter {
                        name: "a".to_string(),
                        ty: "I32".to_string(),
                    },
                    FunctionParameter {
                        name: "b".to_string(),
                        ty: "I32".to_string(),
                    },
                ],
                return_type: "Bool".to_string(),
            },
        )
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert eq function signature"))
        })?;

    program
        .function_sigs
        .insert(
            "sum".to_string(),
            FunctionSignature {
                parameters: vec![
                    FunctionParameter {
                        name: "a".to_string(),
                        ty: "I32".to_string(),
                    },
                    FunctionParameter {
                        name: "b".to_string(),
                        ty: "I32".to_string(),
                    },
                ],
                return_type: "I32".to_string(),
            },
        )
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert sum function signature"))
        })?;

    program
        .function_sigs
        .insert(
            "lt".to_string(),
            FunctionSignature {
                parameters: vec![
                    FunctionParameter {
                        name: "a".to_string(),
                        ty: "I32".to_string(),
                    },
                    FunctionParameter {
                        name: "b".to_string(),
                        ty: "I32".to_string(),
                    },
                ],
                return_type: "Bool".to_string(),
            },
        )
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert lt function signature"))
        })?;

    program.function_sigs.insert(
        "print".to_string(),
        FunctionSignature {
            parameters: vec![FunctionParameter {
                name: "a".to_string(),
                ty: "I32".to_string(),
            }],
            return_type: "I32".to_string(),
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
        },
    );
    program.function_sigs.insert(
        "string_len".to_string(),
        FunctionSignature {
            parameters: vec![FunctionParameter {
                name: "s".to_string(),
                ty: "String".to_string(),
            }],
            return_type: "I32".to_string(),
        },
    );
    program.function_sigs.insert(
        "slice".to_string(),
        FunctionSignature {
            parameters: vec![
                FunctionParameter {
                    name: "s".to_string(),
                    ty: "String".to_string(),
                },
                FunctionParameter {
                    name: "start".to_string(),
                    ty: "I32".to_string(),
                },
                FunctionParameter {
                    name: "len".to_string(),
                    ty: "I32".to_string(),
                },
            ],
            return_type: "String".to_string(),
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
        },
    );

    program
        .function_sigs
        .insert(
            "print_str".to_string(),
            FunctionSignature {
                parameters: vec![FunctionParameter {
                    name: "a".to_string(),
                    ty: "String".to_string(),
                }],
                return_type: "I32".to_string(),
            },
        )
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!(
                "failed to insert print_str function signature"
            ))
        })?;

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
    let synthesized_invariants = synthesize_invariant_functions(
        &ast.invariants,
        &program.type_definitions,
        &ast.top_level_functions,
        &mut program.struct_invariants,
    )?;
    all_functions.extend(synthesized_invariants);

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
            sig,
            body: function.body.clone(),
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
        };
        let definition = FunctionDefinition {
            name: function.name.clone(),
            body: function.body.clone(),
            sig,
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
    for func_def in program.function_definitions.values() {
        program.type_check(func_def)?;
    }

    reject_runtime_semantic_builtin_usage(&program)?;
    program.semantic_expr_metadata = index_semantic_expression_metadata(&program);

    if !program.function_definitions.contains_key("main") {
        return Err(anyhow::anyhow!("main function not defined"));
    }
    validate_main_signature(&program)?;

    Ok(program)
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
    for param in &sig.parameters {
        if !type_definitions.contains_key(&param.ty) {
            return Err(anyhow::anyhow!(
                "function {} has parameter {} with unknown type {}",
                function_name,
                param.name,
                param.ty
            ));
        }
        if param.ty == "Void" {
            return Err(anyhow::anyhow!(
                "function {} cannot use Void as parameter type ({})",
                function_name,
                param.name
            ));
        }
    }

    if !type_definitions.contains_key(&sig.return_type) {
        return Err(anyhow::anyhow!(
            "function {} has unknown return type {}",
            function_name,
            sig.return_type
        ));
    }

    if sig.return_type == "Void" && !allow_void_return {
        return Err(anyhow::anyhow!(
            "function {} cannot return Void (only extern functions may return Void in v1)",
            function_name
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

fn collect_called_functions_in_statement(
    statement: &parser::Statement,
    program: &ResolvedProgram,
    out: &mut Vec<String>,
) {
    match statement {
        parser::Statement::StructDef { .. } => {}
        parser::Statement::Assign { value, .. } => {
            collect_called_functions_in_expression(value, program, out)
        }
        parser::Statement::Return { expr } => {
            collect_called_functions_in_expression(expr, program, out)
        }
        parser::Statement::Expression { expr } => {
            collect_called_functions_in_expression(expr, program, out)
        }
        parser::Statement::Prove { condition } => {
            collect_called_functions_in_expression(condition, program, out)
        }
        parser::Statement::Assert { condition } => {
            collect_called_functions_in_expression(condition, program, out)
        }
        parser::Statement::Conditional {
            condition,
            body,
            else_body,
        } => {
            collect_called_functions_in_expression(condition, program, out);
            for statement in body {
                collect_called_functions_in_statement(statement, program, out);
            }
            if let Some(else_body) = else_body {
                for statement in else_body {
                    collect_called_functions_in_statement(statement, program, out);
                }
            }
        }
        parser::Statement::While { condition, body } => {
            collect_called_functions_in_expression(condition, program, out);
            for statement in body {
                collect_called_functions_in_statement(statement, program, out);
            }
        }
        parser::Statement::Match { subject, arms } => {
            collect_called_functions_in_expression(subject, program, out);
            for arm in arms {
                for statement in &arm.body {
                    collect_called_functions_in_statement(statement, program, out);
                }
            }
        }
    }
}

fn collect_called_functions_in_expression(
    expression: &Expression,
    program: &ResolvedProgram,
    out: &mut Vec<String>,
) {
    match expression {
        Expression::Match { subject, arms } => {
            collect_called_functions_in_expression(subject, program, out);
            for arm in arms {
                collect_called_functions_in_expression(&arm.value, program, out);
            }
        }
        Expression::Literal(_) | Expression::Variable(_) => {}
        Expression::Call(name, args) => {
            out.push(name.clone());
            for arg in args {
                collect_called_functions_in_expression(arg, program, out);
            }
        }
        Expression::PostfixCall { callee, args } => {
            if let Expression::FieldAccess {
                struct_variable,
                field,
            } = callee.as_ref()
            {
                let namespaced_call =
                    parser::qualify_namespace_function_name(struct_variable, field);
                if program.function_sigs.contains_key(&namespaced_call) {
                    out.push(namespaced_call);
                }
            }
            collect_called_functions_in_expression(callee, program, out);
            for arg in args {
                collect_called_functions_in_expression(arg, program, out);
            }
        }
        Expression::BinOp(_, left, right) => {
            collect_called_functions_in_expression(left, program, out);
            collect_called_functions_in_expression(right, program, out);
        }
        Expression::UnaryOp(_, expr) => collect_called_functions_in_expression(expr, program, out),
        Expression::FieldAccess { .. } => {}
        Expression::StructValue { field_values, .. } => {
            for (_, value) in field_values {
                collect_called_functions_in_expression(value, program, out);
            }
        }
    }
}

fn index_semantic_expression_metadata(
    program: &ResolvedProgram,
) -> HashMap<String, SemanticExprMetadata> {
    let mut out = HashMap::new();
    for (name, function) in &program.function_definitions {
        for (statement_index, statement) in function.body.iter().enumerate() {
            index_statement_expression_metadata(
                statement,
                &format!("fn:{name}/stmt:{statement_index}"),
                &mut out,
            );
        }
    }
    for (name, function) in &program.comptime_function_definitions {
        for (statement_index, statement) in function.body.iter().enumerate() {
            index_statement_expression_metadata(
                statement,
                &format!("comptime_fn:{name}/stmt:{statement_index}"),
                &mut out,
            );
        }
    }
    out
}

fn index_statement_expression_metadata(
    statement: &parser::Statement,
    path: &str,
    out: &mut HashMap<String, SemanticExprMetadata>,
) {
    match statement {
        parser::Statement::StructDef { .. } => {}
        parser::Statement::Assign { value, .. } => {
            index_expression_metadata(value, &format!("{path}/assign.value"), out)
        }
        parser::Statement::Return { expr } => {
            index_expression_metadata(expr, &format!("{path}/return.expr"), out)
        }
        parser::Statement::Expression { expr } => {
            index_expression_metadata(expr, &format!("{path}/expr"), out)
        }
        parser::Statement::Prove { condition } => {
            index_expression_metadata(condition, &format!("{path}/prove.cond"), out)
        }
        parser::Statement::Assert { condition } => {
            index_expression_metadata(condition, &format!("{path}/assert.cond"), out)
        }
        parser::Statement::Conditional {
            condition,
            body,
            else_body,
        } => {
            index_expression_metadata(condition, &format!("{path}/if.cond"), out);
            for (index, statement) in body.iter().enumerate() {
                index_statement_expression_metadata(
                    statement,
                    &format!("{path}/if.body.{index}"),
                    out,
                );
            }
            if let Some(else_body) = else_body {
                for (index, statement) in else_body.iter().enumerate() {
                    index_statement_expression_metadata(
                        statement,
                        &format!("{path}/if.else.{index}"),
                        out,
                    );
                }
            }
        }
        parser::Statement::While { condition, body } => {
            index_expression_metadata(condition, &format!("{path}/while.cond"), out);
            for (index, statement) in body.iter().enumerate() {
                index_statement_expression_metadata(
                    statement,
                    &format!("{path}/while.body.{index}"),
                    out,
                );
            }
        }
        parser::Statement::Match { subject, arms } => {
            index_expression_metadata(subject, &format!("{path}/match.subject"), out);
            for (arm_index, arm) in arms.iter().enumerate() {
                for (statement_index, statement) in arm.body.iter().enumerate() {
                    index_statement_expression_metadata(
                        statement,
                        &format!("{path}/match.arm.{arm_index}.{statement_index}"),
                        out,
                    );
                }
            }
        }
    }
}

fn index_expression_metadata(
    expression: &Expression,
    path: &str,
    out: &mut HashMap<String, SemanticExprMetadata>,
) {
    out.insert(
        path.to_string(),
        SemanticExprMetadata {
            id: path.to_string(),
            ty: None,
            source_span: None,
        },
    );

    match expression {
        Expression::Match { subject, arms } => {
            index_expression_metadata(subject, &format!("{path}/match.subject"), out);
            for (index, arm) in arms.iter().enumerate() {
                index_expression_metadata(&arm.value, &format!("{path}/match.arm.{index}"), out);
            }
        }
        Expression::Literal(_) | Expression::Variable(_) | Expression::FieldAccess { .. } => {}
        Expression::Call(_, args) => {
            for (index, arg) in args.iter().enumerate() {
                index_expression_metadata(arg, &format!("{path}/call.arg.{index}"), out);
            }
        }
        Expression::PostfixCall { callee, args } => {
            index_expression_metadata(callee, &format!("{path}/postfix.callee"), out);
            for (index, arg) in args.iter().enumerate() {
                index_expression_metadata(arg, &format!("{path}/postfix.arg.{index}"), out);
            }
        }
        Expression::BinOp(_, left, right) => {
            index_expression_metadata(left, &format!("{path}/bin.left"), out);
            index_expression_metadata(right, &format!("{path}/bin.right"), out);
        }
        Expression::UnaryOp(_, expr) => {
            index_expression_metadata(expr, &format!("{path}/unary"), out);
        }
        Expression::StructValue { field_values, .. } => {
            for (index, (_, value)) in field_values.iter().enumerate() {
                index_expression_metadata(value, &format!("{path}/struct.field.{index}"), out);
            }
        }
    }
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

fn generated_invariant_function_name(struct_name: &str) -> String {
    format!(
        "{}{}{}",
        LEGACY_INVARIANT_PREFIX, struct_name, LEGACY_INVARIANT_SUFFIX
    )
}

fn synthesize_invariant_functions(
    invariants: &[parser::StructInvariantDecl],
    type_definitions: &HashMap<String, TypeDef>,
    existing_functions: &[parser::Function],
    out_struct_invariants: &mut HashMap<String, StructInvariantDefinition>,
) -> anyhow::Result<Vec<parser::Function>> {
    let mut out = Vec::new();
    for invariant in invariants {
        let struct_name = invariant.parameter.ty.clone();
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

        let function_name = generated_invariant_function_name(&struct_name);
        if existing_functions.iter().any(|f| f.name == function_name) {
            return Err(anyhow::anyhow!(
                "invariant \"{}\" for {} conflicts with existing function {}",
                invariant.display_name,
                struct_name,
                function_name
            ));
        }

        if let Some(existing) = out_struct_invariants.get(&struct_name) {
            return Err(anyhow::anyhow!(
                "struct {} has multiple invariants: \"{}\" and \"{}\"",
                struct_name,
                existing.display_name,
                invariant.display_name
            ));
        }
        out_struct_invariants.insert(
            struct_name.clone(),
            StructInvariantDefinition {
                struct_name: struct_name.clone(),
                function_name: function_name.clone(),
                identifier: invariant.identifier.clone(),
                display_name: invariant.display_name.clone(),
            },
        );

        out.push(parser::Function {
            name: function_name,
            parameters: vec![invariant.parameter.clone()],
            body: invariant.body.clone(),
            return_type: "Bool".to_string(),
            is_comptime: false,
            is_extern: false,
        });
    }
    Ok(out)
}

fn register_legacy_struct_invariants(
    functions: &[parser::Function],
    type_definitions: &HashMap<String, TypeDef>,
    function_sigs: &HashMap<String, FunctionSignature>,
    out_struct_invariants: &mut HashMap<String, StructInvariantDefinition>,
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

        if let Some(existing) = out_struct_invariants.get(struct_name) {
            if existing.function_name != function.name {
                return Err(anyhow::anyhow!(
                    "struct {} has multiple invariants: \"{}\" and \"{}\"",
                    struct_name,
                    existing.display_name,
                    function.name
                ));
            }
            continue;
        }

        out_struct_invariants.insert(
            struct_name.to_string(),
            StructInvariantDefinition {
                struct_name: struct_name.to_string(),
                function_name: function.name.clone(),
                identifier: None,
                display_name: function.name.clone(),
            },
        );
    }
    Ok(())
}

fn rewrite_type_ref(
    ty: &str,
    type_param: &str,
    concrete_type: &str,
    local_type_name_map: &HashMap<String, String>,
) -> String {
    if ty == type_param {
        concrete_type.to_string()
    } else if let Some(mapped) = local_type_name_map.get(ty) {
        mapped.clone()
    } else {
        ty.to_string()
    }
}

fn rewrite_expression(
    expr: &Expression,
    local_type_name_map: &HashMap<String, String>,
    local_function_name_map: &HashMap<String, String>,
) -> Expression {
    match expr {
        Expression::Match { subject, arms } => Expression::Match {
            subject: Box::new(rewrite_expression(
                subject,
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
                            type_name: local_type_name_map
                                .get(type_name)
                                .cloned()
                                .unwrap_or_else(|| type_name.clone()),
                            variant_name: variant_name.clone(),
                            binder: binder.clone(),
                        },
                    },
                    value: rewrite_expression(
                        &arm.value,
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
                        rewrite_expression(arg, local_type_name_map, local_function_name_map)
                    })
                    .collect(),
            )
        }
        Expression::PostfixCall { callee, args } => Expression::PostfixCall {
            callee: Box::new(rewrite_expression(
                callee,
                local_type_name_map,
                local_function_name_map,
            )),
            args: args
                .iter()
                .map(|arg| rewrite_expression(arg, local_type_name_map, local_function_name_map))
                .collect(),
        },
        Expression::BinOp(op, left, right) => Expression::BinOp(
            *op,
            Box::new(rewrite_expression(
                left,
                local_type_name_map,
                local_function_name_map,
            )),
            Box::new(rewrite_expression(
                right,
                local_type_name_map,
                local_function_name_map,
            )),
        ),
        Expression::UnaryOp(op, expr) => Expression::UnaryOp(
            *op,
            Box::new(rewrite_expression(
                expr,
                local_type_name_map,
                local_function_name_map,
            )),
        ),
        Expression::FieldAccess {
            struct_variable,
            field,
        } => Expression::FieldAccess {
            struct_variable: local_type_name_map
                .get(struct_variable)
                .cloned()
                .unwrap_or_else(|| struct_variable.clone()),
            field: field.clone(),
        },
        Expression::StructValue {
            struct_name,
            field_values,
        } => Expression::StructValue {
            struct_name: local_type_name_map
                .get(struct_name)
                .cloned()
                .unwrap_or_else(|| struct_name.clone()),
            field_values: field_values
                .iter()
                .map(|(name, expr)| {
                    (
                        name.clone(),
                        rewrite_expression(expr, local_type_name_map, local_function_name_map),
                    )
                })
                .collect(),
        },
    }
}

fn rewrite_statement(
    statement: &parser::Statement,
    local_type_name_map: &HashMap<String, String>,
    local_function_name_map: &HashMap<String, String>,
) -> parser::Statement {
    match statement {
        parser::Statement::StructDef { def } => parser::Statement::StructDef { def: def.clone() },
        parser::Statement::Match { subject, arms } => parser::Statement::Match {
            subject: rewrite_expression(subject, local_type_name_map, local_function_name_map),
            arms: arms
                .iter()
                .map(|arm| parser::MatchArm {
                    pattern: match &arm.pattern {
                        parser::MatchPattern::Variant {
                            type_name,
                            variant_name,
                            binder,
                        } => parser::MatchPattern::Variant {
                            type_name: local_type_name_map
                                .get(type_name)
                                .cloned()
                                .unwrap_or_else(|| type_name.clone()),
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
            condition: rewrite_expression(condition, local_type_name_map, local_function_name_map),
            body: body
                .iter()
                .map(|statement| {
                    rewrite_statement(statement, local_type_name_map, local_function_name_map)
                })
                .collect(),
            else_body: else_body.as_ref().map(|body| {
                body.iter()
                    .map(|statement| {
                        rewrite_statement(statement, local_type_name_map, local_function_name_map)
                    })
                    .collect()
            }),
        },
        parser::Statement::Assign { variable, value } => parser::Statement::Assign {
            variable: variable.clone(),
            value: rewrite_expression(value, local_type_name_map, local_function_name_map),
        },
        parser::Statement::Return { expr } => parser::Statement::Return {
            expr: rewrite_expression(expr, local_type_name_map, local_function_name_map),
        },
        parser::Statement::Expression { expr } => parser::Statement::Expression {
            expr: rewrite_expression(expr, local_type_name_map, local_function_name_map),
        },
        parser::Statement::Prove { condition } => parser::Statement::Prove {
            condition: rewrite_expression(condition, local_type_name_map, local_function_name_map),
        },
        parser::Statement::Assert { condition } => parser::Statement::Assert {
            condition: rewrite_expression(condition, local_type_name_map, local_function_name_map),
        },
        parser::Statement::While { condition, body } => parser::Statement::While {
            condition: rewrite_expression(condition, local_type_name_map, local_function_name_map),
            body: body
                .iter()
                .map(|statement| {
                    rewrite_statement(statement, local_type_name_map, local_function_name_map)
                })
                .collect(),
        },
    }
}

fn expand_templates(ast: &mut Ast) -> anyhow::Result<()> {
    let mut templates_by_name: HashMap<String, parser::TemplateDef> = HashMap::new();
    for template in &ast.template_definitions {
        if templates_by_name
            .insert(template.name.clone(), template.clone())
            .is_some()
        {
            return Err(anyhow::anyhow!(
                "duplicate template definition {}",
                template.name
            ));
        }
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

    for instantiation in &ast.template_instantiations {
        let template = templates_by_name
            .get(&instantiation.template_name)
            .ok_or_else(|| {
                anyhow::anyhow!(
                    "unknown template {} in instantiation {}",
                    instantiation.template_name,
                    instantiation.alias
                )
            })?;

        let mut local_type_name_map: HashMap<String, String> = HashMap::new();
        for type_def in &template.type_definitions {
            let local_name = type_def_name(type_def).to_string();
            let mapped_name = if local_name == template.name {
                instantiation.alias.clone()
            } else {
                format!("{}__{}", instantiation.alias, local_name)
            };
            local_type_name_map.insert(local_name, mapped_name);
        }

        if !local_type_name_map.contains_key(&template.name) {
            return Err(anyhow::anyhow!(
                "template {} must define a primary type named {}",
                template.name,
                template.name
            ));
        }

        let mut local_function_name_map: HashMap<String, String> = HashMap::new();
        for function in &template.top_level_functions {
            local_function_name_map.insert(
                function.name.clone(),
                format!("{}__{}", instantiation.alias, function.name),
            );
        }

        for mapped_name in local_type_name_map.values() {
            if !used_type_names.insert(mapped_name.clone()) {
                return Err(anyhow::anyhow!(
                    "duplicate generated type name {} from template instantiation {}",
                    mapped_name,
                    instantiation.alias
                ));
            }
        }
        for mapped_name in local_function_name_map.values() {
            if !used_function_names.insert(mapped_name.clone()) {
                return Err(anyhow::anyhow!(
                    "duplicate generated function name {} from template instantiation {}",
                    mapped_name,
                    instantiation.alias
                ));
            }
        }

        for type_def in &template.type_definitions {
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
                                    &template.type_param,
                                    &instantiation.concrete_type,
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
                                    &template.type_param,
                                    &instantiation.concrete_type,
                                    &local_type_name_map,
                                )
                            }),
                        })
                        .collect(),
                }),
            };
            generated_type_defs.push(rewritten);
        }

        for function in &template.top_level_functions {
            generated_functions.push(parser::Function {
                name: local_function_name_map
                    .get(&function.name)
                    .cloned()
                    .unwrap_or_else(|| function.name.clone()),
                parameters: function
                    .parameters
                    .iter()
                    .map(|param| parser::Parameter {
                        name: param.name.clone(),
                        ty: rewrite_type_ref(
                            &param.ty,
                            &template.type_param,
                            &instantiation.concrete_type,
                            &local_type_name_map,
                        ),
                    })
                    .collect(),
                body: function
                    .body
                    .iter()
                    .map(|statement| {
                        rewrite_statement(statement, &local_type_name_map, &local_function_name_map)
                    })
                    .collect(),
                return_type: rewrite_type_ref(
                    &function.return_type,
                    &template.type_param,
                    &instantiation.concrete_type,
                    &local_type_name_map,
                ),
                is_comptime: function.is_comptime,
                is_extern: function.is_extern,
            });
        }

        for invariant in &template.invariants {
            generated_invariants.push(parser::StructInvariantDecl {
                identifier: invariant.identifier.clone(),
                display_name: invariant.display_name.clone(),
                parameter: parser::Parameter {
                    name: invariant.parameter.name.clone(),
                    ty: rewrite_type_ref(
                        &invariant.parameter.ty,
                        &template.type_param,
                        &instantiation.concrete_type,
                        &local_type_name_map,
                    ),
                },
                body: invariant
                    .body
                    .iter()
                    .map(|statement| {
                        rewrite_statement(statement, &local_type_name_map, &local_function_name_map)
                    })
                    .collect(),
            });
        }
    }

    ast.type_definitions.extend(generated_type_defs);
    ast.top_level_functions.extend(generated_functions);
    ast.invariants.extend(generated_invariants);
    Ok(())
}

pub(crate) fn get_expression_type(
    expr: &Expression,
    var_types: &HashMap<String, TypeRef>,
    fns: &HashMap<String, FunctionSignature>,
    type_definitions: &HashMap<String, TypeDef>,
) -> anyhow::Result<TypeRef> {
    match expr {
        Expression::Match { subject, arms } => {
            let subject_type = get_expression_type(subject, var_types, fns, type_definitions)?;
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

                let ty = get_expression_type(&arm.value, &scoped_var_types, fns, type_definitions)?;
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
                        let arg_ty =
                            get_expression_type(&args[0], var_types, fns, type_definitions)?;
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
                        );
                    }

                    return Err(anyhow::anyhow!(
                        "variant {} not found in enum {}",
                        field,
                        struct_variable
                    ));
                }

                let namespaced_call =
                    parser::qualify_namespace_function_name(struct_variable, field);
                if fns.contains_key(&namespaced_call) {
                    return get_expression_type(
                        &Expression::Call(namespaced_call, args.clone()),
                        var_types,
                        fns,
                        type_definitions,
                    );
                }

                Err(anyhow::anyhow!(
                    "unsupported call target {:?}",
                    callee.as_ref()
                ))
            }
            _ => Err(anyhow::anyhow!(
                "unsupported call target {:?}",
                callee.as_ref()
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
                    let value_type = get_expression_type(value, var_types, fns, type_definitions)?;
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
            if function == "is_some" {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "is_some expects exactly one argument, got {}",
                        arguments.len()
                    ));
                }
                let arg_type =
                    get_expression_type(&arguments[0], var_types, fns, type_definitions)?;
                if !arg_type.starts_with("Option[") || !arg_type.ends_with(']') {
                    return Err(anyhow::anyhow!(
                        "is_some expects an Option[T] argument, got {}",
                        arg_type
                    ));
                }
                return Ok("Bool".to_string());
            }
            if function == "unwrap" {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "unwrap expects exactly one argument, got {}",
                        arguments.len()
                    ));
                }
                let arg_type =
                    get_expression_type(&arguments[0], var_types, fns, type_definitions)?;
                let Some(inner) = arg_type
                    .strip_prefix("Option[")
                    .and_then(|s| s.strip_suffix(']'))
                else {
                    return Err(anyhow::anyhow!(
                        "unwrap expects an Option[T] argument, got {}",
                        arg_type
                    ));
                };
                return Ok(inner.to_string());
            }
            if function == "concat" {
                if arguments.len() != 2 {
                    return Err(anyhow::anyhow!(
                        "concat expects exactly two String arguments, got {}",
                        arguments.len()
                    ));
                }
                let left = get_expression_type(&arguments[0], var_types, fns, type_definitions)?;
                let right = get_expression_type(&arguments[1], var_types, fns, type_definitions)?;
                if left != "String" || right != "String" {
                    return Err(anyhow::anyhow!(
                        "concat expects (String, String), got ({}, {})",
                        left,
                        right
                    ));
                }
                return Ok("String".to_string());
            }
            if function == "type_name" {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "type_name expects exactly one Type argument, got {}",
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(&arguments[0], var_types, fns, type_definitions)?;
                if arg_ty != "Type" {
                    return Err(anyhow::anyhow!(
                        "type_name expects Type argument, got {}",
                        arg_ty
                    ));
                }
                return Ok("String".to_string());
            }
            if function == "resolve_type" {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "resolve_type expects exactly one String argument, got {}",
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(&arguments[0], var_types, fns, type_definitions)?;
                if arg_ty != "String" {
                    return Err(anyhow::anyhow!(
                        "resolve_type expects String argument, got {}",
                        arg_ty
                    ));
                }
                return Ok("Type".to_string());
            }
            if function == "expr_meta_opt" {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "expr_meta_opt expects exactly one argument, got {}",
                        arguments.len()
                    ));
                }
                return Ok("Option[SemanticExpr]".to_string());
            }
            if function == "definition_location_opt" {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "definition_location_opt expects exactly one argument, got {}",
                        arguments.len()
                    ));
                }
                return Ok("Option[SourceSpan]".to_string());
            }
            if function == "is_struct" {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "is_struct expects exactly one Type argument, got {}",
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(&arguments[0], var_types, fns, type_definitions)?;
                if arg_ty != "Type" {
                    return Err(anyhow::anyhow!(
                        "is_struct expects Type argument, got {}",
                        arg_ty
                    ));
                }
                return Ok("Bool".to_string());
            }
            if function == "as_struct_opt" {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "as_struct_opt expects exactly one Type argument, got {}",
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(&arguments[0], var_types, fns, type_definitions)?;
                if arg_ty != "Type" {
                    return Err(anyhow::anyhow!(
                        "as_struct_opt expects Type argument, got {}",
                        arg_ty
                    ));
                }
                return Ok("Option[StructInfo]".to_string());
            }
            if function == "struct_field_count" {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "struct_field_count expects exactly one StructInfo argument, got {}",
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(&arguments[0], var_types, fns, type_definitions)?;
                if arg_ty != "StructInfo" {
                    return Err(anyhow::anyhow!(
                        "struct_field_count expects StructInfo argument, got {}",
                        arg_ty
                    ));
                }
                return Ok("I32".to_string());
            }
            if function == "struct_field_at" {
                if arguments.len() != 2 {
                    return Err(anyhow::anyhow!(
                        "struct_field_at expects (StructInfo, I32), got {} arguments",
                        arguments.len()
                    ));
                }
                let a = get_expression_type(&arguments[0], var_types, fns, type_definitions)?;
                let b = get_expression_type(&arguments[1], var_types, fns, type_definitions)?;
                if a != "StructInfo" || b != "I32" {
                    return Err(anyhow::anyhow!(
                        "struct_field_at expects (StructInfo, I32), got ({}, {})",
                        a,
                        b
                    ));
                }
                return Ok("Option[FieldInfo]".to_string());
            }
            if function == "field_name" {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "field_name expects exactly one FieldInfo argument, got {}",
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(&arguments[0], var_types, fns, type_definitions)?;
                if arg_ty != "FieldInfo" {
                    return Err(anyhow::anyhow!(
                        "field_name expects FieldInfo argument, got {}",
                        arg_ty
                    ));
                }
                return Ok("String".to_string());
            }
            if function == "field_type" {
                if arguments.len() != 1 {
                    return Err(anyhow::anyhow!(
                        "field_type expects exactly one FieldInfo argument, got {}",
                        arguments.len()
                    ));
                }
                let arg_ty = get_expression_type(&arguments[0], var_types, fns, type_definitions)?;
                if arg_ty != "FieldInfo" {
                    return Err(anyhow::anyhow!(
                        "field_type expects FieldInfo argument, got {}",
                        arg_ty
                    ));
                }
                return Ok("Type".to_string());
            }
            if function == "declset_new" {
                if !arguments.is_empty() {
                    return Err(anyhow::anyhow!(
                        "declset_new expects zero arguments, got {}",
                        arguments.len()
                    ));
                }
                return Ok("DeclSet".to_string());
            }
            if function == "declset_add_derived_struct" {
                if arguments.len() != 3 {
                    return Err(anyhow::anyhow!(
                        "declset_add_derived_struct expects (DeclSet, StructInfo, String), got {} arguments",
                        arguments.len()
                    ));
                }
                let a = get_expression_type(&arguments[0], var_types, fns, type_definitions)?;
                let b = get_expression_type(&arguments[1], var_types, fns, type_definitions)?;
                let c = get_expression_type(&arguments[2], var_types, fns, type_definitions)?;
                if a != "DeclSet" || b != "StructInfo" || c != "String" {
                    return Err(anyhow::anyhow!(
                        "declset_add_derived_struct expects (DeclSet, StructInfo, String), got ({}, {}, {})",
                        a,
                        b,
                        c
                    ));
                }
                return Ok("DeclSet".to_string());
            }
            if function == "declset_add_invariant_field_gt_i32" {
                if arguments.len() != 5 {
                    return Err(anyhow::anyhow!(
                        "declset_add_invariant_field_gt_i32 expects (DeclSet, Type, String, String, I32), got {} arguments",
                        arguments.len()
                    ));
                }
                let a = get_expression_type(&arguments[0], var_types, fns, type_definitions)?;
                let b = get_expression_type(&arguments[1], var_types, fns, type_definitions)?;
                let c = get_expression_type(&arguments[2], var_types, fns, type_definitions)?;
                let d = get_expression_type(&arguments[3], var_types, fns, type_definitions)?;
                let e = get_expression_type(&arguments[4], var_types, fns, type_definitions)?;
                if a != "DeclSet" || b != "Type" || c != "String" || d != "String" || e != "I32" {
                    return Err(anyhow::anyhow!(
                        "declset_add_invariant_field_gt_i32 expects (DeclSet, Type, String, String, I32), got ({}, {}, {}, {}, {})",
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
                let arg_type = get_expression_type(arg, var_types, fns, type_definitions)?;
                let compatible = normalize_numeric_alias(param_type)
                    == normalize_numeric_alias(&arg_type)
                    // C interop convenience: permit String where pointer-sized I64 is expected.
                    || (normalize_numeric_alias(param_type) == "I64" && arg_type == "String");
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
            let expr_type = get_expression_type(expr, var_types, fns, type_definitions)?;
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
            let left_type = get_expression_type(left, var_types, fns, type_definitions)?;
            let right_type = get_expression_type(right, var_types, fns, type_definitions)?;
            let left_norm = normalize_numeric_alias(&left_type);
            let right_norm = normalize_numeric_alias(&right_type);
            match op {
                parser::Op::And | parser::Op::Or => {
                    if left_norm == "Bool" && right_norm == "Bool" {
                        Ok("Bool".to_string())
                    } else {
                        Err(anyhow::anyhow!(
                            "expected Bool operands for {:?}, but got {:?} and {:?}",
                            op,
                            left_type,
                            right_type
                        ))
                    }
                }
                parser::Op::Add | parser::Op::Sub | parser::Op::Mul | parser::Op::Div => {
                    if left_norm == "U8" && right_norm == "U8" {
                        Ok("U8".to_string())
                    } else if left_norm == "I32" && right_norm == "I32" {
                        Ok("I32".to_string())
                    } else if left_norm == "I64" && right_norm == "I64" {
                        Ok("I64".to_string())
                    } else if left_norm == "FP32" && right_norm == "FP32" {
                        Ok("FP32".to_string())
                    } else if left_norm == "FP64" && right_norm == "FP64" {
                        Ok("FP64".to_string())
                    } else {
                        Err(anyhow::anyhow!(
                            "expected both operands of {:?} to be numeric, but got {:?} and {:?}",
                            op,
                            left_type,
                            right_type
                        ))
                    }
                }
                parser::Op::Eq | parser::Op::Neq => {
                    if left_norm == right_norm {
                        if let Some(TypeDef::Enum(enum_def)) = type_definitions.get(left_norm) {
                            if enum_def.is_tagged_union {
                                return Err(anyhow::anyhow!(
                                    "direct {:?} comparison is not supported for tagged enum {}",
                                    op,
                                    enum_def.name
                                ));
                            }
                        }
                        Ok("Bool".to_string())
                    } else {
                        Err(anyhow::anyhow!(
                            "expected both operands of {:?} to have the same type, but got {:?} and {:?}",
                            op,
                            left_type,
                            right_type
                        ))
                    }
                }
                parser::Op::Lt | parser::Op::Gt | parser::Op::Le | parser::Op::Ge => {
                    if (left_norm == "U8" && right_norm == "U8")
                        || (left_norm == "I32" && right_norm == "I32")
                        || (left_norm == "I64" && right_norm == "I64")
                        || (left_norm == "FP32" && right_norm == "FP32")
                        || (left_norm == "FP64" && right_norm == "FP64")
                    {
                        Ok("Bool".to_string())
                    } else {
                        Err(anyhow::anyhow!(
                            "expected both operands of {:?} to be numeric and of same width, but got {:?} and {:?}",
                            op,
                            left_type,
                            right_type
                        ))
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{builtins::BuiltInType, parser, tokenizer};

    use super::{resolve, TypeDef};

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
            resolved.function_sigs.contains_key("malloc"),
            "missing malloc extern function from split stdlib"
        );
        assert!(
            resolved.function_sigs.contains_key("free"),
            "missing free extern function from split stdlib"
        );
        assert!(
            resolved.struct_invariants.contains_key("AsciiChar"),
            "missing AsciiChar invariant metadata from split stdlib"
        );
        assert!(
            resolved
                .function_definitions
                .contains_key("__struct__AsciiChar__invariant"),
            "missing __struct__AsciiChar__invariant function from split stdlib"
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
	free(i32_to_i64(0))
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
    fn resolve_rejects_non_extern_void_return() {
        let source = r#"
fun helper() -> Void {
	return 0
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("non-extern Void return should fail");
        assert!(err
            .to_string()
            .contains("only extern functions may return Void"));
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
        assert_eq!(invariant.function_name, "__struct__Counter__invariant");
        assert_eq!(invariant.display_name, "counter value must be non-negative");
        assert_eq!(invariant.identifier.as_deref(), Some("positive_value"));

        let function = resolved
            .function_definitions
            .get("__struct__Counter__invariant")
            .expect("missing synthesized invariant function");
        assert_eq!(function.sig.parameters.len(), 1);
        assert_eq!(function.sig.parameters[0].ty, "Counter");
        assert_eq!(function.sig.return_type, "Bool");
    }

    #[test]
    fn resolve_expands_template_invariant_to_concrete_struct() {
        let source = r#"
template Box[T] {
	struct Box {
		value: T,
	}

	invariant "value must be non-negative" for (v: Box) {
		return v.value >= 0
	}
}

instantiate BoxI32 = Box[I32]

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
        assert_eq!(invariant.function_name, "__struct__BoxI32__invariant");
        assert_eq!(invariant.display_name, "value must be non-negative");
        assert_eq!(invariant.identifier, None);

        let function = resolved
            .function_definitions
            .get("__struct__BoxI32__invariant")
            .expect("missing synthesized BoxI32 invariant function");
        assert_eq!(function.sig.parameters.len(), 1);
        assert_eq!(function.sig.parameters[0].ty, "BoxI32");
        assert_eq!(function.sig.return_type, "Bool");
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
	return declset_new()
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
    }

    #[test]
    fn resolve_accepts_namespaced_calls_to_template_instantiated_helpers() {
        let source = r#"
template Identity[T] {
	struct Identity {
		value: T,
	}

	fun value(v: T) -> T {
		return v
	}
}

instantiate IntIdentity = Identity[I32]

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
            .contains("expected both operands of Add to be numeric"));
    }

    #[test]
    fn resolve_rejects_runtime_semantic_emission_builtin_call() {
        let source = r#"
fun main() -> I32 {
	ds = declset_new()
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let err = resolve(ast).expect_err("resolve should fail");
        assert!(
            err.to_string()
                .contains("cannot call semantic emission builtin declset_new"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn resolve_rejects_runtime_calling_comptime_function() {
        let source = r#"
comptime fun build_counter(name: String) -> DeclSet {
	return declset_new()
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
