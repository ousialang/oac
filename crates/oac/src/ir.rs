//! Type-checking and IR generation.

use std::collections::{HashMap, HashSet};

use serde::Serialize;
use tracing::trace;

use crate::{
    builtins::{libc_type_signatures, BuiltInType},
    parser::{self, Ast, Expression, Literal, StructDef, UnaryOp},
    tokenizer,
};

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
}

impl ResolvedProgram {
    fn type_check(&self, func_def: &FunctionDefinition) -> anyhow::Result<()> {
        let mut var_types: HashMap<String, TypeRef> = HashMap::new();
        for param in &func_def.sig.parameters {
            var_types.insert(param.name.clone(), param.ty.clone());
        }

        let mut return_type = None;
        for statement in &func_def.body {
            self.type_check_statement(statement, &mut var_types, &mut return_type)?;
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
        let stdlib_source = include_str!("std.oa");
        let stdlib_tokens = tokenizer::tokenize(stdlib_source.to_string())?;
        let stdlib_ast = parser::parse(stdlib_tokens)?;

        ast.top_level_functions
            .extend(stdlib_ast.top_level_functions);
        ast.type_definitions.extend(stdlib_ast.type_definitions);
        ast.template_definitions
            .extend(stdlib_ast.template_definitions);
        ast.template_instantiations
            .extend(stdlib_ast.template_instantiations);
    }
    expand_templates(&mut ast)?;

    let mut program = ResolvedProgram {
        ast: ast.clone(),
        function_definitions: HashMap::new(),
        function_sigs: HashMap::new(),
        type_definitions: HashMap::new(),
    };

    program
        .type_definitions
        .insert("Int".to_string(), TypeDef::BuiltIn(BuiltInType::I32))
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert Int type definition"))
        })?;
    program
        .type_definitions
        .insert("Bool".to_string(), TypeDef::BuiltIn(BuiltInType::Bool))
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert Bool type definition"))
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
        .insert("String".to_string(), TypeDef::BuiltIn(BuiltInType::String))
        .map_or(Ok(()), |_| {
            Err(anyhow::anyhow!("failed to insert String type definition"))
        })?;

    // Built-in functions

    for signature in libc_type_signatures() {
        let sig = FunctionSignature {
            parameters: signature
                .params
                .iter()
                .map(|param| FunctionParameter {
                    name: param.name.clone(),
                    ty: param.r#type.clone(),
                })
                .collect(),
            return_type: signature.return_type.clone(),
        };

        // libc symbol as-is, e.g. `strcmp`.
        program
            .function_sigs
            .insert(signature.name.clone(), sig.clone());
        // Backward-compatible alias, e.g. `c_strcmp`.
        program
            .function_sigs
            .insert(format!("c_{}", signature.name), sig);
    }

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

    // Pass 1: register signatures for all top-level functions.
    for function in ast.top_level_functions.iter() {
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

    // Pass 2: register function bodies.
    for function in ast.top_level_functions.iter() {
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

    // Pass 3: type-check with all signatures available.
    for func_def in program.function_definitions.values() {
        program.type_check(func_def)?;
    }

    if !program.function_definitions.contains_key("main") {
        Err(anyhow::anyhow!("main function not defined"))
    } else {
        Ok(program)
    }
}

fn type_def_name(type_def: &parser::TypeDefDecl) -> &str {
    match type_def {
        parser::TypeDefDecl::Struct(s) => &s.name,
        parser::TypeDefDecl::Enum(e) => &e.name,
    }
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
            });
        }
    }

    ast.type_definitions.extend(generated_type_defs);
    ast.top_level_functions.extend(generated_functions);
    Ok(())
}

pub(crate) fn get_expression_type(
    expr: &Expression,
    var_types: &HashMap<String, TypeRef>,
    fns: &HashMap<String, FunctionSignature>,
    type_definitions: &HashMap<String, TypeDef>,
) -> anyhow::Result<TypeRef> {
    fn normalize_numeric_alias(ty: &str) -> &str {
        if ty == "Int" {
            "I32"
        } else {
            ty
        }
    }

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
                let enum_def = match type_definitions.get(struct_variable) {
                    Some(TypeDef::Enum(enum_def)) => enum_def,
                    _ => {
                        return Err(anyhow::anyhow!(
                            "unsupported call target {:?}",
                            callee.as_ref()
                        ));
                    }
                };
                let variant = enum_def
                    .variants
                    .iter()
                    .find(|v| v.name == *field)
                    .ok_or_else(|| {
                        anyhow::anyhow!("variant {} not found in enum {}", field, struct_variable)
                    })?;
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
                let arg_ty = get_expression_type(&args[0], var_types, fns, type_definitions)?;
                if &arg_ty != payload_ty {
                    return Err(anyhow::anyhow!(
                        "mismatched payload type for {}.{}: expected {}, got {}",
                        struct_variable,
                        field,
                        payload_ty,
                        arg_ty
                    ));
                }
                Ok(enum_def.name.clone())
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
        Expression::Literal(Literal::String(_)) => Ok("String".to_string()),
        Expression::Literal(Literal::Bool(_)) => Ok("Bool".to_string()),
        Expression::Variable(name) => var_types
            .get(name)
            .ok_or_else(|| anyhow::anyhow!("unknown variable {}", name))
            .map(|ty| ty.clone()),
        Expression::Call(function, arguments) => {
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
                let compatible = param_type == &arg_type
                    // C interop convenience: permit String where pointer-sized I64 is expected.
                    || (param_type == "I64" && arg_type == "String");
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
                    if left_norm == "I32" && right_norm == "I32" {
                        Ok("I32".to_string())
                    } else if left_norm == "I64" && right_norm == "I64" {
                        Ok("I64".to_string())
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
                    if (left_norm == "I32" && right_norm == "I32")
                        || (left_norm == "I64" && right_norm == "I64")
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
