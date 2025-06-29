//! Type-checking and IR generation.

use std::collections::HashMap;

use serde::Serialize;
use tracing::trace;

use crate::{
    builtins::{libc_type_signatures, BuiltInType},
    parser::{self, Ast, Expression, Literal},
};

#[derive(Clone, Debug, Serialize)]
pub struct ResolvedProgram {
    pub ast: Ast,
    pub type_definitions: HashMap<String, Type>,
    pub function_sigs: HashMap<String, FunctionSignature>,
    pub function_definitions: HashMap<String, FunctionDefinition>,
}

impl ResolvedProgram {
    fn type_check(&self, func_def: &FunctionDefinition) -> anyhow::Result<()> {
        let mut var_types: HashMap<String, Type> = HashMap::new();
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
        var_types: &mut HashMap<String, Type>,
        return_type: &mut Option<Type>,
    ) -> anyhow::Result<()> {
        match statement {
            parser::Statement::Conditional { condition, body } => {
                let condition_type =
                    get_expression_type(condition, var_types, &self.function_sigs)?;
                if condition_type != Type::BuiltIn(BuiltInType::Int) {
                    return Err(anyhow::anyhow!(
                        "expected condition to be of type int, but got {:?}",
                        condition_type
                    ));
                }
                for statement in body {
                    self.type_check_statement(statement, var_types, return_type)?;
                }
            }
            parser::Statement::While { condition, body } => {
                let condition_type =
                    get_expression_type(condition, var_types, &self.function_sigs)?;
                if condition_type != Type::BuiltIn(BuiltInType::Int) {
                    return Err(anyhow::anyhow!(
                        "expected condition to be of type int, but got {:?}",
                        condition_type
                    ));
                }
                for statement in body {
                    self.type_check_statement(statement, var_types, return_type)?;
                }
            }
            parser::Statement::Assign { variable, value } => {
                let variable_type = get_expression_type(value, &var_types, &self.function_sigs)?;
                var_types.insert(variable.clone(), variable_type);
            }
            parser::Statement::Return { expr } => {
                let expr_type = get_expression_type(expr, &var_types, &self.function_sigs)?;
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
    pub ty: Type,
}

#[derive(Clone, Debug, Serialize)]
pub struct FunctionSignature {
    pub parameters: Vec<FunctionParameter>,
    pub return_type: Type,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub enum Type {
    BuiltIn(BuiltInType),
    Struct(String),
}

#[derive(Clone, Debug, Serialize)]
pub struct FunctionDefinition {
    pub name: String,
    pub body: Vec<parser::Statement>,
    pub sig: FunctionSignature,
}

#[tracing::instrument(level = "trace", skip_all)]
pub fn resolve(ast: Ast) -> anyhow::Result<ResolvedProgram> {
    let mut program = ResolvedProgram {
        ast: ast.clone(),
        function_definitions: HashMap::new(),
        function_sigs: HashMap::new(),
        type_definitions: HashMap::new(),
    };

    program
        .type_definitions
        .insert("I32".to_string(), Type::BuiltIn(BuiltInType::Int));
    program
        .type_definitions
        .insert("I64".to_string(), Type::BuiltIn(BuiltInType::I64));
    program
        .type_definitions
        .insert("String".to_string(), Type::BuiltIn(BuiltInType::String));

    // Built-in functions

    for signature in libc_type_signatures() {
        program.function_sigs.insert(
            format!("c_{}", signature.name),
            FunctionSignature {
                parameters: signature
                    .params
                    .iter()
                    .map(|param| FunctionParameter {
                        name: param.name.clone(),
                        ty: Type::BuiltIn(param.r#type.clone()),
                    })
                    .collect(),
                return_type: Type::BuiltIn(signature.return_type.clone()),
            },
        );
    }

    program.function_sigs.insert(
        "sub".to_string(),
        FunctionSignature {
            parameters: vec![
                FunctionParameter {
                    name: "a".to_string(),
                    ty: Type::BuiltIn(BuiltInType::Int),
                },
                FunctionParameter {
                    name: "b".to_string(),
                    ty: Type::BuiltIn(BuiltInType::Int),
                },
            ],
            return_type: Type::BuiltIn(BuiltInType::Int),
        },
    );

    program.function_sigs.insert(
        "eq".to_string(),
        FunctionSignature {
            parameters: vec![
                FunctionParameter {
                    name: "a".to_string(),
                    ty: Type::BuiltIn(BuiltInType::Int),
                },
                FunctionParameter {
                    name: "b".to_string(),
                    ty: Type::BuiltIn(BuiltInType::Int),
                },
            ],
            return_type: Type::BuiltIn(BuiltInType::Int),
        },
    );

    program.function_sigs.insert(
        "sum".to_string(),
        FunctionSignature {
            parameters: vec![
                FunctionParameter {
                    name: "a".to_string(),
                    ty: Type::BuiltIn(BuiltInType::Int),
                },
                FunctionParameter {
                    name: "b".to_string(),
                    ty: Type::BuiltIn(BuiltInType::Int),
                },
            ],
            return_type: Type::BuiltIn(BuiltInType::Int),
        },
    );

    program.function_sigs.insert(
        "lt".to_string(),
        FunctionSignature {
            parameters: vec![
                FunctionParameter {
                    name: "a".to_string(),
                    ty: Type::BuiltIn(BuiltInType::Int),
                },
                FunctionParameter {
                    name: "b".to_string(),
                    ty: Type::BuiltIn(BuiltInType::Int),
                },
            ],
            return_type: Type::BuiltIn(BuiltInType::Int),
        },
    );

    program.function_sigs.insert(
        "print".to_string(),
        FunctionSignature {
            parameters: vec![FunctionParameter {
                name: "a".to_string(),
                ty: Type::BuiltIn(BuiltInType::Int),
            }],
            return_type: Type::BuiltIn(BuiltInType::Int),
        },
    );

    program.function_sigs.insert(
        "print_str".to_string(),
        FunctionSignature {
            parameters: vec![FunctionParameter {
                name: "a".to_string(),
                ty: Type::BuiltIn(BuiltInType::String),
            }],
            return_type: Type::BuiltIn(BuiltInType::Int),
        },
    );

    for function in ast.top_level_functions {
        let mut parameters = Vec::new();
        for parameter in function.parameters {
            parameters.push(parameter);
        }
        let mut func_def = FunctionDefinition {
            name: function.name.clone(),
            sig: FunctionSignature {
                parameters: parameters
                    .clone()
                    .into_iter()
                    .map(|p| {
                        let ty = program.type_definitions.get(&p.ty).unwrap().clone();
                        Ok(FunctionParameter { name: p.name, ty })
                    })
                    .collect::<anyhow::Result<Vec<_>>>()?,
                return_type: program
                    .type_definitions
                    .get(&function.return_type)
                    .unwrap()
                    .clone(),
            },
            body: function.body.clone(),
        };

        program
            .function_sigs
            .insert(function.name.clone(), func_def.sig.clone());
        program
            .function_definitions
            .insert(function.name.clone(), func_def.clone());

        program.type_check(&mut func_def)?;
    }

    if !program.function_definitions.contains_key("main") {
        Err(anyhow::anyhow!("main function not defined"))
    } else {
        Ok(program)
    }
}

fn get_expression_type(
    expr: &Expression,
    var_types: &HashMap<String, Type>,
    fns: &HashMap<String, FunctionSignature>,
) -> anyhow::Result<Type> {
    match expr {
        Expression::Literal(Literal::Int(_)) => Ok(Type::BuiltIn(BuiltInType::Int)),
        Expression::Literal(Literal::String(_)) => Ok(Type::BuiltIn(BuiltInType::String)),
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
                let arg_type = get_expression_type(arg, &var_types, fns)?;
                if param_type != &arg_type {
                    return Err(anyhow::anyhow!(
                        "mismatched types: expected {:?}, but got {:?}",
                        param_type,
                        arg_type
                    ));
                }
            }
            Ok(func.return_type.clone())
        }
        Expression::BinOp(op, left, right) => {
            let left_type = get_expression_type(left, var_types, fns)?;
            let right_type = get_expression_type(right, var_types, fns)?;

            if left_type != Type::BuiltIn(BuiltInType::Int)
                || right_type != Type::BuiltIn(BuiltInType::Int)
            {
                return Err(anyhow::anyhow!(
                    "expected both operands of {:?} to be of type int, but got {:?} and {:?}",
                    op,
                    left_type,
                    right_type
                ));
            }

            Ok(Type::BuiltIn(BuiltInType::Int))
        }
    }
}
