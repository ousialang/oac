//! Type-checking and IR generation.

use std::collections::HashMap;

use tracing::trace;

use crate::parser::{self, Ast, Expression, Literal, Type};

#[derive(Clone, Debug)]
pub struct ResolvedProgram {
    pub ast: Ast,
    pub function_definitions: HashMap<String, FunctionDefinition>,
}

impl ResolvedProgram {
    fn type_check(&self, func_def: &mut FunctionDefinition) -> anyhow::Result<()> {
        let mut var_types: HashMap<String, parser::Type> = HashMap::new();
        let mut return_type = None;
        for statement in &func_def.body {
            match statement {
                parser::Statement::Assign { variable, value } => {
                    let variable_type =
                        get_expression_type(value, &var_types, &self.function_definitions)?;
                    var_types.insert(variable.clone(), variable_type);
                }
                parser::Statement::Return { expr } => {
                    let expr_type =
                        get_expression_type(expr, &var_types, &self.function_definitions)?;
                    if return_type == None || return_type == Some(expr_type.clone()) {
                        return_type = Some(expr_type);
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
        }
        func_def.return_type = return_type.expect("return type not set");

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct FunctionDefinition {
    pub name: String,
    pub parameters: Vec<parser::Parameter>,
    pub body: Vec<parser::Statement>,
    pub return_type: parser::Type,
}

pub fn resolve(ast: Ast) -> anyhow::Result<ResolvedProgram> {
    let mut program = ResolvedProgram {
        ast: ast.clone(),
        function_definitions: HashMap::new(),
    };

    for function in ast.top_level_functions {
        let mut parameters = Vec::new();
        for parameter in function.parameters {
            parameters.push(parameter);
        }
        let mut func_def = FunctionDefinition {
            name: function.name.clone(),
            parameters: parameters.clone(),
            body: function.body.clone(),
            return_type: Type::Int,
        };
        program.type_check(&mut func_def)?;
        program
            .function_definitions
            .insert(function.name.clone(), func_def);
    }

    Ok(program)
}

fn get_expression_type(
    expr: &Expression,
    var_types: &HashMap<String, parser::Type>,
    fns: &HashMap<String, FunctionDefinition>,
) -> anyhow::Result<parser::Type> {
    match expr {
        Expression::Literal(Literal::Int(_)) => Ok(parser::Type::Int),
        Expression::Literal(Literal::String(_)) => Ok(parser::Type::String),
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
    }
}
