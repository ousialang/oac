use serde::Serialize;
use tracing::trace;

use crate::tokenizer::{TokenData, TokenList};

#[derive(Clone, Debug, Serialize)]
pub struct Ast {
    pub top_level_functions: Vec<Function>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Function {
    pub name: String,
    pub parameters: Vec<Parameter>,
    pub body: Vec<Statement>,
    pub return_type: String,
}

#[derive(Clone, Debug, Serialize)]
pub enum Statement {
    Assign {
        variable: String,
        value: Expression,
    },
    Return {
        expr: Expression,
    },
    Expression {
        expr: Expression,
    },
    While {
        condition: Expression,
        body: Vec<Statement>,
    },
}

#[derive(Clone, Debug, Serialize)]
pub enum Expression {
    Literal(Literal),
    Variable(String),
    Call(String, Vec<Expression>),
}

#[derive(Clone, Debug, Serialize)]
pub enum Literal {
    Int(u32),
    String(String),
}

#[derive(Clone, Debug, Serialize)]
pub struct Parameter {
    pub name: String,
    pub ty: String,
}

fn parse_statement(tokens: &mut Vec<TokenData>) -> anyhow::Result<Statement> {
    trace!(?tokens, "Parsing statement");

    match tokens.first() {
        Some(TokenData::Word(name)) => {
            let name = name.clone();

            if name == "return" {
                tokens.remove(0);
                let expr = parse_expression(tokens)?;
                return Ok(Statement::Return { expr });
            } else if name == "while" {
                tokens.remove(0);
                let condition = parse_expression(tokens)?;
                anyhow::ensure!(
                    tokens.remove(0)
                        == TokenData::Parenthesis {
                            opening: '{',
                            is_opening: true
                        },
                    "expected opening brace"
                );
                let mut body = vec![];
                loop {
                    match tokens.first().unwrap() {
                        TokenData::Parenthesis {
                            opening: '}',
                            is_opening: false,
                        } => {
                            tokens.remove(0);
                            break;
                        }
                        TokenData::Newline => {
                            tokens.remove(0);
                        }
                        _ => {
                            let statement = parse_statement(tokens)?;
                            body.push(statement);
                        }
                    }
                }
                return Ok(Statement::While {
                    condition,
                    body: body,
                });
            } else if tokens.get(1) == Some(&TokenData::Symbols("=".to_string())) {
                tokens.remove(0);
                tokens.remove(0);
                trace!("Parsing assignment statement");
                let value = parse_expression(tokens)?;
                return Ok(Statement::Assign {
                    variable: name,
                    value,
                });
            } else {
                let expr = parse_expression(tokens)?;
                return Ok(Statement::Expression { expr });
            }
        }
        token => return Err(anyhow::anyhow!("expected statement instead of {:?}", token)),
    }
}

fn parse_function_args(tokens: &mut Vec<TokenData>) -> anyhow::Result<Vec<Parameter>> {
    let mut parameters = vec![];
    loop {
        match tokens.first().unwrap() {
            TokenData::Symbols(s) => {
                if s == "," {
                    tokens.remove(0);
                    continue;
                } else {
                    return Err(anyhow::anyhow!("expected ',', parameter name, or ')'"));
                }
            }
            TokenData::Parenthesis {
                opening: ')',
                is_opening: false,
            } => {
                tokens.remove(0);
                break;
            }
            TokenData::Word(name) => {
                let name = name.clone();
                tokens.remove(0);
                anyhow::ensure!(
                    tokens.remove(0) == TokenData::Symbols(":".to_string()),
                    "expected ':' after parameter name"
                );
                let ty = match tokens.remove(0) {
                    TokenData::Word(ty) => ty,
                    _ => return Err(anyhow::anyhow!("expected parameter type")),
                };

                parameters.push(Parameter { name, ty });
            }
            _ => return Err(anyhow::anyhow!("expected parameter name")),
        }
    }

    Ok(parameters)
}

fn parse_function_declaration(tokens: &mut Vec<TokenData>) -> anyhow::Result<Function> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("fun".to_string()),
        "expected 'fun' keyword"
    );

    let name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        _ => return Err(anyhow::anyhow!("expected function name")),
    };

    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '(',
                is_opening: true
            },
        "expected opening parenthesis"
    );

    let parameters = parse_function_args(tokens)?;

    // parse -> return type
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Symbols("->".to_string()),
        "expected '->' after function parameters"
    );

    let return_type = match tokens.remove(0) {
        TokenData::Word(name) => name,
        _ => return Err(anyhow::anyhow!("expected return type")),
    };

    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '{',
                is_opening: true
            },
        "expected opening brace"
    );

    anyhow::ensure!(
        tokens.remove(0) == TokenData::Newline,
        "expected newline after opening brace"
    );

    let mut body = vec![];
    loop {
        trace!(
            "Parsing entry in a function body: {:#?}",
            tokens.first().unwrap()
        );
        match tokens.first().unwrap() {
            TokenData::Parenthesis {
                opening: '}',
                is_opening: false,
            } => {
                tokens.remove(0);
                break;
            }
            TokenData::Newline => {
                tokens.remove(0);
            }
            _ => {
                let statement = parse_statement(tokens)?;
                body.push(statement);
            }
        }
    }

    Ok(Function {
        name,
        parameters,
        body,
        return_type,
    })
}

#[tracing::instrument(level = "trace", skip(tokens))]
pub fn parse(mut tokens: TokenList) -> anyhow::Result<Ast> {
    // Discard all comments.
    tokens
        .tokens
        .retain(|token| !matches!(token, TokenData::Comment(_)));

    let mut ast = Ast {
        top_level_functions: vec![],
    };

    while let Some(token) = tokens.tokens.first() {
        match token {
            TokenData::Word(name) if name == "fun" => {
                let function = parse_function_declaration(&mut tokens.tokens)?;
                ast.top_level_functions.push(function);
            }
            TokenData::Newline => {
                tokens.tokens.remove(0);
            }
            _ => return Err(anyhow::anyhow!("unexpected token {:?}", token)),
        }
    }

    Ok(ast)
}

fn parse_expression(tokens: &mut Vec<TokenData>) -> anyhow::Result<Expression> {
    trace!(?tokens, "Parsing expression");

    // Parse literal, variable, or function call
    let first_token = tokens.remove(0);
    match (first_token, tokens.first()) {
        (
            TokenData::Parenthesis {
                opening: '(',
                is_opening: true,
            },
            _,
        ) => {
            tokens.remove(0);
            trace!(?tokens, "Parsing parenthesized expression");
            let expr = parse_expression(tokens)?;
            anyhow::ensure!(
                tokens.remove(0)
                    == TokenData::Parenthesis {
                        opening: ')',
                        is_opening: false
                    },
                "Expected closing parenthesis"
            );
            Ok(expr)
        }
        (
            TokenData::Word(name),
            Some(TokenData::Parenthesis {
                opening: '(',
                is_opening: true,
            }),
        ) => {
            tokens.remove(0);
            let mut args = vec![];
            loop {
                match tokens.get(0) {
                    Some(TokenData::Parenthesis {
                        opening: ')',
                        is_opening: false,
                    }) => {
                        tokens.remove(0);
                        break;
                    }
                    _ => {
                        trace!(?tokens, "Parsing function argument");
                        let expr = parse_expression(tokens)?;
                        args.push(expr);
                        // TODO: comma and more args
                    }
                }
            }
            Ok(Expression::Call(name, args))
        }
        (TokenData::Word(name), _) => Ok(Expression::Variable(name)),
        (TokenData::String(s), _) => Ok(Expression::Literal(Literal::String(s))),
        (TokenData::Number(value), _) => Ok(Expression::Literal(Literal::Int(value))),
        (token, _) => Err(anyhow::anyhow!("unexpected token {:?}", token)),
    }
}
