use serde::Serialize;
use tracing::trace;

use crate::tokenizer::{TokenData, TokenList};

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct StructDef {
    pub name: String,
    pub struct_fields: Vec<StructField>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct StructField {
    pub name: String,
    pub ty: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct Ast {
    pub type_definitions: Vec<StructDef>,
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
    StructDef {
        def: StructDef,
    },
    Conditional {
        condition: Expression,
        body: Vec<Statement>,
    },
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
    BinOp(Op, Box<Expression>, Box<Expression>),
    FieldAccess(Box<Expression>, String),
    StructValue {
        struct_name: String,
        field_values: Vec<(String, Expression)>,
    },
}

#[derive(Clone, Debug, Serialize)]
pub enum Literal {
    Int(u32),
    String(String),
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq, Copy)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    Lt,
    Gt,
    Le,
    Ge,
}

impl Op {
    fn from_token(token: &TokenData) -> Option<Op> {
        match token {
            TokenData::Symbols(s) => match s.as_str() {
                "+" => Some(Op::Add),
                "-" => Some(Op::Sub),
                "*" => Some(Op::Mul),
                "/" => Some(Op::Div),
                "==" => Some(Op::Eq),
                "!=" => Some(Op::Neq),
                "<" => Some(Op::Lt),
                ">" => Some(Op::Gt),
                "<=" => Some(Op::Le),
                ">=" => Some(Op::Ge),
                _ => None,
            },
            _ => None,
        }
    }

    fn precedence(&self) -> u8 {
        match self {
            Op::Eq | Op::Neq | Op::Lt | Op::Gt | Op::Le | Op::Ge => 0,
            Op::Add | Op::Sub => 1,
            Op::Mul | Op::Div => 2,
        }
    }
}

impl TokenData {
    fn is_op(&self) -> bool {
        matches!(
            self,
            TokenData::Symbols(s) if s == "+" || s == "-" || s == "*" || s == "/" || s == "==" || s == "!=" || s == "<" || s == ">" || s == "<=" || s == ">="
        )
    }
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
                let expr = parse_expression(tokens, 0)?;
                return Ok(Statement::Return { expr });
            } else if name == "if" {
                tokens.remove(0);
                let condition = parse_expression(tokens, 0)?;
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
                return Ok(Statement::Conditional { condition, body });
            } else if name == "while" {
                tokens.remove(0);
                let condition = parse_expression(tokens, 0)?;
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
                let value = parse_expression(tokens, 0)?;
                return Ok(Statement::Assign {
                    variable: name,
                    value,
                });
            } else {
                let expr = parse_expression(tokens, 0)?;
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

fn parse_struct_declaration(tokens: &mut Vec<TokenData>) -> anyhow::Result<StructDef> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("struct".to_string()),
        "expected 'struct' keyword"
    );

    let name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        _ => return Err(anyhow::anyhow!("expected struct name")),
    };

    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '{',
                is_opening: true
            },
        "expected opening brace"
    );

    let mut struct_fields = vec![];
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
                let field_name = match tokens.remove(0) {
                    TokenData::Word(name) => name,
                    _ => return Err(anyhow::anyhow!("expected field name")),
                };
                anyhow::ensure!(
                    tokens.remove(0) == TokenData::Symbols(":".to_string()),
                    "expected ':' after field name"
                );
                let ty = match tokens.remove(0) {
                    TokenData::Word(ty) => ty,
                    _ => return Err(anyhow::anyhow!("expected field type")),
                };

                let next_tok = tokens.remove(0);
                anyhow::ensure!(
                    next_tok == TokenData::Symbols(",".to_string())
                        || next_tok == TokenData::Newline,
                    "expected ',' or newline after field type"
                );
                struct_fields.push(StructField {
                    name: field_name,
                    ty,
                });
            }
        }
    }

    Ok(StructDef {
        name,
        struct_fields,
    })
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
        type_definitions: vec![],
        top_level_functions: vec![],
    };

    while let Some(token) = tokens.tokens.first() {
        match token {
            TokenData::Word(name) if name == "struct" => {
                let type_definition = parse_struct_declaration(&mut tokens.tokens)?;
                ast.type_definitions.push(type_definition);
            }
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

fn parse_struct_value(
    tokens: &mut Vec<TokenData>,
    struct_name: String,
) -> anyhow::Result<Expression> {
    tokens.remove(0);
    assert_eq!(
        tokens.remove(0),
        TokenData::Parenthesis {
            opening: '{',
            is_opening: true,
        }
    );

    let mut fields = vec![];
    while tokens.get(0)
        != Some(&TokenData::Parenthesis {
            opening: '{',
            is_opening: false,
        })
        && tokens.get(0)
            != Some(&TokenData::Parenthesis {
                opening: '}',
                is_opening: false,
            })
    {
        trace!(?tokens, "Parsing field");
        let field_name = match tokens.remove(0) {
            TokenData::Word(name) => name,
            _ => return Err(anyhow::anyhow!("expected field name")),
        };
        assert_eq!(tokens.remove(0), TokenData::Symbols(":".to_string()));

        fields.push((field_name, parse_expression(tokens, 0)?));

        assert_eq!(tokens.remove(0), TokenData::Symbols(",".to_string()));
    }

    tokens.remove(0);

    Ok(Expression::StructValue {
        struct_name,
        field_values: fields,
    })
}

fn parse_atom(tokens: &mut Vec<TokenData>) -> anyhow::Result<Expression> {
    let next = tokens.remove(0);
    match next {
        TokenData::Number(n) => Ok(Expression::Literal(Literal::Int(n))),
        TokenData::String(s) => Ok(Expression::Literal(Literal::String(s))),
        TokenData::Word(s) => {
            if tokens.get(0) == Some(&TokenData::Word("struct".to_string())) {
                parse_struct_value(tokens, s)
            } else if tokens.get(0)
                == Some(&TokenData::Parenthesis {
                    opening: '(',
                    is_opening: true,
                })
            {
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
                        None => return Err(anyhow::anyhow!("unexpected end of file")),
                        _ => {
                            let expr = parse_expression(tokens, 0)?;
                            args.push(expr);
                            if let Some(TokenData::Symbols(s)) = tokens.get(0) {
                                if s == "," {
                                    tokens.remove(0);
                                    continue;
                                }
                            }
                        }
                    }
                }
                Ok(Expression::Call(s, args))
            } else {
                Ok(Expression::Variable(s))
            }
        }
        TokenData::Parenthesis {
            opening: '(',
            is_opening: true,
        } => {
            let expr = parse_expression(tokens, 0)?;
            anyhow::ensure!(
                tokens.remove(0)
                    == TokenData::Parenthesis {
                        opening: ')',
                        is_opening: false
                    }
            );
            Ok(expr)
        }
        t => Err(anyhow::anyhow!("expected a value, got {:?}", t)),
    }
}

fn parse_expression(tokens: &mut Vec<TokenData>, min_precedence: u8) -> anyhow::Result<Expression> {
    trace!(?tokens, "Parsing expression");

    let mut lhs = parse_atom(tokens)?;

    loop {
        match tokens.get(0) {
            Some(TokenData::Symbols(s)) if s == "." => {
                tokens.remove(0); // Consume '.'
                let field_name = expect_identifier(tokens.remove(0))?;
                lhs = Expression::FieldAccess(Box::new(lhs), field_name);
                continue;
            }
            Some(token) if token.is_op() => {
                let op = Op::from_token(token).unwrap();
                let precedence = op.precedence();
                if precedence >= min_precedence {
                    tokens.remove(0);
                    let rhs = parse_expression(tokens, precedence)?;
                    lhs = Expression::BinOp(op, Box::new(lhs), Box::new(rhs));
                } else {
                    break;
                }
            }
            _ => break,
        }
    }

    Ok(lhs)
}

fn expect_identifier(token: TokenData) -> anyhow::Result<String> {
    if let TokenData::Word(s) = token {
        Ok(s)
    } else {
        Err(anyhow::anyhow!("Expected identifier, found {:?}", token))
    }
}
