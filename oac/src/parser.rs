use crate::scanner::{Token, TokenList};

#[derive(Clone, Debug)]
pub struct Ast {
    pub top_level_functions: Vec<Function>,
}

#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub parameters: Vec<Parameter>,
    pub body: Vec<Statement>,
}

#[derive(Clone, Debug)]
pub enum Statement {
    Assign { variable: String, value: Expression },
    Return(Expression),
}

#[derive(Clone, Debug)]
pub enum Expression {
    Literal(Literal),
    Variable(String),
    Call(String, Vec<Expression>),
}

#[derive(Clone, Debug)]
pub enum Literal {
    Int(u32),
    String(String),
}

#[derive(Clone, Debug)]
pub struct Parameter {
    pub name: String,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Int,
    String,
}

fn parse_statement(tokens: &mut Vec<Token>) -> anyhow::Result<Statement> {
    println!("{:?}", tokens);
    match tokens.remove(0) {
        Token::Word(name) => {
            if name == "return" {
                let value = parse_expression(tokens)?;
                return Ok(Statement::Return(value));
            } else if tokens.first() == Some(&Token::Symbols("=".to_string())) {
                tokens.remove(0);
                println!("assign");
                let value = parse_expression(tokens)?;
                return Ok(Statement::Assign {
                    variable: name,
                    value,
                });
            } else {
                return Err(anyhow::anyhow!("expected statement instead of {:?}", name));
            }
        }
        token => return Err(anyhow::anyhow!("expected statement instead of {:?}", token)),
    }
}

fn parse_function_declaration(tokens: &mut Vec<Token>) -> anyhow::Result<Function> {
    anyhow::ensure!(
        tokens.remove(0) == Token::Word("fun".to_string()),
        "expected 'fun' keyword"
    );

    let name = match tokens.remove(0) {
        Token::Word(name) => name,
        _ => return Err(anyhow::anyhow!("expected function name")),
    };

    anyhow::ensure!(
        tokens.remove(0)
            == Token::Parenthesis {
                opening: '(',
                is_opening: true
            },
        "expected opening parenthesis"
    );

    let mut parameters = vec![];
    loop {
        match tokens.first().unwrap() {
            Token::Parenthesis {
                opening: ')',
                is_opening: false,
            } => {
                tokens.remove(0);
                break;
            }
            Token::Word(name) => {
                parameters.push(Parameter {
                    name: name.clone(),
                    ty: Type::Int,
                });

                tokens.remove(0);

                if tokens.first() == Some(&Token::Symbols(",".to_string())) {
                    tokens.remove(0);
                }
            }
            _ => return Err(anyhow::anyhow!("expected parameter name")),
        }
    }

    anyhow::ensure!(
        tokens.remove(0)
            == Token::Parenthesis {
                opening: '{',
                is_opening: true
            },
        "expected opening brace"
    );

    anyhow::ensure!(
        tokens.remove(0) == Token::Newline,
        "expected newline after opening brace"
    );

    let mut body = vec![];
    loop {
        println!("parse statement: {:?}", tokens.first().unwrap());
        match tokens.first().unwrap() {
            Token::Parenthesis {
                opening: '}',
                is_opening: false,
            } => {
                tokens.remove(0);
                break;
            }
            Token::Newline => {
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
    })
}

pub fn parse(mut tokens: TokenList) -> anyhow::Result<Ast> {
    let mut ast = Ast {
        top_level_functions: vec![],
    };

    while let Some(token) = tokens.tokens.first() {
        match token {
            Token::Word(name) if name == "fun" => {
                let function = parse_function_declaration(&mut tokens.tokens)?;
                ast.top_level_functions.push(function);
            }
            Token::Newline => {
                tokens.tokens.remove(0);
            }
            _ => return Err(anyhow::anyhow!("unexpected token {:?}", token)),
        }
    }

    Ok(ast)
}

fn parse_expression(tokens: &mut Vec<Token>) -> anyhow::Result<Expression> {
    // Parse literal, variable, or function call
    let first_token = tokens.remove(0);
    match (first_token, tokens.first()) {
        (
            Token::Parenthesis {
                opening: '(',
                is_opening: true,
            },
            _,
        ) => {
            println!("parsing (expr)");
            tokens.remove(0);
            let expr = parse_expression(tokens)?;
            anyhow::ensure!(
                tokens.remove(0)
                    == Token::Parenthesis {
                        opening: ')',
                        is_opening: false
                    },
                "Expected closing parenthesis"
            );
            Ok(expr)
        }
        (
            Token::Word(name),
            Some(Token::Parenthesis {
                opening: '(',
                is_opening: true,
            }),
        ) => {
            tokens.remove(0);
            let mut args = vec![];
            loop {
                match tokens.get(0) {
                    Some(Token::Parenthesis {
                        opening: ')',
                        is_opening: false,
                    }) => {
                        tokens.remove(0);
                        break;
                    }
                    _ => {
                        let expr = parse_expression(tokens)?;
                        args.push(expr);
                        // TODO: comma and more args
                    }
                }
            }
            Ok(Expression::Call(name, args))
        }
        (Token::Word(name), _) => Ok(Expression::Variable(name)),
        (Token::String(s), _) => Ok(Expression::Literal(Literal::String(s))),
        (Token::Number(value), _) => Ok(Expression::Literal(Literal::Int(value))),
        (token, _) => Err(anyhow::anyhow!("unexpected token {:?}", token)),
    }
}
