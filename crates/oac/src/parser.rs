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

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct EnumVariantDef {
    pub name: String,
    pub payload_ty: Option<String>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct EnumDef {
    pub name: String,
    pub variants: Vec<EnumVariantDef>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub enum TypeDefDecl {
    Struct(StructDef),
    Enum(EnumDef),
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct GenericParam {
    pub name: String,
    pub bounds: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct GenericDef {
    pub name: String,
    pub params: Vec<GenericParam>,
    pub type_definitions: Vec<TypeDefDecl>,
    pub top_level_functions: Vec<Function>,
    pub invariants: Vec<StructInvariantDecl>,
}

#[derive(Clone, Debug, Serialize)]
pub struct GenericSpecialization {
    pub alias: String,
    pub generic_name: String,
    pub concrete_types: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct TraitMethodSig {
    pub name: String,
    pub parameters: Vec<Parameter>,
    pub return_type: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct TraitDecl {
    pub name: String,
    pub methods: Vec<TraitMethodSig>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ImplDecl {
    pub trait_name: String,
    pub for_type: String,
    pub methods: Vec<Function>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ImportDecl {
    pub path: String,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ComptimeApply {
    pub function_name: String,
    pub argument_type: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct TestDecl {
    pub name: String,
    pub body: Vec<Statement>,
}

pub const NAMESPACE_FUNCTION_SEPARATOR: &str = "__";

pub fn qualify_namespace_function_name(namespace: &str, function_name: &str) -> String {
    format!("{namespace}{NAMESPACE_FUNCTION_SEPARATOR}{function_name}")
}

#[derive(Clone, Debug, Serialize, Default)]
pub struct Ast {
    pub imports: Vec<ImportDecl>,
    pub type_definitions: Vec<TypeDefDecl>,
    pub top_level_functions: Vec<Function>,
    pub trait_declarations: Vec<TraitDecl>,
    pub impl_declarations: Vec<ImplDecl>,
    pub tests: Vec<TestDecl>,
    pub invariants: Vec<StructInvariantDecl>,
    pub generic_definitions: Vec<GenericDef>,
    pub generic_specializations: Vec<GenericSpecialization>,
    pub comptime_applies: Vec<ComptimeApply>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Function {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub extern_symbol_name: Option<String>,
    pub parameters: Vec<Parameter>,
    pub body: Vec<Statement>,
    pub return_type: String,
    pub is_comptime: bool,
    pub is_extern: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct StructInvariantDecl {
    pub identifier: Option<String>,
    pub display_name: String,
    pub parameter: Parameter,
    pub body: Vec<Statement>,
}

#[derive(Clone, Debug, Serialize)]
pub enum Statement {
    #[allow(dead_code)]
    StructDef {
        def: StructDef,
    },
    Match {
        subject: Expression,
        arms: Vec<MatchArm>,
    },
    Conditional {
        condition: Expression,
        body: Vec<Statement>,
        else_body: Option<Vec<Statement>>,
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
    Prove {
        condition: Expression,
    },
    Assert {
        condition: Expression,
    },
    While {
        condition: Expression,
        body: Vec<Statement>,
    },
}

#[derive(Clone, Debug, Serialize)]
pub enum MatchPattern {
    Variant {
        type_name: String,
        variant_name: String,
        binder: Option<String>,
    },
}

#[derive(Clone, Debug, Serialize)]
pub struct MatchArm {
    pub pattern: MatchPattern,
    pub body: Vec<Statement>,
}

#[derive(Clone, Debug, Serialize)]
pub struct MatchExprArm {
    pub pattern: MatchPattern,
    pub value: Expression,
}

#[derive(Clone, Debug, Serialize)]
pub enum Expression {
    Match {
        subject: Box<Expression>,
        arms: Vec<MatchExprArm>,
    },
    Literal(Literal),
    Variable(String),
    Call(String, Vec<Expression>),
    PostfixCall {
        callee: Box<Expression>,
        args: Vec<Expression>,
    },
    BinOp(Op, Box<Expression>, Box<Expression>),
    UnaryOp(UnaryOp, Box<Expression>),
    FieldAccess {
        struct_variable: String,
        field: String,
    },
    StructValue {
        struct_name: String,
        field_values: Vec<(String, Expression)>,
    },
}

#[derive(Clone, Debug, Serialize)]
pub enum Literal {
    Int(u32),
    Float32(String),
    Float64(String),
    String(String),
    Bool(bool),
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq, Copy)]
pub enum Op {
    And,
    Or,
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

#[derive(Clone, Debug, Serialize, PartialEq, Eq, Copy)]
pub enum UnaryOp {
    Not,
}

impl Op {
    fn from_token(token: &TokenData) -> Option<Op> {
        match token {
            TokenData::Symbols(s) => match s.as_str() {
                "&&" => Some(Op::And),
                "||" => Some(Op::Or),
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
            Op::Or => 0,
            Op::And => 1,
            Op::Eq | Op::Neq | Op::Lt | Op::Gt | Op::Le | Op::Ge => 2,
            Op::Add | Op::Sub => 3,
            Op::Mul | Op::Div => 4,
        }
    }
}

impl TokenData {
    fn is_op(&self) -> bool {
        matches!(
            self,
            TokenData::Symbols(s)
                if s == "+"
                    || s == "-"
                    || s == "*"
                    || s == "/"
                    || s == "=="
                    || s == "!="
                    || s == "<"
                    || s == ">"
                    || s == "<="
                    || s == ">="
                    || s == "&&"
                    || s == "||"
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
            } else if name == "comptime" {
                return Err(anyhow::anyhow!(
                    "`comptime` declarations are only allowed at top level"
                ));
            } else if (name == "prove" || name == "assert")
                && tokens.get(1)
                    == Some(&TokenData::Parenthesis {
                        opening: '(',
                        is_opening: true,
                    })
            {
                return parse_builtin_assertion_statement(tokens);
            } else if name == "match" {
                tokens.remove(0);
                return parse_match_statement(tokens);
            } else if name == "if" {
                tokens.remove(0);
                let condition = parse_expression(tokens, 0)?;
                let body = parse_braced_block(tokens)?;
                let else_body = parse_optional_else(tokens)?;
                return Ok(Statement::Conditional {
                    condition,
                    body,
                    else_body,
                });
            } else if name == "while" {
                tokens.remove(0);
                let condition = parse_expression(tokens, 0)?;
                let body = parse_braced_block(tokens)?;
                return Ok(Statement::While { condition, body });
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

fn parse_builtin_assertion_statement(tokens: &mut Vec<TokenData>) -> anyhow::Result<Statement> {
    let keyword = match tokens.remove(0) {
        TokenData::Word(name) if name == "prove" || name == "assert" => name,
        other => {
            return Err(anyhow::anyhow!(
                "expected builtin assertion keyword, got {:?}",
                other
            ))
        }
    };

    let args = parse_call_args(tokens)?;
    if args.len() != 1 {
        return Err(anyhow::anyhow!(
            "{} expects exactly one Bool argument, got {}",
            keyword,
            args.len()
        ));
    }
    let condition = args.into_iter().next().expect("single argument exists");
    if keyword == "prove" {
        Ok(Statement::Prove { condition })
    } else {
        Ok(Statement::Assert { condition })
    }
}

fn parse_braced_block(tokens: &mut Vec<TokenData>) -> anyhow::Result<Vec<Statement>> {
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
        match tokens.first() {
            Some(TokenData::Parenthesis {
                opening: '}',
                is_opening: false,
            }) => {
                tokens.remove(0);
                break;
            }
            Some(TokenData::Newline) => {
                tokens.remove(0);
            }
            Some(_) => {
                let statement = parse_statement(tokens)?;
                body.push(statement);
            }
            None => return Err(anyhow::anyhow!("unexpected end of file in braced block")),
        }
    }
    Ok(body)
}

fn parse_call_args(tokens: &mut Vec<TokenData>) -> anyhow::Result<Vec<Expression>> {
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '(',
                is_opening: true
            },
        "expected opening parenthesis for call"
    );

    let mut args = vec![];
    loop {
        match tokens.get(0) {
            Some(TokenData::Newline) => {
                tokens.remove(0);
            }
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
                match tokens.get(0) {
                    Some(TokenData::Symbols(s)) if s == "," => {
                        tokens.remove(0);
                        while tokens.get(0) == Some(&TokenData::Newline) {
                            tokens.remove(0);
                        }
                    }
                    Some(TokenData::Parenthesis {
                        opening: ')',
                        is_opening: false,
                    }) => {}
                    Some(TokenData::Newline) => {
                        while tokens.get(0) == Some(&TokenData::Newline) {
                            tokens.remove(0);
                        }
                        anyhow::ensure!(
                            tokens.get(0)
                                == Some(&TokenData::Parenthesis {
                                    opening: ')',
                                    is_opening: false
                                }),
                            "expected ')' after function call argument"
                        );
                    }
                    Some(tok) => {
                        return Err(anyhow::anyhow!(
                            "expected ',' or ')' after function call argument, got {:?}",
                            tok
                        ));
                    }
                    None => return Err(anyhow::anyhow!("unexpected end of file")),
                }
            }
        }
    }

    Ok(args)
}

fn parse_match_pattern(tokens: &mut Vec<TokenData>) -> anyhow::Result<MatchPattern> {
    let type_name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        tok => {
            return Err(anyhow::anyhow!(
                "expected enum type in match pattern, got {:?}",
                tok
            ));
        }
    };
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Symbols(".".to_string()),
        "expected '.' in match pattern"
    );
    let variant_name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        tok => {
            return Err(anyhow::anyhow!(
                "expected variant name in match pattern, got {:?}",
                tok
            ));
        }
    };

    let binder = if tokens.get(0)
        == Some(&TokenData::Parenthesis {
            opening: '(',
            is_opening: true,
        }) {
        tokens.remove(0);
        let binder = match tokens.remove(0) {
            TokenData::Word(name) => name,
            tok => {
                return Err(anyhow::anyhow!(
                    "expected binder name in payload pattern, got {:?}",
                    tok
                ));
            }
        };
        anyhow::ensure!(
            tokens.remove(0)
                == TokenData::Parenthesis {
                    opening: ')',
                    is_opening: false
                },
            "expected ')' in payload pattern"
        );
        Some(binder)
    } else {
        None
    };

    Ok(MatchPattern::Variant {
        type_name,
        variant_name,
        binder,
    })
}

fn parse_match_statement(tokens: &mut Vec<TokenData>) -> anyhow::Result<Statement> {
    let subject = parse_expression(tokens, 0)?;
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '{',
                is_opening: true
            },
        "expected opening brace after match subject"
    );

    let mut arms = vec![];
    loop {
        while tokens.first() == Some(&TokenData::Newline) {
            tokens.remove(0);
        }

        match tokens.first() {
            Some(TokenData::Parenthesis {
                opening: '}',
                is_opening: false,
            }) => {
                tokens.remove(0);
                break;
            }
            Some(_) => {
                let pattern = parse_match_pattern(tokens)?;
                anyhow::ensure!(
                    tokens.remove(0) == TokenData::Symbols("=>".to_string()),
                    "expected '=>' after match pattern"
                );
                let body = parse_braced_block(tokens)?;
                arms.push(MatchArm { pattern, body });
            }
            None => return Err(anyhow::anyhow!("unexpected end of file in match")),
        }
    }

    Ok(Statement::Match { subject, arms })
}

fn parse_match_expression(tokens: &mut Vec<TokenData>) -> anyhow::Result<Expression> {
    let subject = parse_expression(tokens, 0)?;
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '{',
                is_opening: true
            },
        "expected opening brace after match subject"
    );

    let mut arms = vec![];
    loop {
        while tokens.first() == Some(&TokenData::Newline) {
            tokens.remove(0);
        }

        match tokens.first() {
            Some(TokenData::Parenthesis {
                opening: '}',
                is_opening: false,
            }) => {
                tokens.remove(0);
                break;
            }
            Some(_) => {
                let pattern = parse_match_pattern(tokens)?;
                anyhow::ensure!(
                    tokens.remove(0) == TokenData::Symbols("=>".to_string()),
                    "expected '=>' after match pattern"
                );
                let value = parse_expression(tokens, 0)?;
                arms.push(MatchExprArm { pattern, value });

                while tokens.first() == Some(&TokenData::Newline) {
                    tokens.remove(0);
                }
                if tokens.first() == Some(&TokenData::Symbols(",".to_string())) {
                    tokens.remove(0);
                }
            }
            None => {
                return Err(anyhow::anyhow!(
                    "unexpected end of file in match expression"
                ))
            }
        }
    }

    anyhow::ensure!(
        !arms.is_empty(),
        "match expression must have at least one arm"
    );
    Ok(Expression::Match {
        subject: Box::new(subject),
        arms,
    })
}

fn parse_optional_else(tokens: &mut Vec<TokenData>) -> anyhow::Result<Option<Vec<Statement>>> {
    while tokens.first() == Some(&TokenData::Newline) {
        tokens.remove(0);
    }

    if tokens.first() != Some(&TokenData::Word("else".to_string())) {
        return Ok(None);
    }
    tokens.remove(0);

    if tokens.first() == Some(&TokenData::Word("if".to_string())) {
        tokens.remove(0);
        let condition = parse_expression(tokens, 0)?;
        let body = parse_braced_block(tokens)?;
        let nested_else = parse_optional_else(tokens)?;
        Ok(Some(vec![Statement::Conditional {
            condition,
            body,
            else_body: nested_else,
        }]))
    } else {
        let body = parse_braced_block(tokens)?;
        Ok(Some(body))
    }
}

fn parse_function_args(tokens: &mut Vec<TokenData>) -> anyhow::Result<Vec<Parameter>> {
    let mut parameters = vec![];
    loop {
        match tokens.first() {
            Some(TokenData::Symbols(s)) => {
                if s == "," {
                    tokens.remove(0);
                    continue;
                } else {
                    return Err(anyhow::anyhow!("expected ',', parameter name, or ')'"));
                }
            }
            Some(TokenData::Parenthesis {
                opening: ')',
                is_opening: false,
            }) => {
                tokens.remove(0);
                break;
            }
            Some(TokenData::Word(name)) => {
                let name = name.clone();
                tokens.remove(0);
                anyhow::ensure!(
                    tokens.remove(0) == TokenData::Symbols(":".to_string()),
                    "expected ':' after parameter name"
                );
                let ty = parse_type_reference(tokens)?;

                parameters.push(Parameter { name, ty });
            }
            None => return Err(anyhow::anyhow!("unexpected end of file in parameter list")),
            _ => return Err(anyhow::anyhow!("expected parameter name")),
        }
    }

    Ok(parameters)
}

fn parse_single_parameter(tokens: &mut Vec<TokenData>) -> anyhow::Result<Parameter> {
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '(',
                is_opening: true
            },
        "expected opening parenthesis"
    );
    let parameter = match tokens.remove(0) {
        TokenData::Word(name) => {
            anyhow::ensure!(
                tokens.remove(0) == TokenData::Symbols(":".to_string()),
                "expected ':' after parameter name"
            );
            let ty = parse_type_reference(tokens)?;
            Parameter { name, ty }
        }
        _ => return Err(anyhow::anyhow!("expected parameter name")),
    };
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: ')',
                is_opening: false
            },
        "expected closing parenthesis"
    );
    Ok(parameter)
}

fn parse_function_like_body(tokens: &mut Vec<TokenData>) -> anyhow::Result<Vec<Statement>> {
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
            "Parsing entry in a function-like body: {:#?}",
            tokens.first()
        );
        match tokens.first() {
            Some(TokenData::Parenthesis {
                opening: '}',
                is_opening: false,
            }) => {
                tokens.remove(0);
                break;
            }
            Some(TokenData::Newline) => {
                tokens.remove(0);
            }
            Some(_) => {
                let statement = parse_statement(tokens)?;
                body.push(statement);
            }
            None => return Err(anyhow::anyhow!("unexpected end of file in function body")),
        }
    }

    Ok(body)
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
        match tokens.first() {
            Some(TokenData::Parenthesis {
                opening: '}',
                is_opening: false,
            }) => {
                tokens.remove(0);
                break;
            }
            Some(TokenData::Newline) => {
                tokens.remove(0);
            }
            Some(_) => {
                let field_name = match tokens.remove(0) {
                    TokenData::Word(name) => name,
                    _ => return Err(anyhow::anyhow!("expected field name")),
                };
                anyhow::ensure!(
                    tokens.remove(0) == TokenData::Symbols(":".to_string()),
                    "expected ':' after field name"
                );
                let ty = parse_type_reference(tokens)?;

                match tokens.first() {
                    Some(TokenData::Symbols(s)) if s == "," => {
                        tokens.remove(0);
                    }
                    Some(TokenData::Newline) => {
                        tokens.remove(0);
                    }
                    Some(TokenData::Parenthesis {
                        opening: '}',
                        is_opening: false,
                    }) => {}
                    Some(tok) => {
                        return Err(anyhow::anyhow!(
                            "expected ',', newline, or '}}' after field type, got {:?}",
                            tok
                        ));
                    }
                    None => return Err(anyhow::anyhow!("unexpected end of file in struct body")),
                }
                struct_fields.push(StructField {
                    name: field_name,
                    ty,
                });
            }
            None => {
                return Err(anyhow::anyhow!(
                    "unexpected end of file in struct declaration"
                ))
            }
        }
    }

    Ok(StructDef {
        name,
        struct_fields,
    })
}

fn parse_enum_declaration(tokens: &mut Vec<TokenData>) -> anyhow::Result<EnumDef> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("enum".to_string()),
        "expected 'enum' keyword"
    );

    let name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        _ => return Err(anyhow::anyhow!("expected enum name")),
    };

    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '{',
                is_opening: true
            },
        "expected opening brace"
    );

    let mut variants = vec![];
    loop {
        match tokens.first() {
            Some(TokenData::Parenthesis {
                opening: '}',
                is_opening: false,
            }) => {
                tokens.remove(0);
                break;
            }
            Some(TokenData::Newline) => {
                tokens.remove(0);
            }
            Some(TokenData::Symbols(s)) if s == "," => {
                tokens.remove(0);
            }
            Some(TokenData::Word(_)) => {
                let variant_name = match tokens.remove(0) {
                    TokenData::Word(name) => name,
                    _ => unreachable!(),
                };

                let payload_ty = if tokens.get(0)
                    == Some(&TokenData::Parenthesis {
                        opening: '(',
                        is_opening: true,
                    }) {
                    tokens.remove(0);
                    let ty = parse_type_reference(tokens)?;
                    anyhow::ensure!(
                        tokens.remove(0)
                            == TokenData::Parenthesis {
                                opening: ')',
                                is_opening: false
                            },
                        "expected closing ')' in variant payload"
                    );
                    Some(ty)
                } else {
                    None
                };

                variants.push(EnumVariantDef {
                    name: variant_name,
                    payload_ty,
                });
            }
            Some(tok) => return Err(anyhow::anyhow!("unexpected token in enum body: {:?}", tok)),
            None => return Err(anyhow::anyhow!("unexpected end of file in enum")),
        }
    }

    Ok(EnumDef { name, variants })
}

fn parse_function_declaration(
    tokens: &mut Vec<TokenData>,
    is_comptime: bool,
) -> anyhow::Result<Function> {
    if is_comptime {
        anyhow::ensure!(
            tokens.remove(0) == TokenData::Word("comptime".to_string()),
            "expected 'comptime' keyword"
        );
    }
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

    let return_type = parse_type_reference(tokens)?;

    let body = parse_function_like_body(tokens)?;

    Ok(Function {
        name,
        extern_symbol_name: None,
        parameters,
        body,
        return_type,
        is_comptime,
        is_extern: false,
    })
}

fn parse_extern_function_declaration(tokens: &mut Vec<TokenData>) -> anyhow::Result<Function> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("extern".to_string()),
        "expected 'extern' keyword"
    );
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("fun".to_string()),
        "expected 'fun' keyword after 'extern'"
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

    anyhow::ensure!(
        tokens.remove(0) == TokenData::Symbols("->".to_string()),
        "expected '->' after function parameters"
    );
    let return_type = parse_type_reference(tokens)?;

    Ok(Function {
        name,
        extern_symbol_name: None,
        parameters,
        body: vec![],
        return_type,
        is_comptime: false,
        is_extern: true,
    })
}

fn parse_test_declaration(tokens: &mut Vec<TokenData>) -> anyhow::Result<TestDecl> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("test".to_string()),
        "expected 'test' keyword"
    );

    let name = match tokens.remove(0) {
        TokenData::String(name) => name,
        token => {
            return Err(anyhow::anyhow!(
                "expected test name as string literal, got {:?}",
                token
            ));
        }
    };

    while tokens.first() == Some(&TokenData::Newline) {
        tokens.remove(0);
    }

    let body = parse_braced_block(tokens)?;
    Ok(TestDecl { name, body })
}

fn parse_namespace_declaration(tokens: &mut Vec<TokenData>) -> anyhow::Result<Vec<Function>> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("namespace".to_string()),
        "expected 'namespace' keyword"
    );

    let namespace = match tokens.remove(0) {
        TokenData::Word(name) => name,
        token => {
            return Err(anyhow::anyhow!(
                "expected namespace name after 'namespace', got {:?}",
                token
            ));
        }
    };

    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '{',
                is_opening: true
            },
        "expected '{{' after namespace name"
    );

    let mut functions = vec![];
    loop {
        match tokens.first() {
            Some(TokenData::Parenthesis {
                opening: '}',
                is_opening: false,
            }) => {
                tokens.remove(0);
                break;
            }
            Some(TokenData::Newline) => {
                tokens.remove(0);
            }
            Some(TokenData::Word(name)) if name == "fun" => {
                let mut function = parse_function_declaration(tokens, false)?;
                function.name = qualify_namespace_function_name(&namespace, &function.name);
                functions.push(function);
            }
            Some(TokenData::Word(name)) if name == "extern" => {
                let mut function = parse_extern_function_declaration(tokens)?;
                let symbol_name = function.name.clone();
                function.name = qualify_namespace_function_name(&namespace, &symbol_name);
                function.extern_symbol_name = Some(symbol_name);
                functions.push(function);
            }
            Some(TokenData::Word(name)) if name == "comptime" => {
                return Err(anyhow::anyhow!(
                    "namespace {} only supports `fun` and `extern fun` declarations in v1",
                    namespace
                ));
            }
            Some(token) => {
                return Err(anyhow::anyhow!(
                    "unexpected token in namespace {} body: {:?}",
                    namespace,
                    token
                ));
            }
            None => return Err(anyhow::anyhow!("unexpected end of file in namespace body")),
        }
    }

    Ok(functions)
}

fn parse_type_reference(tokens: &mut Vec<TokenData>) -> anyhow::Result<String> {
    let base = match tokens.remove(0) {
        TokenData::Word(name) => name,
        token => return Err(anyhow::anyhow!("expected type name, got {:?}", token)),
    };

    let args = if tokens.first()
        == Some(&TokenData::Parenthesis {
            opening: '[',
            is_opening: true,
        }) {
        parse_bracketed_type_argument_list(tokens)?
    } else {
        vec![]
    };

    if args.is_empty() {
        Ok(base)
    } else {
        Ok(format!("{base}[{}]", args.join(",")))
    }
}

fn parse_bracketed_type_argument_list(tokens: &mut Vec<TokenData>) -> anyhow::Result<Vec<String>> {
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '[',
                is_opening: true
            },
        "expected '[' to start type argument list"
    );

    let mut args = vec![];
    loop {
        match tokens.first() {
            Some(TokenData::Parenthesis {
                opening: ']',
                is_opening: false,
            }) => {
                tokens.remove(0);
                break;
            }
            Some(TokenData::Newline) => {
                tokens.remove(0);
            }
            Some(_) => {
                let arg = parse_type_reference(tokens)?;
                args.push(arg);
                match tokens.first() {
                    Some(TokenData::Symbols(s)) if s == "," => {
                        tokens.remove(0);
                    }
                    Some(TokenData::Parenthesis {
                        opening: ']',
                        is_opening: false,
                    }) => {}
                    Some(tok) => {
                        return Err(anyhow::anyhow!(
                            "expected ',' or ']' in type argument list, got {:?}",
                            tok
                        ));
                    }
                    None => {
                        return Err(anyhow::anyhow!(
                            "unexpected end of file in type argument list"
                        ));
                    }
                }
            }
            None => {
                return Err(anyhow::anyhow!(
                    "unexpected end of file in type argument list"
                ))
            }
        }
    }

    Ok(args)
}

fn parse_generic_params(tokens: &mut Vec<TokenData>) -> anyhow::Result<Vec<GenericParam>> {
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '[',
                is_opening: true
            },
        "expected '[' after generic name"
    );

    let mut params = vec![];
    loop {
        match tokens.first() {
            Some(TokenData::Parenthesis {
                opening: ']',
                is_opening: false,
            }) => {
                tokens.remove(0);
                break;
            }
            Some(TokenData::Newline) => {
                tokens.remove(0);
            }
            Some(TokenData::Word(_)) => {
                let name = match tokens.remove(0) {
                    TokenData::Word(name) => name,
                    _ => unreachable!(),
                };
                let mut bounds = vec![];
                if tokens.first() == Some(&TokenData::Symbols(":".to_string())) {
                    tokens.remove(0);
                    loop {
                        let bound = match tokens.remove(0) {
                            TokenData::Word(name) => name,
                            token => {
                                return Err(anyhow::anyhow!(
                                    "expected trait bound name, got {:?}",
                                    token
                                ));
                            }
                        };
                        bounds.push(bound);
                        if tokens.first() == Some(&TokenData::Symbols("+".to_string())) {
                            tokens.remove(0);
                            continue;
                        }
                        break;
                    }
                }
                params.push(GenericParam { name, bounds });
                match tokens.first() {
                    Some(TokenData::Symbols(s)) if s == "," => {
                        tokens.remove(0);
                    }
                    Some(TokenData::Parenthesis {
                        opening: ']',
                        is_opening: false,
                    }) => {}
                    Some(tok) => {
                        return Err(anyhow::anyhow!(
                            "expected ',' or ']' after generic parameter, got {:?}",
                            tok
                        ));
                    }
                    None => {
                        return Err(anyhow::anyhow!(
                            "unexpected end of file in generic parameter list"
                        ));
                    }
                }
            }
            Some(tok) => {
                return Err(anyhow::anyhow!(
                    "unexpected token in generic parameter list: {:?}",
                    tok
                ))
            }
            None => {
                return Err(anyhow::anyhow!(
                    "unexpected end of file in generic parameter list"
                ))
            }
        }
    }

    Ok(params)
}

fn parse_struct_invariant_declaration(
    tokens: &mut Vec<TokenData>,
) -> anyhow::Result<StructInvariantDecl> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("invariant".to_string()),
        "expected 'invariant' keyword"
    );

    let (identifier, display_name) = match tokens.remove(0) {
        TokenData::String(display_name) => (None, display_name),
        TokenData::Word(identifier) => {
            let display_name = match tokens.remove(0) {
                TokenData::String(display_name) => display_name,
                token => {
                    return Err(anyhow::anyhow!(
                        "expected invariant display name string after identifier, got {:?}",
                        token
                    ));
                }
            };
            (Some(identifier), display_name)
        }
        token => {
            return Err(anyhow::anyhow!(
                "expected invariant display name string or identifier, got {:?}",
                token
            ));
        }
    };

    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("for".to_string()),
        "expected 'for' after invariant name"
    );
    let parameter = parse_single_parameter(tokens)?;
    let body = parse_function_like_body(tokens)?;

    Ok(StructInvariantDecl {
        identifier,
        display_name,
        parameter,
        body,
    })
}

fn parse_comptime_apply(tokens: &mut Vec<TokenData>) -> anyhow::Result<ComptimeApply> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("comptime".to_string()),
        "expected 'comptime' keyword"
    );
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("apply".to_string()),
        "expected 'apply' keyword after 'comptime'"
    );
    let function_name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        token => {
            return Err(anyhow::anyhow!(
                "expected comptime function name after 'comptime apply', got {:?}",
                token
            ));
        }
    };
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '(',
                is_opening: true
            },
        "expected '(' after comptime apply function name"
    );
    let argument_type = parse_type_reference(tokens)?;
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: ')',
                is_opening: false
            },
        "expected ')' after comptime apply argument"
    );
    Ok(ComptimeApply {
        function_name,
        argument_type,
    })
}

#[tracing::instrument(level = "trace", skip(tokens))]
pub fn parse(mut tokens: TokenList) -> anyhow::Result<Ast> {
    // Discard all comments.
    tokens
        .tokens
        .retain(|token| !matches!(token, TokenData::Comment(_)));

    let mut ast = Ast {
        imports: vec![],
        type_definitions: vec![],
        top_level_functions: vec![],
        trait_declarations: vec![],
        impl_declarations: vec![],
        tests: vec![],
        invariants: vec![],
        generic_definitions: vec![],
        generic_specializations: vec![],
        comptime_applies: vec![],
    };

    while let Some(token) = tokens.tokens.first() {
        match token {
            TokenData::Word(name) if name == "struct" => {
                let type_definition = parse_struct_declaration(&mut tokens.tokens)?;
                ast.type_definitions
                    .push(TypeDefDecl::Struct(type_definition));
            }
            TokenData::Word(name) if name == "enum" => {
                let type_definition = parse_enum_declaration(&mut tokens.tokens)?;
                ast.type_definitions
                    .push(TypeDefDecl::Enum(type_definition));
            }
            TokenData::Word(name) if name == "fun" => {
                let function = parse_function_declaration(&mut tokens.tokens, false)?;
                ast.top_level_functions.push(function);
            }
            TokenData::Word(name) if name == "extern" => {
                let function = parse_extern_function_declaration(&mut tokens.tokens)?;
                ast.top_level_functions.push(function);
            }
            TokenData::Word(name) if name == "test" => {
                let test = parse_test_declaration(&mut tokens.tokens)?;
                ast.tests.push(test);
            }
            TokenData::Word(name) if name == "comptime" => match tokens.tokens.get(1) {
                Some(TokenData::Word(kind)) if kind == "fun" => {
                    let function = parse_function_declaration(&mut tokens.tokens, true)?;
                    ast.top_level_functions.push(function);
                }
                Some(TokenData::Word(kind)) if kind == "apply" => {
                    let apply = parse_comptime_apply(&mut tokens.tokens)?;
                    ast.comptime_applies.push(apply);
                }
                token => {
                    return Err(anyhow::anyhow!(
                        "unexpected token after 'comptime': expected 'fun' or 'apply', got {:?}",
                        token
                    ))
                }
            },
            TokenData::Word(name) if name == "invariant" => {
                let invariant = parse_struct_invariant_declaration(&mut tokens.tokens)?;
                ast.invariants.push(invariant);
            }
            TokenData::Word(name) if name == "generic" => {
                let generic = parse_generic_declaration(&mut tokens.tokens)?;
                ast.generic_definitions.push(generic);
            }
            TokenData::Word(name) if name == "namespace" => {
                let functions = parse_namespace_declaration(&mut tokens.tokens)?;
                ast.top_level_functions.extend(functions);
            }
            TokenData::Word(name) if name == "specialize" => {
                let specialization = parse_generic_specialization(&mut tokens.tokens)?;
                ast.generic_specializations.push(specialization);
            }
            TokenData::Word(name) if name == "trait" => {
                let trait_decl = parse_trait_declaration(&mut tokens.tokens)?;
                ast.trait_declarations.push(trait_decl);
            }
            TokenData::Word(name) if name == "impl" => {
                let impl_decl = parse_impl_declaration(&mut tokens.tokens)?;
                ast.impl_declarations.push(impl_decl);
            }
            TokenData::Word(name) if name == "template" => {
                return Err(anyhow::anyhow!(
                    "template syntax was removed; use `generic Name[T, ...] {{ ... }}` instead"
                ));
            }
            TokenData::Word(name) if name == "instantiate" => {
                return Err(anyhow::anyhow!(
                    "instantiate syntax was removed; use `specialize Alias = Name[T, ...]` instead"
                ));
            }
            TokenData::Word(name) if name == "import" => {
                let import = parse_import_declaration(&mut tokens.tokens)?;
                ast.imports.push(import);
            }
            TokenData::Newline => {
                tokens.tokens.remove(0);
            }
            _ => return Err(anyhow::anyhow!("unexpected token {:?}", token)),
        }
    }

    Ok(ast)
}

fn parse_import_declaration(tokens: &mut Vec<TokenData>) -> anyhow::Result<ImportDecl> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("import".to_string()),
        "expected 'import' keyword"
    );

    let path = match tokens.remove(0) {
        TokenData::String(path) => path,
        _ => return Err(anyhow::anyhow!("expected import path as string literal")),
    };

    Ok(ImportDecl { path })
}

fn parse_struct_value(
    tokens: &mut Vec<TokenData>,
    struct_name: String,
) -> anyhow::Result<Expression> {
    match tokens.first() {
        Some(TokenData::Word(keyword)) if keyword == "struct" => {
            tokens.remove(0);
        }
        Some(token) => {
            return Err(anyhow::anyhow!(
                "expected `struct` keyword after type name in struct literal, got {:?}",
                token
            ));
        }
        None => return Err(anyhow::anyhow!("unexpected end of file in struct literal")),
    }

    match tokens.first() {
        Some(TokenData::Parenthesis {
            opening: '{',
            is_opening: true,
        }) => {
            tokens.remove(0);
        }
        Some(token) => {
            return Err(anyhow::anyhow!(
                "expected opening '{{' in struct literal, got {:?}",
                token
            ));
        }
        None => return Err(anyhow::anyhow!("unexpected end of file in struct literal")),
    }

    let mut fields = vec![];
    while tokens.get(0)
        != Some(&TokenData::Parenthesis {
            opening: '}',
            is_opening: false,
        })
    {
        if tokens.get(0) == Some(&TokenData::Newline) {
            tokens.remove(0);
            continue;
        }

        trace!(?tokens, "Parsing field");
        let field_name = match tokens.remove(0) {
            TokenData::Word(name) => name,
            _ => return Err(anyhow::anyhow!("expected field name")),
        };
        anyhow::ensure!(
            tokens.remove(0) == TokenData::Symbols(":".to_string()),
            "expected ':' after struct field name"
        );

        fields.push((field_name, parse_expression(tokens, 0)?));

        match tokens.first() {
            Some(TokenData::Symbols(s)) if s == "," => {
                tokens.remove(0);
            }
            Some(TokenData::Newline) => {
                tokens.remove(0);
            }
            Some(TokenData::Parenthesis {
                opening: '}',
                is_opening: false,
            }) => {}
            Some(tok) => {
                return Err(anyhow::anyhow!(
                    "expected ',', newline, or '}}' after struct field value, got {:?}",
                    tok
                ));
            }
            None => return Err(anyhow::anyhow!("unexpected end of file in struct literal")),
        }
    }

    tokens.remove(0);

    Ok(Expression::StructValue {
        struct_name,
        field_values: fields,
    })
}

fn parse_atom(tokens: &mut Vec<TokenData>) -> anyhow::Result<Expression> {
    if tokens.is_empty() {
        return Err(anyhow::anyhow!(
            "unexpected end of file while parsing expression"
        ));
    }
    let next = tokens.remove(0);
    match next {
        TokenData::Symbols(s) if s == "!" => {
            let rhs = parse_expression(tokens, u8::MAX)?;
            Ok(Expression::UnaryOp(UnaryOp::Not, Box::new(rhs)))
        }
        TokenData::Number(n) => Ok(Expression::Literal(Literal::Int(n))),
        TokenData::Float(value) => {
            if let Some(TokenData::Word(suffix)) = tokens.first() {
                if suffix == "f64" {
                    tokens.remove(0);
                    return Ok(Expression::Literal(Literal::Float64(value)));
                }
                if suffix == "f32" {
                    tokens.remove(0);
                    return Ok(Expression::Literal(Literal::Float32(value)));
                }
            }
            Ok(Expression::Literal(Literal::Float32(value)))
        }
        TokenData::Char(value) => Ok(Expression::Call(
            qualify_namespace_function_name("Char", "from_code"),
            vec![Expression::Literal(Literal::Int(value as u32))],
        )),
        TokenData::String(s) => Ok(Expression::Literal(Literal::String(s))),
        TokenData::Word(s) => {
            if s == "match" {
                return parse_match_expression(tokens);
            }
            if s == "true" {
                return Ok(Expression::Literal(Literal::Bool(true)));
            }
            if s == "false" {
                return Ok(Expression::Literal(Literal::Bool(false)));
            }
            if tokens.get(0) == Some(&TokenData::Word("struct".to_string())) {
                parse_struct_value(tokens, s)
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
                trace!("Parsing field access {:?}", lhs);
                tokens.remove(0); // Consume '.'
                let field_token = if tokens.is_empty() {
                    return Err(anyhow::anyhow!(
                        "unexpected end of file after '.' in expression"
                    ));
                } else {
                    tokens.remove(0)
                };
                let field_name = expect_identifier(field_token)?;
                let struct_variable = match lhs {
                    Expression::Variable(s) => s,
                    other => {
                        return Err(anyhow::anyhow!(
                            "expected variable before '.', got {:?}",
                            other
                        ))
                    }
                };
                lhs = Expression::FieldAccess {
                    struct_variable,
                    field: field_name,
                };
                continue;
            }
            Some(TokenData::Parenthesis {
                opening: '(',
                is_opening: true,
            }) => {
                let args = parse_call_args(tokens)?;
                lhs = match lhs {
                    Expression::Variable(name) => Expression::Call(name, args),
                    expr => Expression::PostfixCall {
                        callee: Box::new(expr),
                        args,
                    },
                };
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

fn parse_generic_declaration(tokens: &mut Vec<TokenData>) -> anyhow::Result<GenericDef> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("generic".to_string()),
        "expected 'generic' keyword"
    );

    let name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        _ => return Err(anyhow::anyhow!("expected generic name")),
    };

    let params = parse_generic_params(tokens)?;

    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '{',
                is_opening: true
            },
        "expected '{{' after generic header"
    );

    let mut type_definitions = vec![];
    let mut top_level_functions = vec![];
    let mut invariants = vec![];
    loop {
        match tokens.first() {
            Some(TokenData::Parenthesis {
                opening: '}',
                is_opening: false,
            }) => {
                tokens.remove(0);
                break;
            }
            Some(TokenData::Word(name)) if name == "struct" => {
                let struct_def = parse_struct_declaration(tokens)?;
                type_definitions.push(TypeDefDecl::Struct(struct_def));
            }
            Some(TokenData::Word(name)) if name == "enum" => {
                let enum_def = parse_enum_declaration(tokens)?;
                type_definitions.push(TypeDefDecl::Enum(enum_def));
            }
            Some(TokenData::Word(name)) if name == "fun" => {
                let function = parse_function_declaration(tokens, false)?;
                top_level_functions.push(function);
            }
            Some(TokenData::Word(name)) if name == "extern" => {
                return Err(anyhow::anyhow!(
                    "generic body only supports `fun`, `comptime fun`, type declarations, and invariants in v1"
                ));
            }
            Some(TokenData::Word(name)) if name == "comptime" => match tokens.get(1) {
                Some(TokenData::Word(kind)) if kind == "fun" => {
                    let function = parse_function_declaration(tokens, true)?;
                    top_level_functions.push(function);
                }
                token => {
                    return Err(anyhow::anyhow!(
                        "unexpected token after 'comptime' in generic body: {:?}",
                        token
                    ))
                }
            },
            Some(TokenData::Word(name)) if name == "invariant" => {
                let invariant = parse_struct_invariant_declaration(tokens)?;
                invariants.push(invariant);
            }
            Some(TokenData::Newline) => {
                tokens.remove(0);
            }
            Some(tok) => {
                return Err(anyhow::anyhow!(
                    "unexpected token in generic body: {:?}",
                    tok
                ))
            }
            None => return Err(anyhow::anyhow!("unexpected end of file in generic body")),
        }
    }

    Ok(GenericDef {
        name,
        params,
        type_definitions,
        top_level_functions,
        invariants,
    })
}

fn parse_generic_specialization(
    tokens: &mut Vec<TokenData>,
) -> anyhow::Result<GenericSpecialization> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("specialize".to_string()),
        "expected 'specialize' keyword"
    );

    let alias = match tokens.remove(0) {
        TokenData::Word(name) => name,
        _ => return Err(anyhow::anyhow!("expected specialization alias name")),
    };

    anyhow::ensure!(
        tokens.remove(0) == TokenData::Symbols("=".to_string()),
        "expected '=' after specialization alias"
    );

    let generic_name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        _ => return Err(anyhow::anyhow!("expected generic name")),
    };

    let concrete_types = parse_bracketed_type_argument_list(tokens)?;
    anyhow::ensure!(
        !concrete_types.is_empty(),
        "specialization must provide at least one concrete type argument"
    );

    Ok(GenericSpecialization {
        alias,
        generic_name,
        concrete_types,
    })
}

fn parse_trait_method_signature(tokens: &mut Vec<TokenData>) -> anyhow::Result<TraitMethodSig> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("fun".to_string()),
        "expected 'fun' keyword in trait body"
    );
    let name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        token => {
            return Err(anyhow::anyhow!(
                "expected trait method name, got {:?}",
                token
            ))
        }
    };
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '(',
                is_opening: true
            },
        "expected '(' after trait method name"
    );
    let parameters = parse_function_args(tokens)?;
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Symbols("->".to_string()),
        "expected '->' after trait method parameters"
    );
    let return_type = parse_type_reference(tokens)?;
    if tokens.first() == Some(&TokenData::Symbols(",".to_string())) {
        tokens.remove(0);
    }
    while tokens.first() == Some(&TokenData::Newline) {
        tokens.remove(0);
    }
    Ok(TraitMethodSig {
        name,
        parameters,
        return_type,
    })
}

fn parse_trait_declaration(tokens: &mut Vec<TokenData>) -> anyhow::Result<TraitDecl> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("trait".to_string()),
        "expected 'trait' keyword"
    );
    let name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        token => return Err(anyhow::anyhow!("expected trait name, got {:?}", token)),
    };
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '{',
                is_opening: true
            },
        "expected '{{' after trait name"
    );

    let mut methods = vec![];
    loop {
        match tokens.first() {
            Some(TokenData::Parenthesis {
                opening: '}',
                is_opening: false,
            }) => {
                tokens.remove(0);
                break;
            }
            Some(TokenData::Newline) => {
                tokens.remove(0);
            }
            Some(TokenData::Word(name)) if name == "fun" => {
                methods.push(parse_trait_method_signature(tokens)?);
            }
            Some(token) => {
                return Err(anyhow::anyhow!(
                    "trait body only supports method signatures, found {:?}",
                    token
                ));
            }
            None => return Err(anyhow::anyhow!("unexpected end of file in trait body")),
        }
    }

    Ok(TraitDecl { name, methods })
}

fn parse_impl_declaration(tokens: &mut Vec<TokenData>) -> anyhow::Result<ImplDecl> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("impl".to_string()),
        "expected 'impl' keyword"
    );
    let trait_name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        token => {
            return Err(anyhow::anyhow!(
                "expected trait name in impl, got {:?}",
                token
            ))
        }
    };
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("for".to_string()),
        "expected 'for' after trait name in impl declaration"
    );
    let for_type = parse_type_reference(tokens)?;
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '{',
                is_opening: true
            },
        "expected '{{' after impl header"
    );

    let mut methods = vec![];
    loop {
        match tokens.first() {
            Some(TokenData::Parenthesis {
                opening: '}',
                is_opening: false,
            }) => {
                tokens.remove(0);
                break;
            }
            Some(TokenData::Newline) => {
                tokens.remove(0);
            }
            Some(TokenData::Word(name)) if name == "fun" => {
                let method = parse_function_declaration(tokens, false)?;
                anyhow::ensure!(
                    !method.is_extern,
                    "impl method {} cannot be extern",
                    method.name
                );
                methods.push(method);
            }
            Some(TokenData::Word(name)) if name == "comptime" => {
                return Err(anyhow::anyhow!("impl methods cannot be comptime in v1"));
            }
            Some(token) => {
                return Err(anyhow::anyhow!(
                    "impl body only supports method functions, found {:?}",
                    token
                ));
            }
            None => return Err(anyhow::anyhow!("unexpected end of file in impl body")),
        }
    }

    Ok(ImplDecl {
        trait_name,
        for_type,
        methods,
    })
}

#[cfg(test)]
mod tests {
    use crate::tokenizer::tokenize;

    use super::parse;

    #[test]
    fn parses_generic_with_bounds_and_specialization() {
        let source = r#"
generic HashMap[K: Hash + Eq, V] {
	struct HashMap {
		_size: I32,
	}
}

specialize IntToInt = HashMap[I32, I32]
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize generic source");
        let ast = parse(tokens).expect("parse generic source");

        assert_eq!(ast.generic_definitions.len(), 1);
        assert_eq!(ast.generic_specializations.len(), 1);
        let generic = &ast.generic_definitions[0];
        assert_eq!(generic.name, "HashMap");
        assert_eq!(generic.params.len(), 2);
        assert_eq!(generic.params[0].name, "K");
        assert_eq!(generic.params[0].bounds, vec!["Hash", "Eq"]);
        assert_eq!(generic.params[1].name, "V");
        assert!(generic.params[1].bounds.is_empty());
        assert_eq!(ast.generic_specializations[0].alias, "IntToInt");
        assert_eq!(ast.generic_specializations[0].generic_name, "HashMap");
        assert_eq!(
            ast.generic_specializations[0].concrete_types,
            vec!["I32".to_string(), "I32".to_string()]
        );
    }

    #[test]
    fn parses_trait_and_impl_declarations() {
        let source = r#"
trait Hash {
	fun hash(v: Self) -> I32
}

impl Hash for I32 {
	fun hash(v: I32) -> I32 {
		return v
	}
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize trait source");
        let ast = parse(tokens).expect("parse trait source");

        assert_eq!(ast.trait_declarations.len(), 1);
        assert_eq!(ast.impl_declarations.len(), 1);
        assert_eq!(ast.trait_declarations[0].name, "Hash");
        assert_eq!(ast.trait_declarations[0].methods.len(), 1);
        assert_eq!(ast.trait_declarations[0].methods[0].name, "hash");
        assert_eq!(ast.impl_declarations[0].trait_name, "Hash");
        assert_eq!(ast.impl_declarations[0].for_type, "I32");
        assert_eq!(ast.impl_declarations[0].methods.len(), 1);
    }

    #[test]
    fn parses_nested_multi_arg_type_references() {
        let source = r#"
struct Holder {
	value: Pair[Option[I32], Result[I32, Bool]],
}

fun id(v: Pair[Option[I32], Result[I32, Bool]]) -> Pair[Option[I32], Result[I32, Bool]] {
	return v
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize nested type source");
        let ast = parse(tokens).expect("parse nested type source");
        let super::TypeDefDecl::Struct(holder) = &ast.type_definitions[0] else {
            panic!("expected struct");
        };
        assert_eq!(
            holder.struct_fields[0].ty,
            "Pair[Option[I32],Result[I32,Bool]]"
        );
    }

    #[test]
    fn rejects_template_keyword_with_migration_hint() {
        let source = r#"
template Option[T] {
	enum Option {
		None,
		Some(T),
	}
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize legacy template source");
        let err = parse(tokens).expect_err("legacy template syntax should fail");
        assert!(
            err.to_string().contains("template syntax was removed"),
            "unexpected parse error: {err}"
        );
    }

    #[test]
    fn rejects_instantiate_keyword_with_migration_hint() {
        let source = r#"
specialize OptionI32 = Option[I32]
"#
        .replace("specialize", "instantiate");

        let tokens = tokenize(source).expect("tokenize legacy instantiate source");
        let err = parse(tokens).expect_err("legacy instantiate syntax should fail");
        assert!(
            err.to_string().contains("instantiate syntax was removed"),
            "unexpected parse error: {err}"
        );
    }

    #[test]
    fn parses_import_declaration() {
        let source = r#"
import "helpers.oa"

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize import source");
        let ast = parse(tokens).expect("parse import source");
        assert_eq!(ast.imports.len(), 1);
        assert_eq!(ast.imports[0].path, "helpers.oa");
    }

    #[test]
    fn parses_struct_invariant_declaration() {
        let source = r#"
struct Counter {
	value: I32,
}

invariant "positive .value" for (v: Counter) {
	return v.value >= 0
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize invariant source");
        let ast = parse(tokens).expect("parse invariant source");

        assert_eq!(ast.invariants.len(), 1);
        assert_eq!(ast.invariants[0].identifier, None);
        assert_eq!(ast.invariants[0].display_name, "positive .value");
        assert_eq!(ast.invariants[0].parameter.name, "v");
        assert_eq!(ast.invariants[0].parameter.ty, "Counter");
    }

    #[test]
    fn parses_named_struct_invariant_declaration() {
        let source = r#"
struct Counter {
	value: I32,
}

invariant positive_value "positive .value" for (v: Counter) {
	return v.value >= 0
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize named invariant source");
        let ast = parse(tokens).expect("parse named invariant source");

        assert_eq!(ast.invariants.len(), 1);
        assert_eq!(
            ast.invariants[0].identifier.as_deref(),
            Some("positive_value")
        );
        assert_eq!(ast.invariants[0].display_name, "positive .value");
    }

    #[test]
    fn parses_generic_struct_invariant_declaration() {
        let source = r#"
generic Box[T] {
	struct Box {
		value: T,
	}

	invariant "value must be valid" for (v: Box) {
		return true
	}
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize generic invariant source");
        let ast = parse(tokens).expect("parse generic invariant source");

        assert_eq!(ast.generic_definitions.len(), 1);
        let generic = &ast.generic_definitions[0];
        assert_eq!(generic.invariants.len(), 1);
        assert_eq!(generic.invariants[0].display_name, "value must be valid");
        assert_eq!(generic.invariants[0].parameter.ty, "Box");
    }

    #[test]
    fn parses_struct_declaration_without_trailing_comma() {
        let source = r#"
struct Counter {
	value: I32
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");

        assert_eq!(ast.type_definitions.len(), 1);
        let super::TypeDefDecl::Struct(def) = &ast.type_definitions[0] else {
            panic!("expected struct definition");
        };
        assert_eq!(def.name, "Counter");
        assert_eq!(def.struct_fields.len(), 1);
        assert_eq!(def.struct_fields[0].name, "value");
        assert_eq!(def.struct_fields[0].ty, "I32");
    }

    #[test]
    fn parses_struct_literal_without_trailing_comma() {
        let source = r#"
struct Counter {
	value: I32,
}

fun main() -> I32 {
	c = Counter struct { value: 1 }
	return 0
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");

        assert_eq!(ast.top_level_functions.len(), 1);
        let main = &ast.top_level_functions[0];
        let super::Statement::Assign { value, .. } = &main.body[0] else {
            panic!("expected first statement to be assignment");
        };
        let super::Expression::StructValue {
            struct_name,
            field_values,
        } = value
        else {
            panic!("expected struct literal");
        };
        assert_eq!(struct_name, "Counter");
        assert_eq!(field_values.len(), 1);
        assert_eq!(field_values[0].0, "value");
    }

    #[test]
    fn parses_prove_and_assert_statements() {
        let source = r#"
fun main() -> I32 {
	prove(true)
	assert(1 < 2)
	return 0
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");
        let main = &ast.top_level_functions[0];
        assert!(!main.is_comptime);
        assert!(matches!(main.body[0], super::Statement::Prove { .. }));
        assert!(matches!(main.body[1], super::Statement::Assert { .. }));
    }

    #[test]
    fn parses_fp32_literal_expression() {
        let source = r#"
fun main() -> I32 {
	x = 1.25
	return 0
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");
        let main = &ast.top_level_functions[0];
        let super::Statement::Assign { value, .. } = &main.body[0] else {
            panic!("expected assignment statement");
        };
        let super::Expression::Literal(super::Literal::Float32(value)) = value else {
            panic!("expected FP32 literal");
        };
        assert_eq!(value, "1.25");
    }

    #[test]
    fn parses_fp64_literal_expression() {
        let source = r#"
fun main() -> I32 {
	x = 1.25f64
	return 0
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");
        let main = &ast.top_level_functions[0];
        let super::Statement::Assign { value, .. } = &main.body[0] else {
            panic!("expected assignment statement");
        };
        let super::Expression::Literal(super::Literal::Float64(value)) = value else {
            panic!("expected FP64 literal");
        };
        assert_eq!(value, "1.25");
    }

    #[test]
    fn parses_float_literals_ast_snapshot() {
        let source = r#"
fun main() -> I32 {
	a = 1.25
	b = 2.5f64
	return 0
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");
        insta::assert_json_snapshot!("parser_float_literals_ast", ast);
    }

    #[test]
    fn parses_char_literal_expression() {
        let source = r#"
fun main() -> I32 {
	x = 'x'
	return 0
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");
        let main = &ast.top_level_functions[0];
        let super::Statement::Assign { value, .. } = &main.body[0] else {
            panic!("expected assignment statement");
        };
        let super::Expression::Call(name, args) = value else {
            panic!("expected Char constructor call");
        };
        assert_eq!(name, "Char__from_code");
        assert_eq!(args.len(), 1);
        let super::Expression::Literal(super::Literal::Int(code)) = &args[0] else {
            panic!("expected integer literal argument");
        };
        assert_eq!(*code, 'x' as u32);
    }

    #[test]
    fn parses_char_literals_ast_snapshot() {
        let source = r#"
fun main() -> I32 {
	ch = 'x'
	nl = '\n'
	return 0
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");
        insta::assert_json_snapshot!("parser_char_literals_ast", ast);
    }

    #[test]
    fn rejects_prove_wrong_arity() {
        let source = r#"
fun main() -> I32 {
	prove(true, false)
	return 0
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let err = parse(tokens).expect_err("prove wrong arity must fail");
        assert!(
            err.to_string()
                .contains("prove expects exactly one Bool argument"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn parses_comptime_fun_and_apply() {
        let source = r#"
comptime fun build_counter(T: Type) -> DeclSet {
	return declset_new()
}

comptime apply build_counter(Counter)
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");
        assert_eq!(ast.top_level_functions.len(), 1);
        assert!(ast.top_level_functions[0].is_comptime);
        assert_eq!(ast.comptime_applies.len(), 1);
        assert_eq!(ast.comptime_applies[0].function_name, "build_counter");
        assert_eq!(ast.comptime_applies[0].argument_type, "Counter");
    }

    #[test]
    fn parses_extern_function_declaration() {
        let source = r#"
extern fun free(ptr: PtrInt) -> Void

fun main() -> I32 {
	return 0
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");

        assert_eq!(ast.top_level_functions.len(), 2);
        let free = &ast.top_level_functions[0];
        assert_eq!(free.name, "free");
        assert_eq!(free.extern_symbol_name, None);
        assert!(free.is_extern);
        assert!(!free.is_comptime);
        assert!(free.body.is_empty());
        assert_eq!(free.parameters.len(), 1);
        assert_eq!(free.parameters[0].name, "ptr");
        assert_eq!(free.parameters[0].ty, "PtrInt");
        assert_eq!(free.return_type, "Void");
    }

    #[test]
    fn parses_namespace_function_and_namespaced_call() {
        let source = r#"
struct Option {
	value: I32,
}

namespace Option {
	fun is_some(v: Option) -> Bool {
		return v.value > 0
	}
}

fun main() -> I32 {
	v = Option struct { value: 1 }
	Option.is_some(v)
	return 0
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");

        assert_eq!(ast.top_level_functions.len(), 2);
        assert_eq!(ast.top_level_functions[0].name, "Option__is_some");
        assert_eq!(ast.top_level_functions[0].extern_symbol_name, None);

        let main = &ast.top_level_functions[1];
        let super::Statement::Expression { expr } = &main.body[1] else {
            panic!("expected namespaced call expression");
        };
        let super::Expression::PostfixCall { callee, args } = expr else {
            panic!("expected postfix call for namespaced call");
        };
        let super::Expression::FieldAccess {
            struct_variable,
            field,
        } = callee.as_ref()
        else {
            panic!("expected field-access callee in namespaced call");
        };
        assert_eq!(struct_variable, "Option");
        assert_eq!(field, "is_some");
        assert_eq!(args.len(), 1);
    }

    #[test]
    fn parses_test_declaration() {
        let source = r#"
test "A hashtable MUST have size 0 when created" {
	assert(true)
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");
        assert_eq!(ast.tests.len(), 1);
        assert_eq!(
            ast.tests[0].name,
            "A hashtable MUST have size 0 when created"
        );
        assert!(matches!(
            ast.tests[0].body[0],
            super::Statement::Assert { .. }
        ));
    }

    #[test]
    fn parses_namespace_extern_function_and_mangles_only_internal_name() {
        let source = r#"
namespace Clib {
	extern fun free(ptr: PtrInt) -> Void
}

fun main() -> I32 {
	Clib.free(i32_to_i64(0))
	return 0
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");

        assert_eq!(ast.top_level_functions.len(), 2);
        let free = &ast.top_level_functions[0];
        assert_eq!(free.name, "Clib__free");
        assert_eq!(free.extern_symbol_name.as_deref(), Some("free"));
        assert!(free.is_extern);
    }

    #[test]
    fn rejects_comptime_function_inside_namespace() {
        let source = r#"
namespace Option {
	comptime fun bad(v: I32) -> I32 {
		return v
	}
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let err = parse(tokens).expect_err("namespace comptime function must fail");
        assert!(
            err.to_string()
                .contains("only supports `fun` and `extern fun` declarations"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn rejects_comptime_apply_inside_function_body() {
        let source = r#"
fun main() -> I32 {
	comptime apply x(Counter)
	return 0
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let err = parse(tokens).expect_err("comptime apply must be top-level");
        assert!(
            err.to_string()
                .contains("`comptime` declarations are only allowed at top level"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn rejects_struct_literal_missing_brace_without_panicking() {
        let source = r#"
struct Counter {
	value: I32,
}

fun main() -> I32 {
	c = Counter struct value: 1
	return 0
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let err = parse(tokens).expect_err("malformed struct literal must fail");
        assert!(
            err.to_string()
                .contains("expected opening '{' in struct literal"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn rejects_field_access_on_non_variable_without_panicking() {
        let source = r#"
fun main() -> I32 {
	x = (1 + 2).value
	return 0
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let err = parse(tokens).expect_err("invalid field access lhs must fail");
        assert!(
            err.to_string().contains("expected variable before '.'"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn rejects_unterminated_function_body_without_panicking() {
        let source = r#"
fun main() -> I32 {
	return 0
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let err = parse(tokens).expect_err("unterminated function body must fail");
        assert!(
            err.to_string().contains("unexpected end of file in function body"),
            "unexpected error: {err}"
        );
    }
}
