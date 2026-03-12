use std::collections::HashMap;

use serde::Serialize;
use tracing::trace;

use crate::ast_paths::{
    bin_left_segment, bin_right_segment, expression_statement_segment, if_else_statement_segment,
    if_then_statement_segment, join_path, local_precondition_key, local_statement_key,
    match_arm_expression_segment, match_arm_statement_segment, struct_field_segment, unary_segment,
    while_body_statement_segment, AstPathStyle,
};
use crate::source_span::SourceSpan;
use crate::tokenizer::{TokenData, TokenList, TokenSpan};

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
    pub generic_specializations: Vec<GenericSpecialization>,
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
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub preconditions: Vec<Expression>,
    pub body: Vec<Statement>,
    pub return_type: String,
    pub is_comptime: bool,
    pub is_extern: bool,
    #[serde(skip)]
    pub source_span: Option<SourceSpan>,
    #[serde(skip)]
    pub local_source_spans: HashMap<String, SourceSpan>,
    #[serde(skip)]
    pub precondition_source_spans: Vec<SourceSpan>,
}

#[derive(Clone, Debug, Serialize)]
pub struct StructInvariantDecl {
    pub identifier: Option<String>,
    pub display_name: String,
    pub parameters: Vec<Parameter>,
    pub body: Vec<Statement>,
    #[serde(skip)]
    pub source_span: Option<SourceSpan>,
    #[serde(skip)]
    pub local_source_spans: HashMap<String, SourceSpan>,
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
    MethodCall {
        receiver: Box<Expression>,
        method: String,
        args: Vec<Expression>,
    },
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

#[derive(Clone, Debug)]
struct TokenCursor {
    tokens: Vec<TokenData>,
    spans: Vec<TokenSpan>,
    source_name: Option<String>,
    last_removed_span: Option<TokenSpan>,
}

impl TokenCursor {
    fn new(tokens: TokenList) -> Self {
        Self {
            tokens: tokens.tokens,
            spans: tokens.spans,
            source_name: tokens.source_name,
            last_removed_span: None,
        }
    }

    fn first(&self) -> Option<&TokenData> {
        self.tokens.first()
    }

    fn get(&self, index: usize) -> Option<&TokenData> {
        self.tokens.get(index)
    }

    fn remove(&mut self, index: usize) -> TokenData {
        debug_assert_eq!(index, 0, "parser only removes from the front");
        let token = self.tokens.remove(index);
        self.last_removed_span = self.spans.get(index).cloned();
        self.spans.remove(index);
        token
    }

    fn retain(&mut self, mut predicate: impl FnMut(&TokenData) -> bool) {
        let mut kept_tokens = Vec::with_capacity(self.tokens.len());
        let mut kept_spans = Vec::with_capacity(self.spans.len());
        for (token, span) in self.tokens.drain(..).zip(self.spans.drain(..)) {
            if predicate(&token) {
                kept_tokens.push(token);
                kept_spans.push(span);
            }
        }
        self.tokens = kept_tokens;
        self.spans = kept_spans;
    }

    fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    fn current_token_span(&self) -> Option<TokenSpan> {
        self.spans.first().cloned()
    }

    fn last_removed_source_span(&self) -> Option<SourceSpan> {
        self.last_removed_span
            .as_ref()
            .map(|span| span.as_source_span(self.source_name.as_deref()))
    }

    fn source_name(&self) -> Option<&str> {
        self.source_name.as_deref()
    }
}

#[derive(Clone, Debug, Default)]
struct LocalSourceRecorder {
    local_source_spans: HashMap<String, SourceSpan>,
    precondition_source_spans: Vec<SourceSpan>,
}

impl LocalSourceRecorder {
    fn record_local(&mut self, path: impl Into<String>, span: Option<SourceSpan>) {
        if let Some(span) = span {
            self.local_source_spans.insert(path.into(), span);
        }
    }

    fn record_precondition(&mut self, span: Option<SourceSpan>) {
        if let Some(span) = span {
            self.precondition_source_spans.push(span);
        }
    }
}

#[derive(Clone, Debug)]
struct ParsedExpressionNode {
    expression: Expression,
    span: Option<SourceSpan>,
    children: Vec<(String, ParsedExpressionNode)>,
}

impl ParsedExpressionNode {
    fn new(expression: Expression, span: Option<SourceSpan>) -> Self {
        Self {
            expression,
            span,
            children: Vec::new(),
        }
    }
}

fn compose_source_span(
    start: Option<TokenSpan>,
    end: Option<SourceSpan>,
    source_name: Option<&str>,
) -> Option<SourceSpan> {
    let start = start?;
    let end = end?;
    Some(SourceSpan::new(
        source_name.map(str::to_string),
        start.start.line,
        start.start.column,
        end.end_line?,
        end.end_column?,
    ))
}

fn record_path_span(
    recorder: Option<&mut LocalSourceRecorder>,
    path: &str,
    span: Option<SourceSpan>,
) {
    if path.is_empty() {
        return;
    }
    if let Some(recorder) = recorder {
        recorder.record_local(path.to_string(), span);
    }
}

fn local_statement_segment(_style: AstPathStyle, index: usize) -> String {
    local_statement_key(index)
}

fn record_expression_node(
    recorder: &mut LocalSourceRecorder,
    path: &str,
    node: &ParsedExpressionNode,
) {
    if !path.is_empty() {
        recorder.record_local(path.to_string(), node.span.clone());
    }
    for (segment, child) in &node.children {
        record_expression_node(recorder, &join_path(path, segment, AstPathStyle::Ir), child);
    }
}

#[allow(dead_code)]
fn parse_statement(tokens: &mut TokenCursor) -> anyhow::Result<Statement> {
    parse_statement_with_path(tokens, None, "")
}

fn parse_statement_with_path(
    tokens: &mut TokenCursor,
    mut recorder: Option<&mut LocalSourceRecorder>,
    statement_path: &str,
) -> anyhow::Result<Statement> {
    let start = tokens.current_token_span();
    trace!(?tokens, "Parsing statement");

    let statement = match tokens.first() {
        Some(TokenData::Word(name)) => {
            let name = name.clone();

            if name == "return" {
                tokens.remove(0);
                let expr = parse_expression_with_path(
                    tokens,
                    0,
                    recorder.as_deref_mut(),
                    &join_path(statement_path, "return.expr", AstPathStyle::Ir),
                )?;
                Statement::Return { expr }
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
                parse_builtin_assertion_statement(tokens, recorder.as_deref_mut(), statement_path)?
            } else if name == "match" {
                tokens.remove(0);
                parse_match_statement(tokens, recorder.as_deref_mut(), statement_path)?
            } else if name == "if" {
                tokens.remove(0);
                let condition = parse_expression_with_path(
                    tokens,
                    0,
                    recorder.as_deref_mut(),
                    &join_path(statement_path, "if.cond", AstPathStyle::Ir),
                )?;
                let body = parse_braced_block(
                    tokens,
                    recorder.as_deref_mut(),
                    statement_path,
                    if_then_statement_segment,
                )?;
                let else_body =
                    parse_optional_else(tokens, recorder.as_deref_mut(), statement_path)?;
                Statement::Conditional {
                    condition,
                    body,
                    else_body,
                }
            } else if name == "while" {
                tokens.remove(0);
                let condition = parse_expression_with_path(
                    tokens,
                    0,
                    recorder.as_deref_mut(),
                    &join_path(statement_path, "while.cond", AstPathStyle::Ir),
                )?;
                let body = parse_braced_block(
                    tokens,
                    recorder.as_deref_mut(),
                    statement_path,
                    while_body_statement_segment,
                )?;
                Statement::While { condition, body }
            } else if tokens.get(1) == Some(&TokenData::Symbols("=".to_string())) {
                tokens.remove(0);
                tokens.remove(0);
                trace!("Parsing assignment statement");
                let value = parse_expression_with_path(
                    tokens,
                    0,
                    recorder.as_deref_mut(),
                    &join_path(statement_path, "assign.value", AstPathStyle::Ir),
                )?;
                Statement::Assign {
                    variable: name,
                    value,
                }
            } else {
                let expr = parse_expression_with_path(
                    tokens,
                    0,
                    recorder.as_deref_mut(),
                    &join_path(
                        statement_path,
                        expression_statement_segment(AstPathStyle::Ir),
                        AstPathStyle::Ir,
                    ),
                )?;
                Statement::Expression { expr }
            }
        }
        token => return Err(anyhow::anyhow!("expected statement instead of {:?}", token)),
    };
    record_path_span(
        recorder,
        statement_path,
        compose_source_span(
            start,
            tokens.last_removed_source_span(),
            tokens.source_name(),
        ),
    );
    Ok(statement)
}

fn parse_builtin_assertion_statement(
    tokens: &mut TokenCursor,
    mut recorder: Option<&mut LocalSourceRecorder>,
    statement_path: &str,
) -> anyhow::Result<Statement> {
    let keyword = match tokens.remove(0) {
        TokenData::Word(name) if name == "prove" || name == "assert" => name,
        other => {
            return Err(anyhow::anyhow!(
                "expected builtin assertion keyword, got {:?}",
                other
            ))
        }
    };

    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '(',
                is_opening: true
            },
        "expected opening parenthesis for builtin assertion"
    );
    let condition = parse_expression_with_path(
        tokens,
        0,
        recorder.as_deref_mut(),
        &join_path(
            statement_path,
            if keyword == "prove" {
                "prove.cond"
            } else {
                "assert.cond"
            },
            AstPathStyle::Ir,
        ),
    )?;
    if matches!(tokens.first(), Some(TokenData::Symbols(symbols)) if symbols == ",") {
        return Err(anyhow::anyhow!(
            "{keyword} expects exactly one Bool argument"
        ));
    }
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: ')',
                is_opening: false
            },
        "expected closing parenthesis for builtin assertion"
    );
    if keyword == "prove" {
        Ok(Statement::Prove { condition })
    } else {
        Ok(Statement::Assert { condition })
    }
}

fn consume_newlines(tokens: &mut TokenCursor) {
    while tokens.first() == Some(&TokenData::Newline) {
        tokens.remove(0);
    }
}

fn parse_braced_block(
    tokens: &mut TokenCursor,
    mut recorder: Option<&mut LocalSourceRecorder>,
    statement_path: &str,
    child_segment: fn(AstPathStyle, usize) -> String,
) -> anyhow::Result<Vec<Statement>> {
    consume_newlines(tokens);
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
                let nested_path = join_path(
                    statement_path,
                    &child_segment(AstPathStyle::Ir, body.len()),
                    AstPathStyle::Ir,
                );
                let statement =
                    parse_statement_with_path(tokens, recorder.as_deref_mut(), &nested_path)?;
                body.push(statement);
            }
            None => return Err(anyhow::anyhow!("unexpected end of file in braced block")),
        }
    }
    Ok(body)
}

fn parse_match_pattern(tokens: &mut TokenCursor) -> anyhow::Result<MatchPattern> {
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

fn parse_match_arm_body(
    tokens: &mut TokenCursor,
    mut recorder: Option<&mut LocalSourceRecorder>,
    statement_path: &str,
    arm_index: usize,
) -> anyhow::Result<Vec<Statement>> {
    consume_newlines(tokens);
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
                let nested_path = join_path(
                    statement_path,
                    &match_arm_statement_segment(AstPathStyle::Ir, arm_index, body.len()),
                    AstPathStyle::Ir,
                );
                let statement =
                    parse_statement_with_path(tokens, recorder.as_deref_mut(), &nested_path)?;
                body.push(statement);
            }
            None => return Err(anyhow::anyhow!("unexpected end of file in braced block")),
        }
    }
    Ok(body)
}

fn parse_match_statement(
    tokens: &mut TokenCursor,
    mut recorder: Option<&mut LocalSourceRecorder>,
    statement_path: &str,
) -> anyhow::Result<Statement> {
    let subject = parse_expression_with_path(
        tokens,
        0,
        recorder.as_deref_mut(),
        &join_path(statement_path, "match.subject", AstPathStyle::Ir),
    )?;
    consume_newlines(tokens);
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
                let arm_index = arms.len();
                let body = parse_match_arm_body(
                    tokens,
                    recorder.as_deref_mut(),
                    statement_path,
                    arm_index,
                )?;
                arms.push(MatchArm { pattern, body });
            }
            None => return Err(anyhow::anyhow!("unexpected end of file in match")),
        }
    }

    Ok(Statement::Match { subject, arms })
}

fn parse_optional_else(
    tokens: &mut TokenCursor,
    mut recorder: Option<&mut LocalSourceRecorder>,
    statement_path: &str,
) -> anyhow::Result<Option<Vec<Statement>>> {
    while tokens.first() == Some(&TokenData::Newline) {
        tokens.remove(0);
    }

    if tokens.first() != Some(&TokenData::Word("else".to_string())) {
        return Ok(None);
    }
    tokens.remove(0);

    if tokens.first() == Some(&TokenData::Word("if".to_string())) {
        let nested_path = join_path(
            statement_path,
            &if_else_statement_segment(AstPathStyle::Ir, 0),
            AstPathStyle::Ir,
        );
        let nested = parse_statement_with_path(tokens, recorder.as_deref_mut(), &nested_path)?;
        match nested {
            Statement::Conditional { .. } => Ok(Some(vec![nested])),
            other => Err(anyhow::anyhow!(
                "expected else-if conditional statement, got {:?}",
                other
            )),
        }
    } else {
        let body = parse_braced_block(
            tokens,
            recorder.as_deref_mut(),
            statement_path,
            if_else_statement_segment,
        )?;
        Ok(Some(body))
    }
}

fn parse_function_args(tokens: &mut TokenCursor) -> anyhow::Result<Vec<Parameter>> {
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

fn parse_parameter_list(tokens: &mut TokenCursor) -> anyhow::Result<Vec<Parameter>> {
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '(',
                is_opening: true
            },
        "expected opening parenthesis"
    );
    parse_function_args(tokens)
}

fn parse_function_like_body(
    tokens: &mut TokenCursor,
    mut recorder: Option<&mut LocalSourceRecorder>,
) -> anyhow::Result<Vec<Statement>> {
    consume_newlines(tokens);
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
                let statement = parse_statement_with_path(
                    tokens,
                    recorder.as_deref_mut(),
                    &local_statement_key(body.len()),
                )?;
                body.push(statement);
            }
            None => return Err(anyhow::anyhow!("unexpected end of file in function body")),
        }
    }

    Ok(body)
}

fn parse_precondition_block(
    tokens: &mut TokenCursor,
    mut recorder: Option<&mut LocalSourceRecorder>,
) -> anyhow::Result<Vec<Expression>> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("pre".to_string()),
        "expected 'pre' keyword"
    );
    consume_newlines(tokens);
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '{',
                is_opening: true
            },
        "expected opening brace after pre"
    );
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Newline,
        "expected newline after opening brace in pre block"
    );

    let mut preconditions = vec![];
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
                let clause_start = tokens.current_token_span();
                let expression = parse_expression_with_path(
                    tokens,
                    0,
                    recorder.as_deref_mut(),
                    &local_precondition_key(preconditions.len()),
                )?;
                if let Some(recorder) = recorder.as_deref_mut() {
                    recorder.record_precondition(compose_source_span(
                        clause_start,
                        tokens.last_removed_source_span(),
                        tokens.source_name(),
                    ));
                }
                preconditions.push(expression);
                match tokens.first() {
                    Some(TokenData::Newline) => {
                        tokens.remove(0);
                    }
                    Some(TokenData::Parenthesis {
                        opening: '}',
                        is_opening: false,
                    }) => {}
                    Some(token) => {
                        return Err(anyhow::anyhow!(
                            "expected newline or closing brace after precondition expression, got {:?}",
                            token
                        ));
                    }
                    None => {
                        return Err(anyhow::anyhow!("unexpected end of file in pre block"));
                    }
                }
            }
            None => return Err(anyhow::anyhow!("unexpected end of file in pre block")),
        }
    }

    anyhow::ensure!(
        !preconditions.is_empty(),
        "expected at least one precondition clause in pre block"
    );
    Ok(preconditions)
}

fn parse_struct_declaration(tokens: &mut TokenCursor) -> anyhow::Result<StructDef> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("struct".to_string()),
        "expected 'struct' keyword"
    );

    let name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        _ => return Err(anyhow::anyhow!("expected struct name")),
    };

    consume_newlines(tokens);
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

fn parse_enum_declaration(tokens: &mut TokenCursor) -> anyhow::Result<EnumDef> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("enum".to_string()),
        "expected 'enum' keyword"
    );

    let name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        _ => return Err(anyhow::anyhow!("expected enum name")),
    };

    consume_newlines(tokens);
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

                let payload_ty = match tokens.first() {
                    Some(TokenData::Symbols(symbol)) if symbol == ":" => {
                        tokens.remove(0);
                        Some(parse_type_reference(tokens)?)
                    }
                    Some(TokenData::Parenthesis {
                        opening: '(',
                        is_opening: true,
                    }) => {
                        return Err(anyhow::anyhow!(
                            "enum payload syntax uses ':' (for example `{}: Type`) instead of parentheses",
                            variant_name
                        ));
                    }
                    _ => None,
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
    tokens: &mut TokenCursor,
    is_comptime: bool,
) -> anyhow::Result<Function> {
    let start = tokens.current_token_span();
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

    let parameters = parse_parameter_list(tokens)?;

    // parse -> return type
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Symbols("->".to_string()),
        "expected '->' after function parameters"
    );

    let return_type = parse_type_reference(tokens)?;
    consume_newlines(tokens);
    let mut recorder = LocalSourceRecorder::default();
    let preconditions = if tokens.first() == Some(&TokenData::Word("pre".to_string())) {
        parse_precondition_block(tokens, Some(&mut recorder))?
    } else {
        vec![]
    };

    let body = parse_function_like_body(tokens, Some(&mut recorder))?;

    Ok(Function {
        name,
        extern_symbol_name: None,
        parameters,
        preconditions,
        body,
        return_type,
        is_comptime,
        is_extern: false,
        source_span: compose_source_span(
            start,
            tokens.last_removed_source_span(),
            tokens.source_name(),
        ),
        local_source_spans: recorder.local_source_spans,
        precondition_source_spans: recorder.precondition_source_spans,
    })
}

fn parse_extern_function_declaration(tokens: &mut TokenCursor) -> anyhow::Result<Function> {
    let start = tokens.current_token_span();
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

    let parameters = parse_parameter_list(tokens)?;

    anyhow::ensure!(
        tokens.remove(0) == TokenData::Symbols("->".to_string()),
        "expected '->' after function parameters"
    );
    let return_type = parse_type_reference(tokens)?;
    if tokens.first() == Some(&TokenData::Word("pre".to_string())) {
        return Err(anyhow::anyhow!(
            "extern function {} cannot use pre blocks in v1",
            name
        ));
    }

    Ok(Function {
        name,
        extern_symbol_name: None,
        parameters,
        preconditions: vec![],
        body: vec![],
        return_type,
        is_comptime: false,
        is_extern: true,
        source_span: compose_source_span(
            start,
            tokens.last_removed_source_span(),
            tokens.source_name(),
        ),
        local_source_spans: HashMap::new(),
        precondition_source_spans: Vec::new(),
    })
}

fn parse_test_declaration(tokens: &mut TokenCursor) -> anyhow::Result<TestDecl> {
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

    let body = parse_braced_block(tokens, None, "", local_statement_segment)?;
    Ok(TestDecl { name, body })
}

fn parse_namespace_declaration(tokens: &mut TokenCursor) -> anyhow::Result<Vec<Function>> {
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

    consume_newlines(tokens);
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
            Some(TokenData::Word(name)) if name == "comptime" => match tokens.get(1) {
                Some(TokenData::Word(next)) if next == "fun" => {
                    let mut function = parse_function_declaration(tokens, true)?;
                    function.name = qualify_namespace_function_name(&namespace, &function.name);
                    functions.push(function);
                }
                _ => {
                    return Err(anyhow::anyhow!(
                        "namespace {} only supports `fun`, `comptime fun`, and `extern fun` declarations in v1",
                        namespace
                    ));
                }
            },
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

fn parse_type_reference(tokens: &mut TokenCursor) -> anyhow::Result<String> {
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

fn parse_bracketed_type_argument_list(tokens: &mut TokenCursor) -> anyhow::Result<Vec<String>> {
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

fn parse_generic_params(tokens: &mut TokenCursor) -> anyhow::Result<Vec<GenericParam>> {
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

fn parse_invariant_name_components(
    tokens: &mut TokenCursor,
) -> anyhow::Result<(Option<String>, String)> {
    match tokens.remove(0) {
        TokenData::String(display_name) => Ok((None, display_name)),
        TokenData::Word(identifier) => match tokens.remove(0) {
            TokenData::String(display_name) => Ok((Some(identifier), display_name)),
            token => Err(anyhow::anyhow!(
                "expected invariant display name string after identifier, got {:?}",
                token
            )),
        },
        token => Err(anyhow::anyhow!(
            "expected invariant display name string or identifier, got {:?}",
            token
        )),
    }
}

fn parse_grouped_struct_invariant_declarations(
    tokens: &mut TokenCursor,
) -> anyhow::Result<Vec<StructInvariantDecl>> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("for".to_string()),
        "expected 'for' after 'invariant' in grouped declaration"
    );
    let parameters = parse_parameter_list(tokens)?;
    anyhow::ensure!(
        !parameters.is_empty(),
        "invariant requires at least one parameter"
    );
    consume_newlines(tokens);
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '{',
                is_opening: true
            },
        "expected '{{' after grouped invariant header"
    );

    let mut out = vec![];
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
            Some(TokenData::Word(name)) if name == "invariant" => {
                return Err(anyhow::anyhow!(
                    "grouped invariant clauses do not use the inner 'invariant' keyword"
                ));
            }
            Some(_) => {
                let start = tokens.current_token_span();
                let (identifier, display_name) = parse_invariant_name_components(tokens)?;
                let mut recorder = LocalSourceRecorder::default();
                let body = parse_function_like_body(tokens, Some(&mut recorder))?;
                out.push(StructInvariantDecl {
                    identifier,
                    display_name,
                    parameters: parameters.clone(),
                    body,
                    source_span: compose_source_span(
                        start,
                        tokens.last_removed_source_span(),
                        tokens.source_name(),
                    ),
                    local_source_spans: recorder.local_source_spans,
                });
            }
            None => {
                return Err(anyhow::anyhow!(
                    "unexpected end of file in grouped invariant declaration"
                ));
            }
        }
    }

    anyhow::ensure!(
        !out.is_empty(),
        "expected at least one invariant clause in grouped declaration"
    );
    Ok(out)
}

fn parse_struct_invariant_declarations(
    tokens: &mut TokenCursor,
) -> anyhow::Result<Vec<StructInvariantDecl>> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("invariant".to_string()),
        "expected 'invariant' keyword"
    );

    if tokens.first() == Some(&TokenData::Word("for".to_string())) {
        return parse_grouped_struct_invariant_declarations(tokens);
    }

    let start = tokens.current_token_span();
    let (identifier, display_name) = parse_invariant_name_components(tokens)?;

    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("for".to_string()),
        "expected 'for' after invariant name"
    );
    let parameters = parse_parameter_list(tokens)?;
    anyhow::ensure!(
        !parameters.is_empty(),
        "invariant requires at least one parameter"
    );
    let mut recorder = LocalSourceRecorder::default();
    let body = parse_function_like_body(tokens, Some(&mut recorder))?;

    Ok(vec![StructInvariantDecl {
        identifier,
        display_name,
        parameters,
        body,
        source_span: compose_source_span(
            start,
            tokens.last_removed_source_span(),
            tokens.source_name(),
        ),
        local_source_spans: recorder.local_source_spans,
    }])
}

fn parse_comptime_apply(tokens: &mut TokenCursor) -> anyhow::Result<ComptimeApply> {
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
pub fn parse(tokens: TokenList) -> anyhow::Result<Ast> {
    let mut tokens = TokenCursor::new(tokens);
    // Discard all comments.
    tokens.retain(|token| !matches!(token, TokenData::Comment(_)));

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

    while let Some(token) = tokens.first() {
        match token {
            TokenData::Word(name) if name == "struct" => {
                let type_definition = parse_struct_declaration(&mut tokens)?;
                ast.type_definitions
                    .push(TypeDefDecl::Struct(type_definition));
            }
            TokenData::Word(name) if name == "enum" => {
                let type_definition = parse_enum_declaration(&mut tokens)?;
                ast.type_definitions
                    .push(TypeDefDecl::Enum(type_definition));
            }
            TokenData::Word(name) if name == "fun" => {
                let function = parse_function_declaration(&mut tokens, false)?;
                ast.top_level_functions.push(function);
            }
            TokenData::Word(name) if name == "extern" => {
                let function = parse_extern_function_declaration(&mut tokens)?;
                ast.top_level_functions.push(function);
            }
            TokenData::Word(name) if name == "test" => {
                let test = parse_test_declaration(&mut tokens)?;
                ast.tests.push(test);
            }
            TokenData::Word(name) if name == "comptime" => match tokens.get(1) {
                Some(TokenData::Word(kind)) if kind == "fun" => {
                    let function = parse_function_declaration(&mut tokens, true)?;
                    ast.top_level_functions.push(function);
                }
                Some(TokenData::Word(kind)) if kind == "apply" => {
                    let apply = parse_comptime_apply(&mut tokens)?;
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
                let invariants = parse_struct_invariant_declarations(&mut tokens)?;
                ast.invariants.extend(invariants);
            }
            TokenData::Word(name) if name == "generic" => {
                let generic = parse_generic_declaration(&mut tokens)?;
                ast.generic_definitions.push(generic);
            }
            TokenData::Word(name) if name == "namespace" => {
                let functions = parse_namespace_declaration(&mut tokens)?;
                ast.top_level_functions.extend(functions);
            }
            TokenData::Word(name) if name == "specialize" => {
                let specialization = parse_generic_specialization(&mut tokens)?;
                ast.generic_specializations.push(specialization);
            }
            TokenData::Word(name) if name == "trait" => {
                let trait_decl = parse_trait_declaration(&mut tokens)?;
                ast.trait_declarations.push(trait_decl);
            }
            TokenData::Word(name) if name == "impl" => {
                let impl_decl = parse_impl_declaration(&mut tokens)?;
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
                let import = parse_import_declaration(&mut tokens)?;
                ast.imports.push(import);
            }
            TokenData::Newline => {
                tokens.remove(0);
            }
            _ => return Err(anyhow::anyhow!("unexpected token {:?}", token)),
        }
    }

    Ok(ast)
}

fn parse_import_declaration(tokens: &mut TokenCursor) -> anyhow::Result<ImportDecl> {
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

fn parse_struct_value_node(
    tokens: &mut TokenCursor,
    struct_name: String,
    start: Option<TokenSpan>,
) -> anyhow::Result<ParsedExpressionNode> {
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

    consume_newlines(tokens);
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
    let mut children = vec![];
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

        let field_index = fields.len();
        let node = parse_expression_node(tokens, 0)?;
        let field_segment = struct_field_segment(AstPathStyle::Ir, field_index, &field_name);
        fields.push((field_name, node.expression.clone()));
        children.push((field_segment, node));

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

    let mut node = ParsedExpressionNode::new(
        Expression::StructValue {
            struct_name,
            field_values: fields,
        },
        compose_source_span(
            start,
            tokens.last_removed_source_span(),
            tokens.source_name(),
        ),
    );
    node.children = children;
    Ok(node)
}

fn parse_call_arg_nodes(tokens: &mut TokenCursor) -> anyhow::Result<Vec<ParsedExpressionNode>> {
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
                let expr = parse_expression_node(tokens, 0)?;
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

#[allow(dead_code)]
fn parse_call_args(
    tokens: &mut TokenCursor,
    mut recorder: Option<&mut LocalSourceRecorder>,
    expression_path: &str,
    arg_prefix: &str,
) -> anyhow::Result<Vec<Expression>> {
    let nodes = parse_call_arg_nodes(tokens)?;
    if let Some(recorder) = recorder.as_deref_mut() {
        for (index, node) in nodes.iter().enumerate() {
            record_expression_node(
                recorder,
                &join_path(
                    expression_path,
                    &format!("{arg_prefix}.{index}"),
                    AstPathStyle::Ir,
                ),
                node,
            );
        }
    }
    Ok(nodes.into_iter().map(|node| node.expression).collect())
}

fn parse_match_expression_node(
    tokens: &mut TokenCursor,
    start: Option<TokenSpan>,
) -> anyhow::Result<ParsedExpressionNode> {
    let subject = parse_expression_node(tokens, 0)?;
    consume_newlines(tokens);
    anyhow::ensure!(
        tokens.remove(0)
            == TokenData::Parenthesis {
                opening: '{',
                is_opening: true
            },
        "expected opening brace after match subject"
    );

    let mut arms = vec![];
    let mut children = vec![("match.subject".to_string(), subject.clone())];
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
                let arm_index = arms.len();
                let value = parse_expression_node(tokens, 0)?;
                children.push((
                    match_arm_expression_segment(AstPathStyle::Ir, arm_index),
                    value.clone(),
                ));
                arms.push(MatchExprArm {
                    pattern,
                    value: value.expression,
                });

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
    let mut node = ParsedExpressionNode::new(
        Expression::Match {
            subject: Box::new(subject.expression),
            arms,
        },
        compose_source_span(
            start,
            tokens.last_removed_source_span(),
            tokens.source_name(),
        ),
    );
    node.children = children;
    Ok(node)
}

fn parse_atom_node(tokens: &mut TokenCursor) -> anyhow::Result<ParsedExpressionNode> {
    if tokens.is_empty() {
        return Err(anyhow::anyhow!(
            "unexpected end of file while parsing expression"
        ));
    }
    let start = tokens.current_token_span();
    let next = tokens.remove(0);
    match next {
        TokenData::Symbols(s) if s == "!" => {
            let rhs = parse_expression_node(tokens, u8::MAX)?;
            let rhs_expression = rhs.expression.clone();
            let mut node = ParsedExpressionNode::new(
                Expression::UnaryOp(UnaryOp::Not, Box::new(rhs_expression)),
                compose_source_span(
                    start,
                    tokens.last_removed_source_span(),
                    tokens.source_name(),
                ),
            );
            node.children
                .push((unary_segment(AstPathStyle::Ir).to_string(), rhs));
            Ok(node)
        }
        TokenData::Number(n) => Ok(ParsedExpressionNode::new(
            Expression::Literal(Literal::Int(n)),
            compose_source_span(
                start,
                tokens.last_removed_source_span(),
                tokens.source_name(),
            ),
        )),
        TokenData::Float(value) => {
            if let Some(TokenData::Word(suffix)) = tokens.first() {
                if suffix == "f64" {
                    tokens.remove(0);
                    return Ok(ParsedExpressionNode::new(
                        Expression::Literal(Literal::Float64(value)),
                        compose_source_span(
                            start,
                            tokens.last_removed_source_span(),
                            tokens.source_name(),
                        ),
                    ));
                }
                if suffix == "f32" {
                    tokens.remove(0);
                    return Ok(ParsedExpressionNode::new(
                        Expression::Literal(Literal::Float32(value)),
                        compose_source_span(
                            start,
                            tokens.last_removed_source_span(),
                            tokens.source_name(),
                        ),
                    ));
                }
            }
            Ok(ParsedExpressionNode::new(
                Expression::Literal(Literal::Float32(value)),
                compose_source_span(
                    start,
                    tokens.last_removed_source_span(),
                    tokens.source_name(),
                ),
            ))
        }
        TokenData::Char(value) => Ok(ParsedExpressionNode::new(
            Expression::Call(
                qualify_namespace_function_name("Char", "from_code"),
                vec![Expression::Literal(Literal::Int(value as u32))],
            ),
            compose_source_span(
                start,
                tokens.last_removed_source_span(),
                tokens.source_name(),
            ),
        )),
        TokenData::String(s) => Ok(ParsedExpressionNode::new(
            Expression::Literal(Literal::String(s)),
            compose_source_span(
                start,
                tokens.last_removed_source_span(),
                tokens.source_name(),
            ),
        )),
        TokenData::Word(s) => {
            if s == "match" {
                return parse_match_expression_node(tokens, start);
            }
            if s == "true" {
                return Ok(ParsedExpressionNode::new(
                    Expression::Literal(Literal::Bool(true)),
                    compose_source_span(
                        start,
                        tokens.last_removed_source_span(),
                        tokens.source_name(),
                    ),
                ));
            }
            if s == "false" {
                return Ok(ParsedExpressionNode::new(
                    Expression::Literal(Literal::Bool(false)),
                    compose_source_span(
                        start,
                        tokens.last_removed_source_span(),
                        tokens.source_name(),
                    ),
                ));
            }
            if tokens.get(0) == Some(&TokenData::Word("struct".to_string())) {
                parse_struct_value_node(tokens, s, start)
            } else {
                Ok(ParsedExpressionNode::new(
                    Expression::Variable(s),
                    compose_source_span(
                        start,
                        tokens.last_removed_source_span(),
                        tokens.source_name(),
                    ),
                ))
            }
        }
        TokenData::Parenthesis {
            opening: '(',
            is_opening: true,
        } => {
            let mut expr = parse_expression_node(tokens, 0)?;
            anyhow::ensure!(
                tokens.remove(0)
                    == TokenData::Parenthesis {
                        opening: ')',
                        is_opening: false
                    }
            );
            expr.span = compose_source_span(
                start,
                tokens.last_removed_source_span(),
                tokens.source_name(),
            );
            Ok(expr)
        }
        t => Err(anyhow::anyhow!("expected a value, got {:?}", t)),
    }
}

#[allow(dead_code)]
fn parse_expression(tokens: &mut TokenCursor, min_precedence: u8) -> anyhow::Result<Expression> {
    parse_expression_with_path(tokens, min_precedence, None, "")
}

fn parse_expression_with_path(
    tokens: &mut TokenCursor,
    min_precedence: u8,
    mut recorder: Option<&mut LocalSourceRecorder>,
    expression_path: &str,
) -> anyhow::Result<Expression> {
    let node = parse_expression_node(tokens, min_precedence)?;
    if let Some(recorder) = recorder.as_deref_mut() {
        record_expression_node(recorder, expression_path, &node);
    }
    Ok(node.expression)
}

fn parse_expression_node(
    tokens: &mut TokenCursor,
    min_precedence: u8,
) -> anyhow::Result<ParsedExpressionNode> {
    trace!(?tokens, "Parsing expression");
    let start = tokens.current_token_span();

    let mut lhs = parse_atom_node(tokens)?;

    loop {
        match tokens.get(0) {
            Some(TokenData::Symbols(s)) if s == "." => {
                trace!("Parsing field access or method call {:?}", lhs.expression);
                tokens.remove(0); // Consume '.'
                let field_token = if tokens.is_empty() {
                    return Err(anyhow::anyhow!(
                        "unexpected end of file after '.' in expression"
                    ));
                } else {
                    tokens.remove(0)
                };
                let field_name = expect_identifier(field_token)?;
                if matches!(
                    tokens.get(0),
                    Some(TokenData::Parenthesis {
                        opening: '(',
                        is_opening: true
                    })
                ) {
                    let arg_nodes = parse_call_arg_nodes(tokens)?;
                    let mut children = vec![("method.receiver".to_string(), lhs.clone())];
                    let args = arg_nodes
                        .into_iter()
                        .enumerate()
                        .map(|(index, node)| {
                            children.push((format!("method.arg.{index}"), node.clone()));
                            node.expression
                        })
                        .collect();
                    lhs = ParsedExpressionNode {
                        expression: Expression::MethodCall {
                            receiver: Box::new(lhs.expression),
                            method: field_name,
                            args,
                        },
                        span: compose_source_span(
                            start.clone(),
                            tokens.last_removed_source_span(),
                            tokens.source_name(),
                        ),
                        children,
                    };
                    continue;
                }
                let struct_variable = match lhs.expression {
                    Expression::Variable(s) => s,
                    other => {
                        return Err(anyhow::anyhow!(
                            "expected variable before '.', got {:?}",
                            other
                        ))
                    }
                };
                lhs = ParsedExpressionNode::new(
                    Expression::FieldAccess {
                        struct_variable,
                        field: field_name,
                    },
                    compose_source_span(
                        start.clone(),
                        tokens.last_removed_source_span(),
                        tokens.source_name(),
                    ),
                );
                continue;
            }
            Some(TokenData::Parenthesis {
                opening: '(',
                is_opening: true,
            }) => {
                let arg_nodes = parse_call_arg_nodes(tokens)?;
                let args = arg_nodes
                    .iter()
                    .map(|node| node.expression.clone())
                    .collect::<Vec<_>>();
                let mut children = Vec::new();
                for (index, node) in arg_nodes.into_iter().enumerate() {
                    children.push((format!("call.arg.{index}"), node));
                }
                lhs = match lhs {
                    ParsedExpressionNode {
                        expression: Expression::Variable(name),
                        ..
                    } => ParsedExpressionNode {
                        expression: Expression::Call(name, args),
                        span: compose_source_span(
                            start.clone(),
                            tokens.last_removed_source_span(),
                            tokens.source_name(),
                        ),
                        children,
                    },
                    callee_node => {
                        let mut postfix_children =
                            vec![("postfix.callee".to_string(), callee_node.clone())];
                        for (index, (_, node)) in children.into_iter().enumerate() {
                            postfix_children.push((format!("postfix.arg.{index}"), node));
                        }
                        ParsedExpressionNode {
                            expression: Expression::PostfixCall {
                                callee: Box::new(callee_node.expression),
                                args,
                            },
                            span: compose_source_span(
                                start.clone(),
                                tokens.last_removed_source_span(),
                                tokens.source_name(),
                            ),
                            children: postfix_children,
                        }
                    }
                };
                continue;
            }
            Some(token) if token.is_op() => {
                let op = Op::from_token(token).unwrap();
                let precedence = op.precedence();
                if precedence >= min_precedence {
                    tokens.remove(0);
                    let rhs = parse_expression_node(tokens, precedence)?;
                    let left = lhs;
                    let left_expression = left.expression.clone();
                    let rhs_expression = rhs.expression.clone();
                    lhs = ParsedExpressionNode {
                        expression: Expression::BinOp(
                            op,
                            Box::new(left_expression),
                            Box::new(rhs_expression),
                        ),
                        span: compose_source_span(
                            start.clone(),
                            tokens.last_removed_source_span(),
                            tokens.source_name(),
                        ),
                        children: vec![
                            (bin_left_segment(AstPathStyle::Ir).to_string(), left),
                            (bin_right_segment(AstPathStyle::Ir).to_string(), rhs),
                        ],
                    };
                    continue;
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

fn parse_generic_declaration(tokens: &mut TokenCursor) -> anyhow::Result<GenericDef> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("generic".to_string()),
        "expected 'generic' keyword"
    );

    let name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        _ => return Err(anyhow::anyhow!("expected generic name")),
    };

    let params = parse_generic_params(tokens)?;

    consume_newlines(tokens);
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
    let mut generic_specializations = vec![];
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
            Some(TokenData::Word(name)) if name == "specialize" => {
                let specialization = parse_generic_specialization(tokens)?;
                generic_specializations.push(specialization);
            }
            Some(TokenData::Word(name)) if name == "extern" => {
                return Err(anyhow::anyhow!(
                    "generic body only supports `fun`, `comptime fun`, `specialize`, type declarations, and invariants in v1"
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
                let parsed = parse_struct_invariant_declarations(tokens)?;
                invariants.extend(parsed);
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
        generic_specializations,
        invariants,
    })
}

fn parse_generic_specialization(tokens: &mut TokenCursor) -> anyhow::Result<GenericSpecialization> {
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

fn parse_trait_method_signature(tokens: &mut TokenCursor) -> anyhow::Result<TraitMethodSig> {
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
    if tokens.first() == Some(&TokenData::Word("pre".to_string())) {
        return Err(anyhow::anyhow!(
            "trait method {} cannot use pre blocks in v1",
            name
        ));
    }
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

fn parse_trait_declaration(tokens: &mut TokenCursor) -> anyhow::Result<TraitDecl> {
    anyhow::ensure!(
        tokens.remove(0) == TokenData::Word("trait".to_string()),
        "expected 'trait' keyword"
    );
    let name = match tokens.remove(0) {
        TokenData::Word(name) => name,
        token => return Err(anyhow::anyhow!("expected trait name, got {:?}", token)),
    };
    consume_newlines(tokens);
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

fn parse_impl_declaration(tokens: &mut TokenCursor) -> anyhow::Result<ImplDecl> {
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
    consume_newlines(tokens);
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
    use super::parse;
    use crate::tokenizer::tokenize;

    #[test]
    fn parses_generic_with_bounds_and_specialization() {
        let source = r#"
generic HashMap[K: Hash + Equality, V] {
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
        assert!(generic.generic_specializations.is_empty());
        assert_eq!(generic.params[0].name, "K");
        assert_eq!(generic.params[0].bounds, vec!["Hash", "Equality"]);
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
    fn parses_local_specialization_in_generic_body() {
        let source = r#"
generic List[T] {
	struct List {
		value: T,
	}

	specialize MaybeValue = Option[T]

	fun wrap(value: T) -> MaybeValue {
		return MaybeValue.Some(value)
	}
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize generic source");
        let ast = parse(tokens).expect("parse generic source");

        assert_eq!(ast.generic_definitions.len(), 1);
        let generic = &ast.generic_definitions[0];
        assert_eq!(generic.generic_specializations.len(), 1);
        assert_eq!(generic.generic_specializations[0].alias, "MaybeValue");
        assert_eq!(generic.generic_specializations[0].generic_name, "Option");
        assert_eq!(
            generic.generic_specializations[0].concrete_types,
            vec!["T".to_string()]
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
    fn parses_enum_declaration_with_newlines_before_opening_brace() {
        let source = r#"
enum JsonKind

		{
	Object,
	Array,
	String,
	Number,
	Bool,
	Null,
	Invalid,
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize enum brace-gap source");
        let ast = parse(tokens).expect("parse enum brace-gap source");
        let super::TypeDefDecl::Enum(enum_def) = &ast.type_definitions[0] else {
            panic!("expected enum");
        };
        assert_eq!(enum_def.name, "JsonKind");
        assert_eq!(enum_def.variants.len(), 7);
        assert_eq!(enum_def.variants[0].name, "Object");
        assert_eq!(enum_def.variants[6].name, "Invalid");
    }

    #[test]
    fn parses_enum_declaration_with_colon_payload_and_unit_variant() {
        let source = r#"
enum ParseResult {
	Ok: I32,
	Err: ParseErr,
	UnitVariant,
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize enum payload source");
        let ast = parse(tokens).expect("parse enum payload source");
        let super::TypeDefDecl::Enum(enum_def) = &ast.type_definitions[0] else {
            panic!("expected enum");
        };
        assert_eq!(enum_def.name, "ParseResult");
        assert_eq!(enum_def.variants.len(), 3);
        assert_eq!(enum_def.variants[0].name, "Ok");
        assert_eq!(enum_def.variants[0].payload_ty.as_deref(), Some("I32"));
        assert_eq!(enum_def.variants[1].name, "Err");
        assert_eq!(enum_def.variants[1].payload_ty.as_deref(), Some("ParseErr"));
        assert_eq!(enum_def.variants[2].name, "UnitVariant");
        assert_eq!(enum_def.variants[2].payload_ty, None);
    }

    #[test]
    fn rejects_parenthesized_enum_payload_syntax_with_migration_hint() {
        let source = r#"
enum Option {
	None,
	Some(I32),
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize legacy enum payload source");
        let err = parse(tokens).expect_err("legacy enum payload syntax should fail");
        assert!(
            err.to_string().contains("enum payload syntax uses ':'"),
            "unexpected parse error: {err}"
        );
    }

    #[test]
    fn rejects_template_keyword_with_migration_hint() {
        let source = r#"
template Option[T] {
	enum Option {
		None,
		Some: T,
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
        assert_eq!(ast.invariants[0].parameters.len(), 1);
        assert_eq!(ast.invariants[0].parameters[0].name, "v");
        assert_eq!(ast.invariants[0].parameters[0].ty, "Counter");
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
    fn parses_grouped_struct_invariant_declarations() {
        let source = r#"
struct Counter {
	value: I32,
	max: I32,
}

invariant for (v: Counter) {
	non_negative_value "positive .value" {
		return v.value >= 0
	}

	"positive .max" {
		return v.max >= 0
	}
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize grouped invariant source");
        let ast = parse(tokens).expect("parse grouped invariant source");

        assert_eq!(ast.invariants.len(), 2);
        assert_eq!(
            ast.invariants[0].identifier.as_deref(),
            Some("non_negative_value")
        );
        assert_eq!(ast.invariants[0].display_name, "positive .value");
        assert_eq!(ast.invariants[0].parameters.len(), 1);
        assert_eq!(ast.invariants[0].parameters[0].name, "v");
        assert_eq!(ast.invariants[0].parameters[0].ty, "Counter");

        assert_eq!(ast.invariants[1].identifier, None);
        assert_eq!(ast.invariants[1].display_name, "positive .max");
        assert_eq!(ast.invariants[1].parameters.len(), 1);
        assert_eq!(ast.invariants[1].parameters[0].name, "v");
        assert_eq!(ast.invariants[1].parameters[0].ty, "Counter");
    }

    #[test]
    fn parses_multi_parameter_struct_invariant_declaration() {
        let source = r#"
struct Counter {
	value: I32,
}

invariant "counter add preserves ordering" for (lhs: Counter, rhs: Counter) {
	return lhs.value <= rhs.value
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize multi parameter invariant source");
        let ast = parse(tokens).expect("parse multi parameter invariant source");

        assert_eq!(ast.invariants.len(), 1);
        assert_eq!(ast.invariants[0].identifier, None);
        assert_eq!(
            ast.invariants[0].display_name,
            "counter add preserves ordering"
        );
        assert_eq!(ast.invariants[0].parameters.len(), 2);
        assert_eq!(ast.invariants[0].parameters[0].name, "lhs");
        assert_eq!(ast.invariants[0].parameters[0].ty, "Counter");
        assert_eq!(ast.invariants[0].parameters[1].name, "rhs");
        assert_eq!(ast.invariants[0].parameters[1].ty, "Counter");
    }

    #[test]
    fn rejects_struct_invariant_declaration_without_parameters() {
        let source = r#"
struct Counter {
	value: I32,
}

invariant "counter value must be non-negative" for () {
	return true
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize missing parameter invariant source");
        let err = parse(tokens).expect_err("missing invariant parameters should fail");
        assert!(err
            .to_string()
            .contains("invariant requires at least one parameter"));
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
        assert_eq!(generic.invariants[0].parameters.len(), 1);
        assert_eq!(generic.invariants[0].parameters[0].ty, "Box");
    }

    #[test]
    fn parses_grouped_generic_struct_invariant_declaration() {
        let source = r#"
generic Box[T] {
	struct Box {
		value: T,
	}

	invariant for (v: Box) {
		"value must be valid" {
			return true
		}
	}
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize grouped generic invariant source");
        let ast = parse(tokens).expect("parse grouped generic invariant source");

        assert_eq!(ast.generic_definitions.len(), 1);
        let generic = &ast.generic_definitions[0];
        assert_eq!(generic.invariants.len(), 1);
        assert_eq!(generic.invariants[0].identifier, None);
        assert_eq!(generic.invariants[0].display_name, "value must be valid");
        assert_eq!(generic.invariants[0].parameters.len(), 1);
        assert_eq!(generic.invariants[0].parameters[0].name, "v");
        assert_eq!(generic.invariants[0].parameters[0].ty, "Box");
    }

    #[test]
    fn parses_grouped_multi_parameter_struct_invariant_declarations() {
        let source = r#"
struct Counter {
	value: I32,
}

invariant for (lhs: Counter, rhs: Counter) {
	"counter pair ordering" {
		return lhs.value <= rhs.value
	}
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize grouped multi parameter invariant source");
        let ast = parse(tokens).expect("parse grouped multi parameter invariant source");

        assert_eq!(ast.invariants.len(), 1);
        assert_eq!(ast.invariants[0].display_name, "counter pair ordering");
        assert_eq!(ast.invariants[0].parameters.len(), 2);
        assert_eq!(ast.invariants[0].parameters[0].name, "lhs");
        assert_eq!(ast.invariants[0].parameters[1].name, "rhs");
    }

    #[test]
    fn parses_generic_multi_parameter_struct_invariant_declaration() {
        let source = r#"
generic Pair[T] {
	struct Pair {
		left: T,
		right: T,
	}

	invariant "pair equality is reflexive" for (lhs: Pair, rhs: Pair) {
		return true
	}
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize generic multi parameter invariant source");
        let ast = parse(tokens).expect("parse generic multi parameter invariant source");

        assert_eq!(ast.generic_definitions.len(), 1);
        let generic = &ast.generic_definitions[0];
        assert_eq!(generic.invariants.len(), 1);
        assert_eq!(generic.invariants[0].parameters.len(), 2);
        assert_eq!(generic.invariants[0].parameters[0].ty, "Pair");
        assert_eq!(generic.invariants[0].parameters[1].ty, "Pair");
    }

    #[test]
    fn rejects_grouped_invariant_clause_without_display_name() {
        let source = r#"
struct Counter {
	value: I32,
}

invariant for (v: Counter) {
	missing_display {
		return v.value >= 0
	}
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize invalid grouped invariant source");
        let err = parse(tokens).expect_err("missing display string should fail");
        assert!(err
            .to_string()
            .contains("expected invariant display name string after identifier"));
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
    fn parses_function_preconditions() {
        let source = r#"
fun clamp(v: I32) -> I32 pre {
	v >= 0
	v <= 10
} {
	return v
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");
        let function = &ast.top_level_functions[0];
        assert_eq!(function.preconditions.len(), 2);
    }

    #[test]
    fn parses_function_preconditions_ast_snapshot() {
        let source = r#"
fun clamp(v: I32) -> I32 pre {
	v >= 0
	v <= 10
} {
	return v
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");
        insta::assert_json_snapshot!("parser_function_preconditions_ast", ast);
    }

    #[test]
    fn rejects_empty_precondition_block() {
        let source = r#"
fun clamp(v: I32) -> I32 pre {
} {
	return v
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let err = parse(tokens).expect_err("empty pre block must fail");
        assert!(
            err.to_string()
                .contains("expected at least one precondition clause in pre block"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn rejects_extern_function_preconditions() {
        let source = r#"
extern fun clamp(v: I32) -> I32 pre {
	v >= 0
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let err = parse(tokens).expect_err("extern pre block must fail");
        assert!(
            err.to_string()
                .contains("extern function clamp cannot use pre blocks in v1"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn parses_comptime_function_preconditions() {
        let source = r#"
comptime fun clamp(v: I32) -> I32 pre {
	v >= 0
} {
	return v
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("comptime pre block should parse");
        assert_eq!(ast.top_level_functions.len(), 1);
        let clamp = &ast.top_level_functions[0];
        assert!(clamp.is_comptime);
        assert_eq!(clamp.preconditions.len(), 1);
    }

    #[test]
    fn rejects_trait_method_preconditions() {
        let source = r#"
trait Clamp {
	fun clamp(v: I32) -> I32 pre {
		v >= 0
	}
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let err = parse(tokens).expect_err("trait method pre block must fail");
        assert!(
            err.to_string()
                .contains("trait method clamp cannot use pre blocks in v1"),
            "unexpected error: {err}"
        );
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
	return DeclSet.new()
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
        let super::Expression::MethodCall {
            receiver,
            method,
            args,
        } = expr
        else {
            panic!("expected method call for namespaced call syntax");
        };
        let super::Expression::Variable(receiver_name) = receiver.as_ref() else {
            panic!("expected variable receiver in namespaced call syntax");
        };
        assert_eq!(receiver_name, "Option");
        assert_eq!(method, "is_some");
        assert_eq!(args.len(), 1);
    }

    #[test]
    fn parses_method_call_on_temporary_receiver() {
        let source = r#"
struct Counter {
	value: I32,
}

fun make_counter() -> Counter {
	return Counter struct { value: 7 }
}

fun main() -> I32 {
	return (make_counter()).next()
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");

        let main = &ast.top_level_functions[1];
        let super::Statement::Return { expr } = &main.body[0] else {
            panic!("expected return statement");
        };
        let super::Expression::MethodCall {
            receiver,
            method,
            args,
        } = expr
        else {
            panic!("expected method call");
        };
        assert!(matches!(receiver.as_ref(), super::Expression::Call(_, _)));
        assert_eq!(method, "next");
        assert!(args.is_empty());
    }

    #[test]
    fn parses_chained_method_calls() {
        let source = r#"
fun main() -> I32 {
	return start().step().finish()
}
        "#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("parse source");

        let main = &ast.top_level_functions[0];
        let super::Statement::Return { expr } = &main.body[0] else {
            panic!("expected return statement");
        };
        let super::Expression::MethodCall {
            receiver,
            method,
            args,
        } = expr
        else {
            panic!("expected outer method call");
        };
        assert_eq!(method, "finish");
        assert!(args.is_empty());
        assert!(matches!(
            receiver.as_ref(),
            super::Expression::MethodCall { .. }
        ));
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
    fn parses_comptime_function_inside_namespace() {
        let source = r#"
namespace Option {
	comptime fun bad(v: I32) -> I32 {
		return v
	}
}
"#
        .to_string();

        let tokens = tokenize(source).expect("tokenize source");
        let ast = parse(tokens).expect("namespace comptime function should parse");
        assert_eq!(ast.top_level_functions.len(), 1);
        let function = &ast.top_level_functions[0];
        assert_eq!(function.name, "Option__bad");
        assert!(function.is_comptime);
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
            err.to_string()
                .contains("unexpected end of file in function body"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn parses_std_json_module() {
        let source = std::fs::read_to_string("src/std/std_json.oa")
            .expect("read std_json module for parser regression");
        let tokens = tokenize(source).expect("tokenize std_json module");
        parse(tokens).expect("parse std_json module");
    }
}
