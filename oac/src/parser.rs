use super::lexer::TokenList;

#[derive(Debug)]
pub struct SyntaxTree {
    nodes: Vec<SyntaxNode>,
}

#[derive(Debug)]
pub enum SyntaxNode {
    Constant {
        identifier: String,
        typ: String,
        value: String,
    },
    Variable {
        identifier: String,
        typ: String,
        value: String,
    },
    SetValue {
        identifier: String,
        value: String,
    },
    Print {
        identifire: String,
    },
}

pub fn parse(tokens: TokenList) -> AST {}
