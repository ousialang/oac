// cst.rs
// ======
//
// An incremental parser that builds the Concrete Syntax Tree (CST) of some source.

use std::collections::LinkedList;
use std::fs::File;
use std::io::prelude::*;
use std::iter::Peekable;
use std::ops::Range;
use std::path::PathBuf;
use std::str::Chars;

#[derive(Debug)]
pub struct Cst {
    source: String,
    tree: LinkedList<Token>,
    feedbacks: Vec<String>,
}

#[derive(Debug)]
pub struct Token {
    location: Range<u64>,
    kind: TokenKind,
}

#[derive(Debug)]
pub enum TokenKind {
    NestedScope(NestedScope),
    Number(Number),
    Literal(Literal),
    Word,
    Symbol,
}

#[derive(Debug)]
pub struct NestedScope {
    bracket: Bracket,
    contents: Vec<Token>,
}

#[derive(Debug)]
pub enum Bracket {
    Round,
    Square,
    Curly,
}

#[derive(Debug)]
pub struct Number {
    buffer: String,
}

#[derive(Debug)]
pub struct Literal {
    true_str: String,
}

impl Cst {
    pub fn new() -> Cst {
        Cst {
            tokens: LinkedList::new(),
        }
    }

    pub fn from_string(src: &str) -> Option<Cst> {
        let mut parser = Parser::new();
        // TODO: create warnings when src is empty
        if src.is_empty() {
            return (parser.ast, parser.feedbacks);
        }
        let mut chars = src.chars().peekable();
        loop {
            match parser.peek_position(&mut chars) {
                Position::Whitespace(ref mut s) => parser.parse_whitespace(s.chars),
                Position::Symbol(ref mut s) => parser.parse_symbol(s.chars),
                Position::Word(ref mut s) => parser.parse_word(s.chars),
                Position::String(ref mut s) => parser.parse_string(s.chars),
                Position::Number(ref mut s) => parser.parse_number(s.chars),
                Position::LBracket(ref mut s) => parser.parse_opening_bracket(s.chars),
                Position::RBracket(ref mut s) => parser.parse_closing_bracket(s.chars),
                Position::EOF => {
                    parser.terminate();
                    break;
                }
                _ => println!("bvvzxcvxzc"),
            }
        }
        parser.ast
    }

    pub fn from_file(path: PathBuf) -> Option<Ast> {
        let mut buffer = String::new();
        File::open(path).unwrap().read_to_string(&mut buffer);
        Ast::from_string(buffer.as_str())
    }

    fn add_token(&mut self, t: Token) {
        self.tokens.push(t);
    }
}

enum Position<'a> {
    Whitespace(WithChars<'a>),
    String(WithChars<'a>),
    Number(WithChars<'a>),
    Word(WithChars<'a>),
    Symbol(WithChars<'a>),
    EOF,
    Unknown(WithChars<'a>),
    LBracket(WithChars<'a>),
    RBracket(WithChars<'a>),
}

struct WithChars<'a> {
    chars: &'a Peekable<Chars<'a>>,
}
