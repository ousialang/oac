use utils::chars::CharUtils;
use utils::feedback::Feedback;

use std::collections::LinkedList;
use std::fs::File;
use std::io::prelude::*;
use std::iter::Peekable;
use std::ops::Range;
use std::path::PathBuf;
use std::str::Chars;


#[derive(Debug)]
pub struct Ast {
    tokens: Vec<Token>,
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


type ParserResult = (Option<Ast>, Vec<Feedback>);


impl Ast {
    pub fn new() -> Ast {
        Ast { tokens: Vec::new() }
    }

    pub fn from_string(src: &str) -> ParserResult {
        let mut parser = Parser::new();
        if src.is_empty() {
            return (parser.ast, parser.feedbacks); // TODO warning
        }
        let mut chars = src.chars().peekable();
        while chars.peek().is_some() {
            let c = chars.peek().unwrap().clone();
            if c.is_whitespace() {
                //parser.parse_whitespace(chars);
            } else if c.is_symbol() {
                parser.parse_symbol(&mut chars);
            } else if c.is_alphabetic() {
                parser.parse_word(&mut chars);
            } else if c == '"' {
                parser.parse_string(&mut chars);
            } else if c.is_digit(10) {
                parser.parse_number(&mut chars);
            } else {
                println!("{}", chars.next().unwrap());
            }
        }
        (parser.ast, parser.feedbacks)
    }

    pub fn from_file(path: PathBuf) -> ParserResult {
        let mut buffer = String::new();
        File::open(path).unwrap().read_to_string(&mut buffer);
        Ast::from_string(buffer.as_str())
    }

    fn add_token(&mut self, t: Token) {
        self.tokens.push(t);
    }
}


struct Parser {
    ast: Option<Ast>,
    feedbacks: Vec<Feedback>,
    pedigree_of_current_scope: String,
    buffer: String,
    flag: bool,
}

impl Parser {
    fn new() -> Parser {
        Parser {
            ast: Some(Ast::new()),
            feedbacks: Vec::new(),
            pedigree_of_current_scope: String::new(),
            buffer: String::new(),
            flag: false,
        }
    }

    fn parse_word(&mut self, chars: &mut Peekable<Chars>) {
        loop {
            let opt_c = chars.peek();
            match opt_c {
                Some(c) => {
                    if c.is_alphabetic() {
                        self.buffer.push(*c);
                    } else {
                        break;
                    }
                }
                None => break,
            }
        }
    }

    fn parse_symbol(&mut self, chars: &mut Peekable<Chars>) {
        loop {
            let opt_c = chars.peek();
            match opt_c {
                Some(c) => {
                    if c.is_symbol() {
                        self.buffer.push(*c);
                    } else {
                        break;
                    }
                }
                None => break,
            }
        }
    }

    fn parse_number(&mut self, chars: &mut Peekable<Chars>) {
        loop {
            match chars.next() {
                Some(c) => {
                    if c.is_digit(10) {
                        self.buffer.push(c);
                    } else {
                        self.add_token(Token {
                            location: Range { start: 0, end: 1 },
                            kind: TokenKind::Number(Number { buffer: "abc".to_owned() }),
                        });
                        break;
                    }
                }
                None => break,
            }
        }
    }

    fn parse_string(&mut self, chars: &mut Peekable<Chars>) {
        loop {
            match chars.next() {
                Some(c) => {
                    if self.flag {
                        self.buffer.push(c);
                    } else if c == '"' {
                        break;
                    } else if c == '/' {
                        self.flag = true;
                    } else {
                        self.buffer.push(c);
                    }
                }
                None => {
                    self.flag = true;
                }
            }
        }
    }

    fn parse_opening_bracket(&mut self, chars: &mut Peekable<Chars>) {
        match chars.next() {
            Some(c) => {
                self.pedigree_of_current_scope.push(c);
            }
            None => (),
        }
    }

    fn parse_closing_bracket(&mut self, chars: &mut Peekable<Chars>) {
        match chars.next() {
            Some(c_right) => {
                match self.pedigree_of_current_scope.pop() {
                    Some(c_left) => (),
                    None => (), // TODO
                }
            }
            None => (),
        }
    }

    fn add_token(&mut self, t: Token) {}
}
