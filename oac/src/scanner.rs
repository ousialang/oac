use std::iter::Peekable;
use std::path::PathBuf;
use std::str::Chars;

#[derive(Debug)]
pub struct TokenList {
    original_source: String,
    tokens: Vec<Token>,
}

#[derive(Debug)]
pub enum Token {
    Parenthesis { opening: char, is_opening: bool },
    Number(u32),
    String(String),
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

#[derive(Debug)]
pub struct Position {
    pub path: Option<PathBuf>,
    pub absolute_i: u32,
    pub line: u32,
    pub column: u32,
}

impl Position {
    pub fn advance(&mut self, c: char) {
        self.absolute_i += 1;
        self.column += 1;
        if c == '\n' {
            self.line += 1;
            self.column = 1;
        }
    }
}

impl Default for Position {
    fn default() -> Self {
        Self {
            path: None,
            absolute_i: 1,
            line: 1,
            column: 1,
        }
    }
}

pub fn scan(s: String) -> Result<TokenList, String> {
    let s_cloned = s.clone();
    let mut chars = s_cloned.chars().peekable();
    let mut tokens = TokenList {
        original_source: s,
        tokens: vec![],
    };
    let mut position = Position::default();
    while let Some(c) = chars.next() {
        if c == '"' {
            let mut string = String::new();
            while chars.peek().is_some() && *chars.peek().unwrap() != '"' {
                let c = chars.next().unwrap();
                string.push(c);
            }
            if chars.peek().is_some() {
                chars.next();
            }
            tokens.tokens.push(Token::String(string));
        } else if c.is_digit(10) {
            let mut number = c.to_digit(10).unwrap();
            while chars.peek().is_some() && chars.peek().unwrap().is_digit(10) {
                let c = chars.next().unwrap();
                let digit = c.to_digit(10).unwrap();
                number = number * 10 + digit;
            }
            tokens.tokens.push(Token::Number(number))
        } else if c.is_ascii_whitespace() {
        } else {
            return Err(format!("Syntax error at position {:?}", position));
        }
        position.advance(c);
    }
    Ok(tokens)
}

//enum Position<'a> {
//    Whitespace(WithChars<'a>),
//    String(WithChars<'a>),
//    Number(WithChars<'a>),
//    Word(WithChars<'a>),
//    Symbol(WithChars<'a>),
//    EOF,
//    Unknown(WithChars<'a>),
//    LBracket(WithChars<'a>),
//    RBracket(WithChars<'a>),
//}

struct WithChars<'a> {
    chars: &'a Peekable<Chars<'a>>,
}
