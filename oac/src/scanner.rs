use std::path::PathBuf;

#[derive(Debug)]
pub struct TokenList {
    pub tokens: Vec<Token>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    Newline,
    Parenthesis { opening: char, is_opening: bool },
    Number(u32),
    String(String),
    Word(String),
    Symbols(String),
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
    let mut tokens = TokenList { tokens: vec![] };
    let mut position = Position::default();
    while let Some(c) = chars.next() {
        if "([{".contains(c) {
            tokens.tokens.push(Token::Parenthesis {
                opening: c,
                is_opening: true,
            });
        } else if ")]}".contains(c) {
            tokens.tokens.push(Token::Parenthesis {
                opening: c,
                is_opening: false,
            });
        } else if c == '/' && chars.peek() == Some(&'/') {
            while chars.peek().is_some() && *chars.peek().unwrap() != '\n' {
                chars.next().unwrap();
            }
        } else if c == '"' {
            let mut string = String::new();
            while chars.peek().is_some() && *chars.peek().unwrap() != '"' {
                let c = chars.next().unwrap();
                string.push(c);
            }
            if chars.peek().is_some() {
                chars.next();
            }
            tokens.tokens.push(Token::String(string));
        } else if "*@%=,".contains(c) {
            let mut symbols = String::new();
            symbols.push(c);
            while chars.peek().is_some() && "*@=&,".contains(*chars.peek().unwrap()) {
                let c = chars.next().unwrap();
                symbols.push(c);
            }
            tokens.tokens.push(Token::Symbols(symbols));
        } else if c.is_ascii_digit() {
            let mut number = c.to_digit(10).unwrap();
            while chars.peek().is_some() && chars.peek().unwrap().is_digit(10) {
                let c = chars.next().unwrap();
                let digit = c.to_digit(10).unwrap();
                number = number * 10 + digit;
            }
            tokens.tokens.push(Token::Number(number))
        } else if c == '\n' {
            tokens.tokens.push(Token::Newline);
        } else if c.is_ascii_whitespace() {
        } else if c.is_ascii_alphabetic() {
            let mut word = String::new();
            word.push(c);
            while chars.peek().is_some() && chars.peek().unwrap().is_ascii_alphanumeric() {
                let c = chars.next().unwrap();
                word.push(c);
            }
            tokens.tokens.push(Token::Word(word));
        } else {
            return Err(format!(
                "Syntax error char {} at position {:?}",
                c, position
            ));
        }
        position.advance(c);
    }
    Ok(tokens)
}
