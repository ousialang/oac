//! An eager tokenizer for Ousia source files.
//!
//! By "eager", we mean that the tokenizer consumes the entire source file before
//! returning the data to the next stage (i.e. the parser). Here's a nice thread
//! about the tradeoffs involved with such an approach:
//! <https://old.reddit.com/r/ProgrammingLanguages/comments/9ve8ms/scanning_on_demand_or_separate_pass/>.

use serde::{Deserialize, Serialize};

/// Sequences of these characters compose symbols.
const ALLOWED_SYMBOLS: &str = "*@%=,+/:-><+-.";

#[derive(Debug, Serialize, Deserialize)]
pub struct TokenList {
    pub tokens: Vec<TokenData>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TokenData {
    Newline,
    Parenthesis { opening: char, is_opening: bool },
    Number(u32),
    String(String),
    Word(String),
    Symbols(String),
    Comment(String),
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Position {
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
            absolute_i: 1,
            line: 1,
            column: 1,
        }
    }
}

#[derive(Debug, thiserror::Error, Serialize, Deserialize)]
#[error("syntax error: {message}")]
pub struct SyntaxError {
    pub message: String,
    pub position: Position,
}

#[tracing::instrument(level = "trace", skip_all)]
pub fn tokenize(s: String) -> Result<TokenList, SyntaxError> {
    let s_cloned = s.clone();
    let mut chars = s_cloned.chars().peekable();
    let mut tokens = TokenList { tokens: vec![] };
    let mut position = Position::default();
    while let Some(c) = chars.next() {
        if "([{".contains(c) {
            tokens.tokens.push(TokenData::Parenthesis {
                opening: c,
                is_opening: true,
            });
        } else if ")]}".contains(c) {
            tokens.tokens.push(TokenData::Parenthesis {
                opening: c,
                is_opening: false,
            });
        // Must come before symbol parsing, because slashes are also symbols.
        } else if c == '/' && chars.peek() == Some(&'/') {
            chars.next();
            let mut comment = String::new();
            while chars.peek().is_some() && *chars.peek().unwrap() != '\n' {
                comment.push(chars.next().unwrap());
            }
            tokens.tokens.push(TokenData::Comment(comment));
        } else if c == '"' {
            let mut string = String::new();
            while chars.peek().is_some() && *chars.peek().unwrap() != '"' {
                let c = chars.next().unwrap();
                string.push(c);
            }
            if chars.peek().is_some() {
                chars.next();
            }
            tokens.tokens.push(TokenData::String(string));
        } else if ALLOWED_SYMBOLS.contains(c) {
            let mut symbols = String::new();
            symbols.push(c);
            while chars.peek().is_some() && ALLOWED_SYMBOLS.contains(*chars.peek().unwrap()) {
                let c = chars.next().unwrap();
                symbols.push(c);
            }
            tokens.tokens.push(TokenData::Symbols(symbols));
        } else if c.is_ascii_digit() {
            let mut number = c.to_digit(10).unwrap();
            while chars.peek().is_some() && chars.peek().unwrap().is_digit(10) {
                let c = chars.next().unwrap();
                let digit = c.to_digit(10).unwrap();
                number = number * 10 + digit;
            }
            tokens.tokens.push(TokenData::Number(number))
        } else if c == '\n' {
            tokens.tokens.push(TokenData::Newline);
        } else if c.is_ascii_whitespace() {
        } else if c.is_ascii_alphabetic() || c == '_' {
            let mut word = String::new();
            word.push(c);
            while chars.peek().is_some() && chars.peek().unwrap().is_ascii_alphanumeric()
                || *chars.peek().unwrap() == '_'
            {
                let c = chars.next().unwrap();
                word.push(c);
            }
            tokens.tokens.push(TokenData::Word(word));
        } else {
            return Err(SyntaxError {
                message: format!("unexpected char '{}'", c),
                position,
            });
        }
        position.advance(c);
    }
    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn tokenize_files() {
        let test_files = fs::read_dir("tokenizer_tests").unwrap();

        for path in test_files {
            let path = path.unwrap().path();
            let file_contents = fs::read_to_string(&path).unwrap();
            let result = tokenize(file_contents);
            insta::assert_json_snapshot!(path.display().to_string(), result);
        }
    }
}
