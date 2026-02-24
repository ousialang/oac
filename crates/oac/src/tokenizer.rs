//! An eager tokenizer for Ousia source files.
//!
//! By "eager", we mean that the tokenizer consumes the entire source file before
//! returning the data to the next stage (i.e. the parser). Here's a nice thread
//! about the tradeoffs involved with such an approach:
//! <https://old.reddit.com/r/ProgrammingLanguages/comments/9ve8ms/scanning_on_demand_or_separate_pass/>.

use serde::{Deserialize, Serialize};

/// Sequences of these characters compose symbols.
const ALLOWED_SYMBOLS: &str = "*@%=,+/:-><+-.!&|";

#[derive(Debug, Serialize, Deserialize)]
pub struct TokenList {
    pub tokens: Vec<TokenData>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TokenData {
    Newline,
    Parenthesis { opening: char, is_opening: bool },
    Number(u32),
    Float(String),
    Char(char),
    String(String),
    Word(String),
    Symbols(String),
    Comment(String),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
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
        } else if c == '\'' {
            let next = chars.next().ok_or(SyntaxError {
                message: "unterminated char literal".to_string(),
                position: position.clone(),
            })?;
            let decoded = if next == '\\' {
                let escaped = chars.next().ok_or(SyntaxError {
                    message: "unterminated escape sequence in char literal".to_string(),
                    position: position.clone(),
                })?;
                match escaped {
                    '\\' => '\\',
                    '\'' => '\'',
                    '"' => '"',
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    other => {
                        return Err(SyntaxError {
                            message: format!("unsupported escape sequence '\\{}'", other),
                            position: position.clone(),
                        })
                    }
                }
            } else {
                next
            };

            let closing = chars.next().ok_or(SyntaxError {
                message: "unterminated char literal".to_string(),
                position: position.clone(),
            })?;
            if closing != '\'' {
                return Err(SyntaxError {
                    message: "char literal must contain exactly one character".to_string(),
                    position: position.clone(),
                });
            }

            tokens.tokens.push(TokenData::Char(decoded));
        } else if c == '"' {
            let mut string = String::new();
            while chars.peek().is_some() && *chars.peek().unwrap() != '"' {
                let next = chars.next().unwrap();
                if next == '\\' {
                    let escaped = chars.next().ok_or(SyntaxError {
                        message: "unterminated escape sequence in string literal".to_string(),
                        position: position.clone(),
                    })?;
                    let decoded = match escaped {
                        '\\' => '\\',
                        '"' => '"',
                        'n' => '\n',
                        't' => '\t',
                        'r' => '\r',
                        other => {
                            return Err(SyntaxError {
                                message: format!("unsupported escape sequence '\\{}'", other),
                                position: position.clone(),
                            })
                        }
                    };
                    string.push(decoded);
                } else {
                    string.push(next);
                }
            }
            if chars.peek().is_some() {
                chars.next();
            } else {
                return Err(SyntaxError {
                    message: "unterminated string literal".to_string(),
                    position: position.clone(),
                });
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
            let mut literal = String::new();
            literal.push(c);
            while chars.peek().is_some() && chars.peek().unwrap().is_ascii_digit() {
                literal.push(chars.next().unwrap());
            }

            let is_float = if chars.peek() == Some(&'.') {
                let mut lookahead = chars.clone();
                lookahead.next();
                lookahead.peek().is_some_and(|ch| ch.is_ascii_digit())
            } else {
                false
            };

            if is_float {
                literal.push(chars.next().unwrap());
                while chars.peek().is_some() && chars.peek().unwrap().is_ascii_digit() {
                    literal.push(chars.next().unwrap());
                }
                tokens.tokens.push(TokenData::Float(literal));
            } else {
                let number = literal.parse::<u32>().map_err(|_| SyntaxError {
                    message: format!("integer literal out of range for I32: {}", literal),
                    position: position.clone(),
                })?;
                tokens.tokens.push(TokenData::Number(number));
            }
        } else if c == '\n' {
            tokens.tokens.push(TokenData::Newline);
        } else if c.is_ascii_whitespace() {
        } else if c.is_ascii_alphabetic() || c == '_' {
            let mut word = String::new();
            word.push(c);
            while chars
                .peek()
                .is_some_and(|next| next.is_ascii_alphanumeric() || *next == '_')
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
    fn tokenizes_fp32_literals() {
        let tokens = tokenize("x = 1.25\n".to_string()).expect("tokenize source");
        assert!(tokens
            .tokens
            .contains(&TokenData::Float("1.25".to_string())));
    }

    #[test]
    fn tokenizes_fp64_suffix_as_following_word() {
        let tokens = tokenize("x = 1.25f64\n".to_string()).expect("tokenize source");
        assert!(tokens
            .tokens
            .contains(&TokenData::Float("1.25".to_string())));
        assert!(tokens.tokens.contains(&TokenData::Word("f64".to_string())));
    }

    #[test]
    fn tokenizes_char_literals() {
        let tokens = tokenize("x = 'x'\n".to_string()).expect("tokenize source");
        assert!(tokens.tokens.contains(&TokenData::Char('x')));
    }

    #[test]
    fn tokenizes_identifier_at_eof_without_panicking() {
        let tokens = tokenize("identifier".to_string()).expect("tokenize source");
        assert_eq!(
            tokens.tokens,
            vec![TokenData::Word("identifier".to_string())]
        );
    }

    #[test]
    fn tokenizes_underscore_identifier_at_eof_without_panicking() {
        let tokens = tokenize("_".to_string()).expect("tokenize source");
        assert_eq!(tokens.tokens, vec![TokenData::Word("_".to_string())]);
    }

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
