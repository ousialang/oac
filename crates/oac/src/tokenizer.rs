//! An eager tokenizer for Ousia source files.
//!
//! By "eager", we mean that the tokenizer consumes the entire source file before
//! returning the data to the next stage (i.e. the parser). Here's a nice thread
//! about the tradeoffs involved with such an approach:
//! <https://old.reddit.com/r/ProgrammingLanguages/comments/9ve8ms/scanning_on_demand_or_separate_pass/>.

use std::iter::Peekable;
use std::str::Chars;

use serde::{Deserialize, Serialize};

use crate::source_span::SourceSpan;

/// Sequences of these characters compose symbols.
const ALLOWED_SYMBOLS: &str = "*@%=,+/:-><+-.!&|";

#[derive(Debug, Serialize, Deserialize)]
pub struct TokenList {
    pub tokens: Vec<TokenData>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub spans: Vec<TokenSpan>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_name: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
pub struct TokenSpan {
    pub start: Position,
    pub end: Position,
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

impl TokenSpan {
    pub fn as_source_span(&self, source_name: Option<&str>) -> SourceSpan {
        SourceSpan::new(
            source_name.map(str::to_string),
            self.start.line,
            self.start.column,
            self.end.line,
            self.end.column,
        )
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
    tokenize_with_source_name(s, None)
}

#[tracing::instrument(level = "trace", skip_all)]
pub fn tokenize_with_source_name(
    s: String,
    source_name: Option<String>,
) -> Result<TokenList, SyntaxError> {
    let mut chars = s.chars().peekable();
    let mut tokens = TokenList {
        tokens: vec![],
        spans: vec![],
        source_name,
    };
    let mut position = Position::default();
    while let Some((c, start)) = next_char(&mut chars, &mut position) {
        let mut end = start.clone();
        if "([{".contains(c) {
            push_token(
                &mut tokens,
                TokenData::Parenthesis {
                    opening: c,
                    is_opening: true,
                },
                start,
                end,
            );
        } else if ")]}".contains(c) {
            push_token(
                &mut tokens,
                TokenData::Parenthesis {
                    opening: c,
                    is_opening: false,
                },
                start,
                end,
            );
        // Must come before symbol parsing, because slashes are also symbols.
        } else if c == '/' && chars.peek() == Some(&'/') {
            let (_, second_slash_end) = next_char(&mut chars, &mut position).expect("peeked slash");
            end = second_slash_end;
            let mut comment = String::new();
            while chars.peek().is_some() && *chars.peek().unwrap() != '\n' {
                let (comment_char, comment_end) =
                    next_char(&mut chars, &mut position).expect("peeked comment char");
                comment.push(comment_char);
                end = comment_end;
            }
            push_token(&mut tokens, TokenData::Comment(comment), start, end);
        } else if c == '\'' {
            let (next, _next_end) = next_char(&mut chars, &mut position).ok_or(SyntaxError {
                message: "unterminated char literal".to_string(),
                position: start.clone(),
            })?;
            let decoded = if next == '\\' {
                let (escaped, _escaped_end) =
                    next_char(&mut chars, &mut position).ok_or(SyntaxError {
                        message: "unterminated escape sequence in char literal".to_string(),
                        position: start.clone(),
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
                            position: start.clone(),
                        })
                    }
                }
            } else {
                next
            };

            let (closing, closing_end) =
                next_char(&mut chars, &mut position).ok_or(SyntaxError {
                    message: "unterminated char literal".to_string(),
                    position: start.clone(),
                })?;
            end = closing_end;
            if closing != '\'' {
                return Err(SyntaxError {
                    message: "char literal must contain exactly one character".to_string(),
                    position: start,
                });
            }

            push_token(&mut tokens, TokenData::Char(decoded), start, end);
        } else if c == '"' {
            let mut string = String::new();
            while chars.peek().is_some() && *chars.peek().unwrap() != '"' {
                let (next, _next_end) =
                    next_char(&mut chars, &mut position).expect("peeked string char");
                if next == '\\' {
                    let (escaped, _escaped_end) =
                        next_char(&mut chars, &mut position).ok_or(SyntaxError {
                            message: "unterminated escape sequence in string literal".to_string(),
                            position: start.clone(),
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
                                position: start.clone(),
                            })
                        }
                    };
                    string.push(decoded);
                } else {
                    string.push(next);
                }
            }
            if chars.peek().is_some() {
                let (_, closing_end) =
                    next_char(&mut chars, &mut position).expect("peeked string close");
                end = closing_end;
            } else {
                return Err(SyntaxError {
                    message: "unterminated string literal".to_string(),
                    position: start,
                });
            }
            push_token(&mut tokens, TokenData::String(string), start, end);
        } else if ALLOWED_SYMBOLS.contains(c) {
            let mut symbols = String::new();
            symbols.push(c);
            while chars.peek().is_some() && ALLOWED_SYMBOLS.contains(*chars.peek().unwrap()) {
                let (next, next_end) = next_char(&mut chars, &mut position).expect("peeked symbol");
                symbols.push(next);
                end = next_end;
            }
            push_token(&mut tokens, TokenData::Symbols(symbols), start, end);
        } else if c.is_ascii_digit() {
            let mut literal = String::new();
            literal.push(c);
            while chars.peek().is_some() && chars.peek().unwrap().is_ascii_digit() {
                let (next, next_end) = next_char(&mut chars, &mut position).expect("peeked digit");
                literal.push(next);
                end = next_end;
            }

            let is_float = if chars.peek() == Some(&'.') {
                let mut lookahead = chars.clone();
                lookahead.next();
                lookahead.peek().is_some_and(|ch| ch.is_ascii_digit())
            } else {
                false
            };

            if is_float {
                let (dot, dot_end) = next_char(&mut chars, &mut position).expect("peeked dot");
                literal.push(dot);
                end = dot_end;
                while chars.peek().is_some() && chars.peek().unwrap().is_ascii_digit() {
                    let (next, next_end) =
                        next_char(&mut chars, &mut position).expect("peeked float digit");
                    literal.push(next);
                    end = next_end;
                }
                push_token(&mut tokens, TokenData::Float(literal), start, end);
            } else {
                let number = literal.parse::<u32>().map_err(|_| SyntaxError {
                    message: format!("integer literal out of range for I32: {}", literal),
                    position: start.clone(),
                })?;
                push_token(&mut tokens, TokenData::Number(number), start, end);
            }
        } else if c == '\n' {
            push_token(&mut tokens, TokenData::Newline, start, end);
        } else if c.is_ascii_whitespace() {
        } else if c.is_ascii_alphabetic() || c == '_' {
            let mut word = String::new();
            word.push(c);
            while chars
                .peek()
                .is_some_and(|next| next.is_ascii_alphanumeric() || *next == '_')
            {
                let (next, next_end) =
                    next_char(&mut chars, &mut position).expect("peeked identifier char");
                word.push(next);
                end = next_end;
            }
            push_token(&mut tokens, TokenData::Word(word), start, end);
        } else {
            return Err(SyntaxError {
                message: format!("unexpected char '{}'", c),
                position: start,
            });
        }
    }
    Ok(tokens)
}

fn next_char(chars: &mut Peekable<Chars<'_>>, position: &mut Position) -> Option<(char, Position)> {
    let c = chars.next()?;
    let current = position.clone();
    position.advance(c);
    Some((c, current))
}

fn push_token(tokens: &mut TokenList, token: TokenData, start: Position, end: Position) {
    tokens.tokens.push(token);
    tokens.spans.push(TokenSpan { start, end });
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
