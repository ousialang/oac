/* This file is part of Oac.
 *
 * Oac is free software: you can redistribute it and/or modify it under the
 * terms of the GNU General Public License as published by the Free Software
 * Foundation, either version 3 of the License, or (at your option) any later
 * version.
 *
 * Oac is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
 * details.
 *
 * You should have received a copy of the GNU General Public License along with
 * Oac.  If not, see <https://www.gnu.org/licenses/>. */

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

impl Pass<SyntaxTree> for UncommentedLines {
    pub fn transform(self) -> Result<SyntaxTree, failure::Error>
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

    pub fn from_file(path: PathBuf) -> Option<Cst> {
        let mut buffer = String::new();
        File::open(path).unwrap().read_to_string(&mut buffer);
        Cst::from_string(buffer.as_str())
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
