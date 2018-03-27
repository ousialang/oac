use utils::chars;
use utils::feedback::Feedback;

use std::collections::LinkedList;
use std::fs::File;
use std::io::prelude::*;
use std::ops::Range;
use std::path::PathBuf;


pub struct Ast {
    expressions: Vec<Expression>,
}

pub struct Expression {
    tokens: Ast,
}

pub struct Token {
    location: Range<u64>,
    kind: TokenKind,
}

pub enum TokenKind {
    NestedScope(NestedScope),
    Number(Number),
    Literal(Literal),
    Word,
    Symbol,
}

pub struct NestedScope {
    bracket: Bracket,
    contents: Vec<Expression>,
}

pub enum Bracket {
    Round,
    Square,
    Curly,
}

pub struct Number {
    decimal_point: Option<u16>,
}

pub struct Literal {
    true_str: String,
}


type ParserResult = (Option<Ast>, Vec<Feedback>);

impl Ast {
    pub fn new() -> Ast {
        Ast { expressions: Vec::new() }
    }

    pub fn from_string(src: &str) -> ParserResult {
        if src.is_empty() {
            let empty_ast = Ast { expressions: Vec::new() };
            return (Some(empty_ast), Vec::new()); // TODO warning
        }
        let mut parser = Parser::new();
        src.chars().map(|c| parser.transition(c));
        (parser.ast, parser.feedbacks)
    }

    pub fn from_file(path: PathBuf) -> ParserResult {
        let mut buffer = String::new();
        File::open(path).unwrap().read_to_string(&mut buffer);
        Ast::from_string(buffer.as_str())
    }
}


struct Parser {
    state: State,
    ast: Option<Ast>,
    feedbacks: Vec<Feedback>,
}

impl Parser {
    fn new() -> Parser {
        Parser {
            state: State::new(),
            ast: Some(Ast::new()),
            feedbacks: Vec::new(),
        }
    }

    fn transition(&mut self, c: char) {}
}


struct State {
    position: Position,
    pedigree_of_current_scope: LinkedList<char>,
    // Literals
    true_str: String,
    is_currently_escaped: bool,
    // Numbers
    base: Option<u8>,
    decimal_offset: Option<u64>,
    // Comments
    multiline_comment_nested_levels: u64,
    flag_last_char_was_asterisk: bool,
    flag_last_char_was_slash: bool,
    // Whitespace
    flag_last_char_was_cr: bool,
}

impl State {
    fn new() -> State {
        State {
            position: Position::Empty,
            pedigree_of_current_scope: LinkedList::new(),
            true_str: String::new(),
            is_currently_escaped: false,
            base: None,
            decimal_offset: None,
            multiline_comment_nested_levels: 0,
            flag_last_char_was_asterisk: false,
            flag_last_char_was_slash: false,
            flag_last_char_was_cr: false,
        }
    }
}

pub enum Position {
    Empty,
    InlineComment,
    MultilineComment,
    Literal,
    Number,
    Symbol,
    Word,
    Bracket,
    Whitespace,
}
/*
    fn transition(&mut self, c: char, parser: Parser) -> State {
        if c.is_bracket() {
            State::Bracket
        } else if c.is_alphabetic() {
            State::Word
        } else if c.is_symbol() {
            State::Symbol
        } else if c == '"' {
            State::Literal
        } else if c.is_digit() {
            State::Number
        } else if c.is_whitespace() {
            State::Whitespace
        } else {
            State::Unknown
        }
    }

struct Global {
    nested_brackets: LinkedList<char>,
}


struct InlineComment;


struct MultilineComment {
    asterisk_flag: bool,
    nested_levels: u64,
}


struct Empty;

impl Transition for Empty {

    fn new() -> State {
        Empty
    }

    fn transition(self, c: char) -> State {
        self.renew(c)
    }

    fn finalize(&self) -> Token {}
}


struct Literal {
    is_currently_escaped: bool,
    true_str: String,
}

impl Transition for Literal {

    fn new(c: char) -> State {
        State::Literal {
            is_escaped: false,
            true_literal: String::new(),
        }
    }

    fn transition(&mut self, c: char) -> ParserState {
        if c == '/' && !self.is_escaped {
            self.is_escaped = true;
        } else if c == '"' {
            self.true_literal.push(c);
        }
    }

    fn leave(&mut self) {
        self.is_escaped = false;
        self.true_literal = "";
    }

    fn finalize(self) -> Token {
        Token::Literal {
            true_literal: self.true_literal,
        }
    }
}


struct Number{
    explicit_base: Option<u8>,
    decimal_offset: u16,
}

impl Transition for Number {

    fn new(c: char) -> State {
        if c == '0' {
            State::Number {
                explicit_base: Ok(c),
                decimal_offset: None,
            }
        } else {
            State::Number {
                explicit_base: None,
                decimal_offset: None,
            }
        }
    }

    fn transition(&mut self, c: char) -> State {

    }

    fn finalize(&self) -> Token {}
}

struct Symbol;
struct Word;
struct Whitespace;
struct Bracket;*/
