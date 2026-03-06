use tokenizer::TokenData;

use crate::{parser, tokenizer};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum PendingBreak {
    None,
    Newline,
    BlankLine,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LineContent {
    Empty,
    Comment,
    Code,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Delimiter {
    TopLevel,
    Brace,
    Paren,
    Bracket,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LastKind {
    WordLike,
    OpenParen,
    CloseParen,
    OpenBracket,
    CloseBracket,
    OpenBrace,
    CloseBrace,
    Dot,
    Colon,
    Comma,
    Operator,
}

pub fn format_document(source: &str) -> Option<String> {
    let validation_tokens = tokenizer::tokenize(source.to_string()).ok()?;
    parser::parse(validation_tokens).ok()?;

    let tokens = tokenizer::tokenize(source.to_string()).ok()?;
    let mut formatter = Formatter::new(&tokens.tokens);
    let formatted = formatter.format();

    let formatted_tokens = tokenizer::tokenize(formatted.clone()).ok()?;
    parser::parse(formatted_tokens).ok()?;

    Some(formatted)
}

struct Formatter<'a> {
    tokens: &'a [TokenData],
    output: String,
    pending_break: PendingBreak,
    pending_space: bool,
    line_content: LineContent,
    delimiters: Vec<Delimiter>,
    indent_level: usize,
    last_kind: Option<LastKind>,
    last_word: Option<String>,
}

impl<'a> Formatter<'a> {
    fn new(tokens: &'a [TokenData]) -> Self {
        Self {
            tokens,
            output: String::new(),
            pending_break: PendingBreak::None,
            pending_space: false,
            line_content: LineContent::Empty,
            delimiters: vec![Delimiter::TopLevel],
            indent_level: 0,
            last_kind: None,
            last_word: None,
        }
    }

    fn format(&mut self) -> String {
        let mut index = 0;
        while index < self.tokens.len() {
            match &self.tokens[index] {
                TokenData::Newline => {
                    let run_len = self.newline_run_len(index);
                    self.handle_newline_run(index, run_len);
                    index += run_len;
                }
                TokenData::Comment(comment) => {
                    self.write_comment(comment);
                    index += 1;
                }
                TokenData::Parenthesis {
                    opening: '{',
                    is_opening: true,
                } => {
                    self.handle_open_brace();
                    index += 1;
                }
                TokenData::Parenthesis {
                    opening: '}',
                    is_opening: false,
                } => {
                    self.handle_close_brace(index);
                    index += 1;
                }
                TokenData::Parenthesis {
                    opening: '(',
                    is_opening: true,
                } => {
                    self.write_open_paren();
                    index += 1;
                }
                TokenData::Parenthesis {
                    opening: ')',
                    is_opening: false,
                } => {
                    self.write_close_paren();
                    index += 1;
                }
                TokenData::Parenthesis {
                    opening: '[',
                    is_opening: true,
                } => {
                    self.write_open_bracket();
                    index += 1;
                }
                TokenData::Parenthesis {
                    opening: ']',
                    is_opening: false,
                } => {
                    self.write_close_bracket();
                    index += 1;
                }
                TokenData::Parenthesis {
                    opening,
                    is_opening,
                } => {
                    let ch = if *is_opening {
                        opening.to_string()
                    } else {
                        match opening {
                            '}' => "}".to_string(),
                            ')' => ")".to_string(),
                            ']' => "]".to_string(),
                            other => other.to_string(),
                        }
                    };
                    self.write_word_like(&ch);
                    index += 1;
                }
                TokenData::Number(number) => {
                    self.write_word_like(&number.to_string());
                    index += 1;
                }
                TokenData::Float(value) => {
                    if matches!(
                        self.tokens.get(index + 1),
                        Some(TokenData::Word(suffix)) if suffix == "f32" || suffix == "f64"
                    ) {
                        let suffix = match &self.tokens[index + 1] {
                            TokenData::Word(suffix) => suffix.as_str(),
                            _ => unreachable!(),
                        };
                        self.write_word_like(&format!("{value}{suffix}"));
                        index += 2;
                    } else {
                        self.write_word_like(value);
                        index += 1;
                    }
                }
                TokenData::Char(value) => {
                    self.write_word_like(&format_char_literal(*value));
                    index += 1;
                }
                TokenData::String(value) => {
                    self.write_word_like(&format_string_literal(value));
                    index += 1;
                }
                TokenData::Word(word) => {
                    self.write_word(word);
                    index += 1;
                }
                TokenData::Symbols(symbols) => {
                    self.handle_symbols(symbols, index);
                    index += 1;
                }
            }
        }

        let mut output = self.output.trim_end_matches('\n').to_string();
        if !output.is_empty() {
            output.push('\n');
        }
        output
    }

    fn newline_run_len(&self, start: usize) -> usize {
        let mut index = start;
        while matches!(self.tokens.get(index), Some(TokenData::Newline)) {
            index += 1;
        }
        index - start
    }

    fn handle_newline_run(&mut self, start: usize, run_len: usize) {
        if self.should_join_else_after_newlines(start + run_len) {
            return;
        }

        if self.should_join_open_brace_after_newlines(start + run_len) {
            return;
        }

        if self.next_token_index(start + run_len).is_none() {
            return;
        }

        if self.is_top_level() && self.line_content == LineContent::Code {
            self.request_break(PendingBreak::BlankLine);
            return;
        }

        if run_len >= 2 {
            self.request_break(PendingBreak::BlankLine);
        } else {
            self.request_break(PendingBreak::Newline);
        }
    }

    fn handle_open_brace(&mut self) {
        if !self.is_line_start() {
            self.request_space();
        }
        self.write_raw("{", LastKind::OpenBrace);
        self.delimiters.push(Delimiter::Brace);
        self.indent_level += 1;
        self.request_break(PendingBreak::Newline);
    }

    fn handle_close_brace(&mut self, index: usize) {
        if matches!(self.delimiters.last(), Some(Delimiter::Brace)) {
            self.delimiters.pop();
        }
        self.indent_level = self.indent_level.saturating_sub(1);

        if self.line_content != LineContent::Empty {
            self.request_break(PendingBreak::Newline);
        }
        self.pending_space = false;
        self.write_raw("}", LastKind::CloseBrace);

        if self.should_join_else_after_newlines(index + 1) {
            self.request_space();
            return;
        }

        match self.tokens.get(index + 1) {
            Some(TokenData::Comment(_)) => {}
            Some(TokenData::Symbols(symbol))
                if symbol == ","
                    || symbol == "."
                    || is_binary_operator(symbol)
                    || symbol == ":" => {}
            Some(TokenData::Parenthesis {
                opening: ')',
                is_opening: false,
            })
            | Some(TokenData::Parenthesis {
                opening: ']',
                is_opening: false,
            })
            | Some(TokenData::Parenthesis {
                opening: '(',
                is_opening: true,
            }) => {}
            Some(TokenData::Newline) | None => {}
            Some(_) => {
                if self.is_top_level() {
                    self.request_break(PendingBreak::BlankLine);
                } else {
                    self.request_break(PendingBreak::Newline);
                }
            }
        }
    }

    fn write_open_paren(&mut self) {
        if self.last_word.as_deref() == Some("for") {
            self.request_space();
        }
        self.write_raw("(", LastKind::OpenParen);
        self.delimiters.push(Delimiter::Paren);
    }

    fn write_close_paren(&mut self) {
        if matches!(self.delimiters.last(), Some(Delimiter::Paren)) {
            self.delimiters.pop();
        }
        self.pending_space = false;
        self.write_raw(")", LastKind::CloseParen);
    }

    fn write_open_bracket(&mut self) {
        self.write_raw("[", LastKind::OpenBracket);
        self.delimiters.push(Delimiter::Bracket);
    }

    fn write_close_bracket(&mut self) {
        if matches!(self.delimiters.last(), Some(Delimiter::Bracket)) {
            self.delimiters.pop();
        }
        self.pending_space = false;
        self.write_raw("]", LastKind::CloseBracket);
    }

    fn handle_symbols(&mut self, symbols: &str, index: usize) {
        match symbols {
            "." => {
                self.pending_space = false;
                self.write_raw(".", LastKind::Dot);
            }
            ":" => {
                self.pending_space = false;
                self.write_raw(":", LastKind::Colon);
                self.request_space();
            }
            "," => {
                self.pending_space = false;
                self.write_raw(",", LastKind::Comma);
                if matches!(self.tokens.get(index + 1), Some(TokenData::Comment(_))) {
                    return;
                }
                if self.in_brace_context() {
                    self.request_break(PendingBreak::Newline);
                } else if !matches!(
                    self.tokens.get(index + 1),
                    Some(TokenData::Parenthesis {
                        opening: ')',
                        is_opening: false,
                    }) | Some(TokenData::Parenthesis {
                        opening: ']',
                        is_opening: false,
                    })
                ) {
                    self.request_space();
                }
            }
            "->" | "=>" => {
                self.write_operator(symbols);
            }
            symbol if is_binary_operator(symbol) => {
                self.write_operator(symbol);
            }
            other => self.write_word_like(other),
        }
    }

    fn write_operator(&mut self, operator: &str) {
        self.request_space();
        self.write_raw(operator, LastKind::Operator);
        self.request_space();
    }

    fn write_word_like(&mut self, text: &str) {
        if matches!(
            self.last_kind,
            Some(
                LastKind::WordLike
                    | LastKind::CloseParen
                    | LastKind::CloseBracket
                    | LastKind::CloseBrace
            )
        ) {
            self.request_space();
        }
        self.write_raw(text, LastKind::WordLike);
        self.last_word = None;
    }

    fn write_word(&mut self, word: &str) {
        self.write_word_like(word);
        self.last_word = Some(word.to_string());
    }

    fn write_comment(&mut self, comment: &str) {
        self.flush_pending_break();
        if self.is_line_start() {
            self.write_indent();
        } else {
            self.pending_space = false;
            self.output.push(' ');
        }
        self.output.push_str("//");
        self.output.push_str(comment);
        self.line_content = if self.line_content == LineContent::Code {
            LineContent::Code
        } else {
            LineContent::Comment
        };
        self.last_kind = None;
        self.last_word = None;
        self.request_break(PendingBreak::Newline);
    }

    fn write_raw(&mut self, text: &str, kind: LastKind) {
        self.flush_pending_break();
        if self.is_line_start() {
            self.write_indent();
        } else if self.pending_space {
            self.output.push(' ');
        }

        self.output.push_str(text);
        self.pending_space = false;
        self.line_content = LineContent::Code;
        self.last_kind = Some(kind);
        if kind != LastKind::WordLike {
            self.last_word = None;
        }
    }

    fn request_space(&mut self) {
        if !self.is_line_start() {
            self.pending_space = true;
        }
    }

    fn request_break(&mut self, pending_break: PendingBreak) {
        self.pending_space = false;
        self.pending_break = self.pending_break.max(pending_break);
    }

    fn flush_pending_break(&mut self) {
        if self.pending_break == PendingBreak::None || self.output.is_empty() {
            self.pending_break = PendingBreak::None;
            return;
        }

        let newline_count = match self.pending_break {
            PendingBreak::None => 0,
            PendingBreak::Newline => 1,
            PendingBreak::BlankLine => 2,
        };
        for _ in 0..newline_count {
            self.output.push('\n');
        }
        self.pending_break = PendingBreak::None;
        self.line_content = LineContent::Empty;
        self.last_kind = None;
        self.last_word = None;
    }

    fn write_indent(&mut self) {
        for _ in 0..self.indent_level {
            self.output.push('\t');
        }
    }

    fn should_join_else_after_newlines(&self, start: usize) -> bool {
        let mut index = start;
        while matches!(self.tokens.get(index), Some(TokenData::Newline)) {
            index += 1;
        }

        matches!(self.tokens.get(index), Some(TokenData::Word(word)) if word == "else")
    }

    fn should_join_open_brace_after_newlines(&self, start: usize) -> bool {
        let mut index = start;
        while matches!(self.tokens.get(index), Some(TokenData::Newline)) {
            index += 1;
        }

        matches!(
            self.tokens.get(index),
            Some(TokenData::Parenthesis {
                opening: '{',
                is_opening: true,
            })
        )
    }

    fn next_token_index(&self, start: usize) -> Option<usize> {
        let mut index = start;
        while matches!(self.tokens.get(index), Some(TokenData::Newline)) {
            index += 1;
        }
        self.tokens.get(index).map(|_| index)
    }

    fn is_top_level(&self) -> bool {
        self.delimiters.len() == 1
    }

    fn in_brace_context(&self) -> bool {
        matches!(self.delimiters.last(), Some(Delimiter::Brace))
    }

    fn is_line_start(&self) -> bool {
        self.line_content == LineContent::Empty
    }
}

fn format_string_literal(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for ch in value.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            other => out.push(other),
        }
    }
    out.push('"');
    out
}

fn format_char_literal(value: char) -> String {
    let mut out = String::from("'");
    match value {
        '\\' => out.push_str("\\\\"),
        '\'' => out.push_str("\\'"),
        '"' => out.push_str("\\\""),
        '\n' => out.push_str("\\n"),
        '\t' => out.push_str("\\t"),
        '\r' => out.push_str("\\r"),
        other => out.push(other),
    }
    out.push('\'');
    out
}

fn is_binary_operator(symbol: &str) -> bool {
    matches!(
        symbol,
        "=" | "+" | "-" | "*" | "/" | "==" | "!=" | "<" | ">" | "<=" | ">=" | "&&" | "||" | "%"
    )
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::PathBuf;

    use super::format_document;

    fn fixture_paths(dir: &str) -> Vec<PathBuf> {
        let mut paths = fs::read_dir(dir)
            .unwrap_or_else(|err| panic!("read {dir}: {err}"))
            .map(|entry| entry.expect("read directory entry").path())
            .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("oa"))
            .collect::<Vec<_>>();
        paths.sort();
        paths
    }

    #[test]
    fn formats_fixture_files() {
        for path in fixture_paths("formatter_tests") {
            let source = fs::read_to_string(&path)
                .unwrap_or_else(|err| panic!("read fixture {}: {err}", path.display()));
            let formatted = format_document(&source)
                .unwrap_or_else(|| panic!("expected formatter output for {}", path.display()));
            insta::assert_snapshot!(path.display().to_string(), formatted);
        }
    }

    #[test]
    fn returns_none_for_invalid_fixture_files() {
        for path in fixture_paths("formatter_invalid_tests") {
            let source = fs::read_to_string(&path)
                .unwrap_or_else(|err| panic!("read fixture {}: {err}", path.display()));
            assert!(
                format_document(&source).is_none(),
                "expected formatting to fail for {}",
                path.display()
            );
        }
    }
}
