use std::any::Any;
use std::collections::HashMap;
use std::fmt;
use std::io::IsTerminal;
use std::ops::Range;
use std::path::Path;

use ariadne::{sources, Config, Label, Report, ReportKind};

use crate::tokenizer::{Position, SyntaxError};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DiagnosticStage {
    Tokenize,
    Parse,
    Import,
    Comptime,
    Resolve,
    Prove,
    StructInvariant,
    LoopClassifier,
    Qbe,
    Zig,
    Io,
    Internal,
}

impl fmt::Display for DiagnosticStage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            DiagnosticStage::Tokenize => "tokenize",
            DiagnosticStage::Parse => "parse",
            DiagnosticStage::Import => "import",
            DiagnosticStage::Comptime => "comptime",
            DiagnosticStage::Resolve => "resolve",
            DiagnosticStage::Prove => "prove",
            DiagnosticStage::StructInvariant => "struct-invariant",
            DiagnosticStage::LoopClassifier => "loop-classifier",
            DiagnosticStage::Qbe => "qbe",
            DiagnosticStage::Zig => "zig",
            DiagnosticStage::Io => "io",
            DiagnosticStage::Internal => "internal",
        };
        f.write_str(name)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DiagnosticSeverity {
    Error,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceLabel {
    pub file_id: String,
    pub span: Range<usize>,
    pub message: String,
}

#[derive(Clone, Debug)]
pub struct CompilerDiagnostic {
    pub code: String,
    pub stage: DiagnosticStage,
    pub severity: DiagnosticSeverity,
    pub message: String,
    pub labels: Vec<SourceLabel>,
    pub notes: Vec<String>,
    pub help: Option<String>,
    pub sources: HashMap<String, String>,
}

impl CompilerDiagnostic {
    pub fn new(
        code: impl Into<String>,
        stage: DiagnosticStage,
        message: impl Into<String>,
    ) -> Self {
        Self {
            code: code.into(),
            stage,
            severity: DiagnosticSeverity::Error,
            message: message.into(),
            labels: Vec::new(),
            notes: Vec::new(),
            help: None,
            sources: HashMap::new(),
        }
    }

    pub fn with_source(mut self, file_id: impl Into<String>, source: impl Into<String>) -> Self {
        self.sources.insert(file_id.into(), source.into());
        self
    }

    pub fn with_label(
        mut self,
        file_id: impl Into<String>,
        span: Range<usize>,
        message: impl Into<String>,
    ) -> Self {
        self.labels.push(SourceLabel {
            file_id: file_id.into(),
            span,
            message: message.into(),
        });
        self
    }

    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    #[allow(dead_code)]
    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    pub fn render_plain(&self) -> String {
        self.render_with_color(false)
    }

    #[allow(dead_code)]
    pub fn render_terminal_auto(&self) -> String {
        self.render_with_color(std::io::stderr().is_terminal())
    }

    fn render_with_color(&self, use_color: bool) -> String {
        let (primary_file_id, primary_span) = if let Some(label) = self.labels.first() {
            (label.file_id.clone(), sanitize_span(&label.span))
        } else if let Some((file_id, source)) = self.sources.iter().next() {
            let end = next_char_boundary(source, 0);
            (file_id.clone(), 0..end)
        } else {
            ("<unknown>".to_string(), 0..1)
        };

        let severity_prefix = match self.severity {
            DiagnosticSeverity::Error => "error",
        };

        let mut report = Report::build(
            ReportKind::Error,
            (primary_file_id.clone(), primary_span.clone()),
        )
        .with_code(self.code.clone())
        .with_message(format!(
            "{severity_prefix}[{}:{}]: {}",
            self.stage, self.code, self.message
        ))
        .with_config(Config::default().with_color(use_color));

        for label in &self.labels {
            report = report.with_label(
                Label::new((label.file_id.clone(), sanitize_span(&label.span)))
                    .with_message(label.message.clone()),
            );
        }

        for note in &self.notes {
            report = report.with_note(note.clone());
        }

        if let Some(help) = &self.help {
            report = report.with_help(help.clone());
        }

        let mut source_entries = self
            .sources
            .iter()
            .map(|(id, src)| (id.clone(), src.clone()))
            .collect::<Vec<_>>();
        if source_entries.is_empty() {
            source_entries.push((primary_file_id.clone(), String::new()));
        } else if !source_entries.iter().any(|(id, _)| id == &primary_file_id) {
            source_entries.push((primary_file_id.clone(), String::new()));
        }

        let mut output = Vec::new();
        match report.finish().write(sources(source_entries), &mut output) {
            Ok(()) => String::from_utf8_lossy(&output).trim_end().to_string(),
            Err(_) => self.fallback_render(),
        }
    }

    fn fallback_render(&self) -> String {
        let mut out = format!("error[{}:{}]: {}", self.stage, self.code, self.message);
        for note in &self.notes {
            out.push('\n');
            out.push_str("note: ");
            out.push_str(note);
        }
        if let Some(help) = &self.help {
            out.push('\n');
            out.push_str("help: ");
            out.push_str(help);
        }
        out
    }
}

impl fmt::Display for CompilerDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.render_plain())
    }
}

#[derive(Clone, Debug, Default)]
pub struct CompilerDiagnosticBundle {
    pub diagnostics: Vec<CompilerDiagnostic>,
}

impl CompilerDiagnosticBundle {
    pub fn single(diagnostic: CompilerDiagnostic) -> Self {
        Self {
            diagnostics: vec![diagnostic],
        }
    }

    pub fn from_anyhow(
        stage: DiagnosticStage,
        code: impl Into<String>,
        message: impl Into<String>,
        error: &anyhow::Error,
        source_path: Option<&Path>,
        source_text: Option<&str>,
    ) -> Self {
        Self::single(diagnostic_from_anyhow(
            stage,
            code,
            message,
            error,
            source_path,
            source_text,
        ))
    }

    #[allow(dead_code)]
    pub fn push(&mut self, diagnostic: CompilerDiagnostic) {
        self.diagnostics.push(diagnostic);
    }

    pub fn render_plain(&self) -> String {
        self.render_all(false)
    }

    pub fn render_terminal_auto(&self) -> String {
        self.render_all(std::io::stderr().is_terminal())
    }

    fn render_all(&self, use_color: bool) -> String {
        self.diagnostics
            .iter()
            .map(|diagnostic| diagnostic.render_with_color(use_color))
            .collect::<Vec<_>>()
            .join("\n\n")
    }
}

impl fmt::Display for CompilerDiagnosticBundle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.render_plain())
    }
}

pub fn diagnostic_from_anyhow(
    stage: DiagnosticStage,
    code: impl Into<String>,
    message: impl Into<String>,
    error: &anyhow::Error,
    source_path: Option<&Path>,
    source_text: Option<&str>,
) -> CompilerDiagnostic {
    let mut diagnostic = CompilerDiagnostic::new(code, stage, message);
    if let Some(source) = source_text {
        let file_id = file_id_from_path(source_path);
        diagnostic = diagnostic.with_source(file_id, source.to_string());
    }

    let mut causes = error.chain();
    if let Some(primary) = causes.next() {
        diagnostic.message = format!("{}: {}", diagnostic.message, primary);
    }
    for cause in causes {
        diagnostic = diagnostic.with_note(format!("caused by: {cause}"));
    }

    diagnostic
}

pub fn diagnostic_from_tokenizer_error(
    code: impl Into<String>,
    source: &str,
    source_path: Option<&Path>,
    error: &SyntaxError,
) -> CompilerDiagnostic {
    let file_id = file_id_from_path(source_path);
    let span = span_from_position(source, &error.position);
    CompilerDiagnostic::new(code, DiagnosticStage::Tokenize, "tokenization failed")
        .with_source(file_id.clone(), source.to_string())
        .with_label(file_id, span, error.message.clone())
        .with_note(format!(
            "at line {}, column {}",
            error.position.line, error.position.column
        ))
}

pub fn diagnostic_from_panic(payload: Box<dyn Any + Send>) -> CompilerDiagnostic {
    let panic_message = if let Some(msg) = payload.downcast_ref::<String>() {
        msg.clone()
    } else if let Some(msg) = payload.downcast_ref::<&'static str>() {
        msg.to_string()
    } else {
        "panic with non-string payload".to_string()
    };

    CompilerDiagnostic::new(
        "OAC-ICE-001",
        DiagnosticStage::Internal,
        "internal compiler error",
    )
    .with_note(format!("panic: {panic_message}"))
}

pub fn file_id_from_path(path: Option<&Path>) -> String {
    path.map(|value| value.display().to_string())
        .unwrap_or_else(|| "<memory>".to_string())
}

pub fn span_from_position(source: &str, position: &Position) -> Range<usize> {
    let start = line_column_to_byte_index(source, position.line, position.column);
    let end = next_char_boundary(source, start);
    sanitize_span(&(start..end))
}

pub fn sanitize_span(span: &Range<usize>) -> Range<usize> {
    if span.end <= span.start {
        span.start..span.start.saturating_add(1)
    } else {
        span.clone()
    }
}

#[allow(dead_code)]
pub fn char_index_to_byte_index(source: &str, char_index: usize) -> usize {
    source
        .char_indices()
        .nth(char_index)
        .map(|(idx, _)| idx)
        .unwrap_or(source.len())
}

pub fn line_column_to_byte_index(source: &str, line_1_based: u32, column_1_based: u32) -> usize {
    let mut line = 1_u32;
    let mut column = 1_u32;
    for (idx, ch) in source.char_indices() {
        if line == line_1_based && column == column_1_based {
            return idx;
        }
        if ch == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }
    source.len()
}

pub fn next_char_boundary(source: &str, start: usize) -> usize {
    if start >= source.len() {
        return start.saturating_add(1);
    }
    let mut iter = source[start..].char_indices();
    let _ = iter.next();
    if let Some((delta, _)) = iter.next() {
        start + delta
    } else {
        source.len()
    }
}

#[cfg(test)]
mod tests {
    use super::{
        diagnostic_from_tokenizer_error, CompilerDiagnostic, CompilerDiagnosticBundle,
        DiagnosticStage,
    };
    use crate::tokenizer::tokenize;

    #[test]
    fn tokenizer_error_conversion_marks_error_byte() {
        let source = "fun main() -> I32 {\n\t$\n}\n";
        let err = tokenize(source.to_string()).expect_err("tokenizer should fail");
        let diagnostic = diagnostic_from_tokenizer_error("OAC-TOKENIZE-001", source, None, &err);
        assert_eq!(diagnostic.labels.len(), 1);
        let span = diagnostic.labels[0].span.clone();
        assert_eq!(&source[span], "$");
    }

    #[test]
    fn plain_rendering_does_not_contain_ansi_sequences() {
        let diagnostic = CompilerDiagnostic::new(
            "OAC-RESOLVE-001",
            DiagnosticStage::Resolve,
            "type resolution failed",
        )
        .with_note("unknown type Foo");
        let text = diagnostic.render_plain();
        assert!(!text.contains("\u{1b}["));
    }

    #[test]
    fn bundle_plain_rendering_works_without_labels() {
        let diagnostic =
            CompilerDiagnostic::new("OAC-PARSE-001", DiagnosticStage::Parse, "parse failed")
                .with_note("unexpected token");
        let bundle = CompilerDiagnosticBundle::single(diagnostic);
        let text = bundle.render_plain();
        assert!(text.contains("parse failed"));
        assert!(text.contains("OAC-PARSE-001"));
    }

    #[test]
    fn plain_rendering_with_source_and_no_labels_is_valid() {
        let diagnostic =
            CompilerDiagnostic::new("OAC-IMPORT-001", DiagnosticStage::Import, "import failed")
                .with_source("test.oa", "fun main() -> I32 {\n\treturn 0\n}\n")
                .with_note("missing import");
        let text = diagnostic.render_plain();
        assert!(text.contains("import failed"));
        assert!(text.contains("OAC-IMPORT-001"));
    }
}
