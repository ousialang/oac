use serde::Serialize;

#[derive(Clone, Debug, Default, Serialize, PartialEq, Eq)]
pub struct SourceSpan {
    pub file: Option<String>,
    pub start_line: Option<u32>,
    pub start_column: Option<u32>,
    pub end_line: Option<u32>,
    pub end_column: Option<u32>,
}

impl SourceSpan {
    pub fn new(
        file: Option<String>,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    ) -> Self {
        Self {
            file,
            start_line: Some(start_line),
            start_column: Some(start_column),
            end_line: Some(end_line),
            end_column: Some(end_column),
        }
    }

    #[allow(dead_code)]
    pub fn with_file(&self, file: Option<String>) -> Self {
        let mut out = self.clone();
        out.file = file;
        out
    }

    pub fn display_compact(&self) -> String {
        let file_prefix = self
            .file
            .as_ref()
            .map(|file| format!("{file}:"))
            .unwrap_or_default();
        match (
            self.start_line,
            self.start_column,
            self.end_line,
            self.end_column,
        ) {
            (Some(start_line), Some(start_column), Some(end_line), Some(end_column))
                if start_line == end_line && start_column == end_column =>
            {
                format!("{file_prefix}{start_line}:{start_column}")
            }
            (Some(start_line), Some(start_column), Some(end_line), Some(end_column))
                if start_line == end_line =>
            {
                format!("{file_prefix}{start_line}:{start_column}-{end_column}")
            }
            (Some(start_line), Some(start_column), Some(end_line), Some(end_column)) => {
                format!("{file_prefix}{start_line}:{start_column}-{end_line}:{end_column}")
            }
            _ => file_prefix.trim_end_matches(':').to_string(),
        }
    }
}
