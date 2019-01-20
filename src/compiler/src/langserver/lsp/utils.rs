use langserver::jsonrpc::Id;

use std::collections::HashMap;

use serde_json::{Number as JsonNumber, Value as JsonValue};

#[derive(Serialize, Deserialize)]
pub struct Void;

pub type Uri = String;
pub type Syntax = String;

#[derive(Serialize, Deserialize)]
pub struct Position {
    line: u64,
    character: u64,
}

#[derive(Serialize, Deserialize)]
pub struct Range {
    start: Position,
    end: Position,
}

#[derive(Serialize, Deserialize)]
pub struct Location {
    uri: Uri,
    range: Range,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Diagnostic {
    range: Range,
    #[serde(skip_serializing_if = "Option::is_none")]
    severity: Option<JsonNumber>,
    #[serde(skip_serializing_if = "Option::is_none")]
    code: Option<Id>,
    #[serde(skip_serializing_if = "Option::is_none")]
    source: Option<String>,
    message: String,
    related_information: Option<Vec<DiagnosticRelatedInfo>>,
}

pub enum DiagnosticSeverity {
    Error = 1,
    Warning = 2,
    Information = 3,
    Hint = 4,
}

#[derive(Serialize, Deserialize)]
pub struct DiagnosticRelatedInfo {
    location: Location,
    message: String,
}

#[derive(Serialize, Deserialize)]
pub struct Command {
    title: String,
    command: String,
    arguments: Option<JsonValue>,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TextEdit {
    range: Range,
    new_text: String,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FileEdit {
    file: VersionedFileId,
    // https://github.com/Microsoft/language-server-protocol/blob/master/versions/protocol-2-x.md#textedit-1
    edits: Vec<TextEdit>,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WorkspaceEdit {
    changes: Option<HashMap<String, Vec<TextEdit>>>,
    document_changes: Option<Vec<FileEdit>>,
}

#[derive(Serialize, Deserialize)]
pub struct FileId {
    uri: Uri,
}

#[derive(Serialize, Deserialize)]
pub struct FileIdWrapper {
    #[serde(rename = "textDocument")]
    file_id: FileId,
}

#[derive(Serialize, Deserialize)]
pub struct SourceFile {
    uri: Uri,
    #[serde(rename = "languageId")]
    language: String,
    version: JsonNumber,
    text: String,
}

#[derive(Serialize, Deserialize)]
pub struct VersionedFileId {
    #[serde(flatten)]
    #[serde(rename = "textDocument")]
    file_id: FileId,
    version: Option<JsonNumber>,
}

#[derive(Serialize, Deserialize)]
pub struct FilePosition {
    #[serde(rename = "textDocument")]
    file_id: FileId,
    position: Position,
}

#[derive(Serialize, Deserialize)]
pub struct FileFilter {
    #[serde(skip_serializing_if = "Option::is_none")]
    language: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    scheme: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pattern: Option<String>,
}

#[derive(Serialize, Deserialize)]
pub struct FileSelector {
    #[serde(flatten)]
    filters: Vec<FileFilter>,
}

#[derive(Serialize, Deserialize)]
pub struct MarkupContent {
    value: String,
    kind: String,
}

#[derive(Serialize, Deserialize)]
pub enum ReasonForSavingFile {
    Manual = 1,
    AfterDelay = 2,
    FocusOut = 3,
}

pub mod options {
    use langserver::lsp::utils::FileSelector;

    #[derive(Serialize, Deserialize)]
    pub struct FileSelectorWrapper {
        #[serde(rename = "documentSelector")]
        file_selector: Option<FileSelector>,
    }
}
