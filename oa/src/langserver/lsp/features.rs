use langserver::lsp::utils::*;
use serde_json::Value as JsonValue;

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Completion {
    #[serde(flatten)]
    position_params: FilePosition,
    #[serde(skip_serializing_if = "Option::is_none")]
    context: Option<utils::CompletionContext>,
}

#[derive(Serialize, Deserialize)]
pub struct Hover {
    contents: utils::HoverContentsKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    range: Option<Range>,
}

#[derive(Serialize, Deserialize)]
pub struct References {
    context: utils::ReferencesContext,
}

#[derive(Serialize, Deserialize)]
pub struct Command {
    title: String,
    command: String,
    arguments: JsonValue,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct TextEdit {
    range: Range,
    new_text: String,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SignatureHelp {
    signatures: Vec<utils::SignatureInformation>,
    active_signature: u64,
    active_param: u64,
}

#[derive(Serialize, Deserialize)]
pub struct Highlights {
    range: Range,
    kind: Option<utils::HighlightsKind>,
}

#[derive(Serialize, Deserialize)]
pub struct CodeAction {
    file: FileId,
    range: Range,
    context: utils::CodeActionContext,
}

#[derive(Serialize, Deserialize)]
pub struct ColorPresentations {
    #[serde(rename = "textDocument")]
    file_id: FileId,
    #[serde(rename = "colorInfo")]
    color: utils::Color,
    range: Range,
}

#[derive(Serialize, Deserialize)]
pub struct Format {
    file_id: FileId,
    options: utils::FormatOptions,
}

#[derive(Serialize, Deserialize)]
pub struct FormatInRange {
    file_id: FileId,
    range: Range,
    options: utils::FormatOptions,
}

#[derive(Serialize, Deserialize)]
pub struct FormatWhileTyping {
    file_id: FileId,
    position: Position,
    c: char,
    options: utils::FormatOptions,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Rename {
    file: FileId,
    position: Position,
    new_name: String,
}

pub mod utils {
    use langserver::lsp::utils::{Diagnostic, MarkupContent};
    use serde_json::Value as JsonValue;
    use std::collections::HashMap;

    #[derive(Serialize, Deserialize)]
    pub struct CompletionContext {
        trigger_kind: CompletionTriggerKind,
        trigger_char: Option<char>,
    }

    #[derive(Serialize, Deserialize)]
    pub enum CompletionItemKind {
        Text = 1,
        Method = 2,
        Function = 3,
        Constructor = 4,
        Field = 5,
        Variable = 6,
        Class = 7,
        Interface = 8,
        Module = 9,
        Property = 10,
        Unit = 11,
        Value = 12,
        Enum = 13,
        Keyword = 14,
        Snippet = 15,
        Color = 16,
        File = 17,
        Reference = 18,
        Folder = 19,
        EnumMember = 20,
        Constant = 21,
        Struct = 22,
        Event = 23,
        Operator = 24,
        TypeParameter = 25,
    }

    #[derive(Serialize, Deserialize)]
    pub struct CodeActionContext {
        diagnostics: Vec<Diagnostic>,
    }

    #[derive(Serialize, Deserialize)]
    pub enum CompletionTriggerKind {
        Invoked = 1,
        TriggerChar = 2,
        TriggerForIncompleteCompletions = 3,
    }

    #[derive(Serialize, Deserialize)]
    pub enum HoverContentsKind {
        MarkedString(MarkedString),
        MarkedStringVec(Vec<MarkedString>),
        MarkupContent(MarkupContent),
    }

    #[derive(Serialize, Deserialize)]
    pub enum MarkedString {
        String(String),
        StringWithLanguage(StringWithLanguage),
    }

    #[derive(Serialize, Deserialize)]
    pub struct StringWithLanguage {
        language: String,
        value: String,
    }

    #[derive(Serialize, Deserialize)]
    pub struct SignatureInformation {
        label: String,
        documentation: StringOrMarkupContent,
        params: Vec<ParamInformation>,
    }

    #[derive(Serialize, Deserialize)]
    pub struct ReferencesContext {
        include_declaration: bool,
    }

    #[derive(Serialize, Deserialize)]
    pub struct ParamInformation {
        label: String,
        documentation: StringOrMarkupContent,
    }

    #[derive(Serialize, Deserialize)]
    pub enum HighlightsKind {
        Text = 1,
        Read = 2,
        Write = 3,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub enum SymbolsKind {
        File = 1,
        Module = 2,
        Namespace = 3,
        Package = 4,
        Class = 5,
        Method = 6,
        Property = 7,
        Field = 8,
        Constructor = 9,
        Enum = 10,
        Interface = 11,
        Function = 12,
        Variable = 13,
        Constant = 14,
        String = 15,
        Number = 16,
        Boolean = 17,
        Array = 18,
        Object = 19,
        Key = 20,
        Null = 21,
        EnumMember = 22,
        Struct = 23,
        Event = 24,
        Operator = 25,
        TypeParameter = 26,
    }

    #[derive(Serialize, Deserialize)]
    pub enum StringOrMarkupContent {
        String(String),
        MarkupContent(MarkupContent),
    }

    #[derive(Serialize, Deserialize)]
    pub struct Color {
        red: f32,
        green: f32,
        blue: f32,
        alpha: f32,
    }

    #[derive(Serialize, Deserialize)]
    pub struct FormatOptions {
        #[serde(rename = "tabSize")]
        indentation_size: u64,
        // https://www.youtube.com/watch?v=SsoOG6ZeyUI
        #[serde(rename = "insertSpaces")]
        indentation_kind: IndentationKind,
        #[serde(flatten)]
        options: HashMap<String, JsonValue>,
    }

    #[derive(Serialize, Deserialize)]
    pub enum IndentationKind {
        Spaces,
        Tabs,
    }
}

pub mod options {

    use langserver::lsp::utils::Diagnostic;
    use langserver::lsp::utils::options::FileSelectorWrapper;

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct Completion {
        #[serde(flatten)]
        file_selector_wrapper: FileSelectorWrapper,
        trigger_characters: Option<Vec<String>>,
        resolve_provider: Option<bool>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct Hover {
        #[serde(flatten)]
        file_selector_wrapper: FileSelectorWrapper,
        trigger_chars: Option<Vec<String>>,
        resolve_provider: Option<bool>,
    }

    #[derive(Serialize, Deserialize)]
    pub struct CodeActionContext {
        diagnostics: Vec<Diagnostic>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct Links {
        #[serde(flatten)]
        file_selector_wrapper: FileSelectorWrapper,
        resolve_provider: Option<bool>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct FormatWhileTyping {
        #[serde(flatten)]
        file_selector_wrapper: FileSelectorWrapper,
        first_trigger: char,
        other_triggers: Vec<char>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct CodeLens {
        #[serde(flatten)]
        file_selector_wrapper: FileSelectorWrapper,
        #[serde(skip_serializing_if = "Option::is_none")]
        resolve_provider: Option<bool>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct SignatureHelp {
        trigger_char: Vec<String>,
    }
}
