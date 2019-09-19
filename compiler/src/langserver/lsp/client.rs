// client.rs
// =========
//
// Dynamic capability registristration from the client.
use langserver::jsonrpc::Id;
use langserver::lsp::utils::Void;
use langserver::lsp::utils::options::FileSelectorWrapper;
use langserver::lsp::{features, workspace};

#[derive(Serialize, Deserialize)]
pub struct ClientRegisterCapability {
    registrations: Vec<Registration>,
}

#[derive(Serialize, Deserialize)]
pub struct Registration {
    id: Id,
    #[serde(flatten)]
    dynamic_capability: DynamicCapability,
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "method", content = "registerOptions")]
pub enum DynamicCapability {
    // Workspace
    #[serde(rename = "workplace/didChangeWatchedFiles")]
    DidChangeWatchedFiles(workspace::options::DidChangeWatchedFiles),
    #[serde(rename = "workplace/symbol")]
    Symbol(Void),
    #[serde(rename = "workplace/didChangeWatchedFiles")]
    ExecuteCommand(workspace::options::ExecuteCommand),
    #[serde(rename = "workplace/didChangeWatchedFiles")]
    DidOpen(FileSelectorWrapper),
    // Language Features
    #[serde(rename = "textDocument/completion")]
    Completion(features::options::Completion),
    #[serde(rename = "textDocument/hover")]
    Hover(FileSelectorWrapper),
    #[serde(rename = "textDocument/SignatureHelp")]
    SignatureHelp(features::options::SignatureHelp),
    #[serde(rename = "textDocument/definition")]
    GotoDefinition(FileSelectorWrapper),
    #[serde(rename = "textDocument/typeDefinition")]
    GotoTypeDefinition(FileSelectorWrapper),
    #[serde(rename = "textDocument/implementation")]
    GotoImplementation(FileSelectorWrapper),
    #[serde(rename = "textDocument/references")]
    References(FileSelectorWrapper),
    #[serde(rename = "textDocument/highlights")]
    Highlights(FileSelectorWrapper),
    #[serde(rename = "textDocument/documentSymbol")]
    Symbols(FileSelectorWrapper),
    #[serde(rename = "textDocument/highlights")]
    CodeAction(FileSelectorWrapper),
    #[serde(rename = "textDocument/codeLens")]
    CodeLens(features::options::CodeLens),
    #[serde(rename = "textDocument/highlights")]
    Links(features::options::Links),
    #[serde(rename = "textDocument/rename")]
    Rename(FileSelectorWrapper),
}

#[derive(Serialize, Deserialize)]
pub struct ClientUnregisterCapability {
    unregisterations: Vec<Unregistration>,
}

#[derive(Serialize, Deserialize)]
pub struct Unregistration {
    id: Id,
    // TODO: Force Serde to encode 'method' as a 'DynamicCapability' tag.
    method: String,
}
