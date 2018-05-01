// general.rs
// ==========
//
// Type declarations for JSON-RPC messages managing metadata and server lifetime. See the relevant
// section of LSP's specification at
//   https://microsoft.github.io/language-server-protocol/specification#general

use langserver::jsonrpc::Id;
use langserver::lsp::workspace::Folders;
use serde_json::Value as JsonValue;

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Initialize {
    process_id: Option<i64>,
    // TODO: Add an alias for deprecated 'rootPath'.
    root_uri: Option<String>,
    options: Option<JsonValue>,
    capabilities: utils::ClientCapabilities,
    #[serde(default)]
    trace: utils::TraceSetting,
    workspace_folders: Option<Vec<Folders>>,
}

#[derive(Serialize, Deserialize)]
pub struct CancelRequest {
    id: Id,
}

pub mod utils {
    use langserver::jsonrpc;
    use langserver::lsp;
    use langserver::lsp::features::utils::CompletionItemKind;
    use serde_json::{Number as JsonNumber, Value as JsonValue};

    // Start of capabilities-related utilities
    // ---------------------------------------

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ClientCapabilities {
        #[serde(skip_serializing_if = "Option::is_none")]
        workspace: Option<ClientCapabilityOfWorkspace>,
        #[serde(skip_serializing_if = "Option::is_none")]
        text_document: Option<ClientCapabilityOfFiles>,
        experimental: Option<JsonValue>,
    }

    #[derive(Serialize, Deserialize)]
    pub struct DynamicRegistrationSupport {
        #[serde(rename = "dynamicRegistration")]
        support: bool,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ClientCapabilityOfWorkspace {
        apply_edit: Option<bool>,
        #[serde(rename = "workspaceEdit")]
        edit: Option<ClientCapabilityOfWorkspaceEdit>,
        did_change_configuration: Option<DynamicRegistrationSupport>,
        did_change_watched_files: Option<DynamicRegistrationSupport>,
        #[serde(rename = "symbol")]
        symbols: Option<ClientCapabilityOfWorkspaceSymbols>,
        execute_command: Option<DynamicRegistrationSupport>,
        folders: Option<bool>,
        configuration: Option<bool>,
    }

    #[derive(Serialize, Deserialize)]
    pub struct ClientCapabilityOfWorkspaceEdit {
        #[serde(rename = "documentChanges")]
        file_changes: Option<bool>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ClientCapabilityOfWorkspaceSymbols {
        dynamic_registration: bool,
        #[serde(rename = "symbolKind")]
        kind: ClientCapabilityOfWorkspaceSymbolsKind,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ClientCapabilityOfWorkspaceSymbolsKind {
        value_set: Vec<SymbolsKind>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ClientCapabilityOfFiles {
        #[serde(rename = "synchronization")]
        sync: Option<ClientCapabilityOfSync>,
        completion: Option<ClientCapabilityOfCompletion>,
        hover: Option<ClientCapabilityOfHover>,
        signature_help: Option<ClientCapabilityOfSignatureHelp>,
        references: Option<DynamicRegistrationSupport>,
        #[serde(rename = "documentHighlight")]
        highlights: Option<DynamicRegistrationSupport>,
        #[serde(rename = "documentSymbol")]
        symbols: Option<ClientCapabilityOfSymbols>,
        #[serde(rename = "definition")]
        goto_definition: Option<DynamicRegistrationSupport>,
        #[serde(rename = "typeDefinition")]
        goto_type_defitinion: Option<DynamicRegistrationSupport>,
        #[serde(rename = "implementation")]
        goto_implementation: Option<DynamicRegistrationSupport>,
        code_action: Option<DynamicRegistrationSupport>,
        code_lens: Option<DynamicRegistrationSupport>,
        #[serde(rename = "documentLink")]
        links: Option<DynamicRegistrationSupport>,
        #[serde(rename = "colorProvider")]
        colors: Option<DynamicRegistrationSupport>,
        #[serde(rename = "formatting")]
        format: Option<DynamicRegistrationSupport>,
        #[serde(rename = "rangeFormatting")]
        format_in_range: Option<DynamicRegistrationSupport>,
        #[serde(rename = "onTypeFormatting")]
        format_while_typing: Option<DynamicRegistrationSupport>,
        rename: Option<DynamicRegistrationSupport>,
        publish_diagnostics: Option<DynamicRegistrationSupport>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ClientCapabilityOfSync {
        dynamic_registration: Option<bool>,
        will_save: Option<bool>,
        will_save_request: Option<bool>,
        did_save: Option<bool>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ClientCapabilityOfCompletion {
        dynamic_registration: Option<bool>,
        completition_item: Option<ClientCapabilityOfCompletionItem>,
        completition_item_kind: Option<ClientCapabilityOfCompletionItemKind>,
        context_support: Option<bool>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ClientCapabilityOfCompletionItem {
        snipper_support: Option<bool>,
        #[serde(rename = "commitCharactersSupport")]
        commit_chars_support: Option<bool>,
        documentation_format: Vec<String>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ClientCapabilityOfCompletionItemKind {
        value_set: Option<Vec<CompletionItemKind>>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ClientCapabilityOfHover {
        dynamic_registration: Option<bool>,
        content_format: Option<Vec<String>>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ClientCapabilityOfSymbols {
        dynamic_registration: Option<bool>,
        symbol_kind: Option<Vec<SymbolKind>>,
    }

    // fixme
    type SymbolKind = String;

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ClientCapabilityOfSignatureHelp {
        dynamic_registration: Option<bool>,
        signature_information: Option<ClientCapabilityOfSignatureHelpInformation>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ClientCapabilityOfSignatureHelpInformation {
        documentation_format: Option<Vec<String>>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ServerCapabilities {
        #[serde(skip_serializing_if = "Option::is_none")]
        #[serde(rename = "textDocumentSync")]
        sync: Option<ServerCapabilityOfSync>,
        #[serde(skip_serializing_if = "Option::is_none")]
        #[serde(rename = "hoverProvider")]
        hover: Option<bool>,
        #[serde(skip_serializing_if = "Option::is_none")]
        completion: Option<ServerCapabilityOfCompletion>,
        #[serde(skip_serializing_if = "Option::is_none")]
        signature_help: Option<ServerCapabilityOfSignatureHelp>,
        #[serde(skip_serializing_if = "Option::is_none")]
        #[serde(rename = "definitionProvider")]
        goto_definition: Option<bool>,
        #[serde(skip_serializing_if = "Option::is_none")]
        #[serde(rename = "definitionProvider")]
        goto_type_definition: (),
        #[serde(skip_serializing_if = "Option::is_none")]
        #[serde(rename = "definitionProvider")]
        references: Option<bool>,
        #[serde(skip_serializing_if = "Option::is_none")]
        #[serde(rename = "definitionProvider")]
        highlights: Option<bool>,
        #[serde(skip_serializing_if = "Option::is_none")]
        #[serde(rename = "definitionProvider")]
        symbols: Option<bool>,
        #[serde(skip_serializing_if = "Option::is_none")]
        code_action: Option<bool>,
        #[serde(skip_serializing_if = "Option::is_none")]
        code_lens: Option<ServerCapabilityWithResolveProvider>,
        #[serde(skip_serializing_if = "Option::is_none")]
        format: Option<bool>,
        #[serde(skip_serializing_if = "Option::is_none")]
        format_in_range: Option<bool>,
        #[serde(skip_serializing_if = "Option::is_none")]
        format_while_typing: Option<lsp::features::options::FormatWhileTyping>,
        #[serde(skip_serializing_if = "Option::is_none")]
        rename: Option<bool>,
        #[serde(skip_serializing_if = "Option::is_none")]
        links: Option<ServerCapabilityWithResolveProvider>,
        #[serde(skip_serializing_if = "Option::is_none")]
        execute_command: Option<lsp::workspace::options::ExecuteCommand>,
        #[serde(skip_serializing_if = "Option::is_none")]
        workspace: Option<ServerCapabilityOfWorkspace>,
        #[serde(skip_serializing_if = "Option::is_none")]
        experimental: Option<JsonValue>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ServerCapabilityOfSync {
        #[serde(skip_serializing_if = "Option::is_none")]
        open_close: Option<bool>,
        #[serde(skip_serializing_if = "Option::is_none")]
        change: Option<JsonNumber>,
        #[serde(skip_serializing_if = "Option::is_none")]
        will_save: Option<bool>,
        #[serde(skip_serializing_if = "Option::is_none")]
        will_save_request: Option<bool>,
        #[serde(skip_serializing_if = "Option::is_none")]
        save: Option<ServerCapabilityOfSyncSave>,
    }

    #[derive(Serialize, Deserialize)]
    pub struct ServerCapabilityOfSyncSave {
        #[serde(skip_serializing_if = "Option::is_none")]
        include_text: Option<bool>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ServerCapabilityOfCompletion {
        #[serde(skip_serializing_if = "Option::is_none")]
        resolve_provider: Option<bool>,
        #[serde(skip_serializing_if = "Option::is_none")]
        #[serde(rename = "triggerCharacters")]
        trigger_chars: Option<Vec<char>>,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ServerCapabilityOfSignatureHelp {
        #[serde(skip_serializing_if = "Option::is_none")]
        #[serde(rename = "triggerCharacters")]
        trigger_chars: Option<Vec<char>>,
    }

    #[derive(Serialize, Deserialize)]
    pub struct ServerCapabilityWithResolveProvider {
        #[serde(skip_serializing_if = "Option::is_none")]
        resolve_provider: Option<bool>,
    }

    #[derive(Serialize, Deserialize)]
    pub struct ServerCapabilityOfWorkspace {
        #[serde(rename = "workspaceFolders")]
        folders: ServerCapabilityOfWorkspaceFolders,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ServerCapabilityOfWorkspaceFolders {
        supported: Option<bool>,
        change_notifications: Option<StringOrBool>,
    }

    #[derive(Serialize, Deserialize)]
    pub enum StringOrBool {
        String(String),
        Bool(bool),
    }

    // End of capabilities-related utilities
    // -------------------------------------

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub enum TraceSetting {
        Off,
        Messages,
        Verbose,
    }

    impl Default for TraceSetting {
        fn default() -> Self {
            TraceSetting::Off
        }
    }
}

pub mod results {
    use langserver::lsp::general::utils::ServerCapabilities;

    #[derive(Serialize, Deserialize)]
    pub struct Initialize {
        capabilities: ServerCapabilities,
    }
}

pub mod errors {
    const ERROR_CODE_UNKNOWN_PROTOCOL_VERSION: i64 = 1;

    #[derive(Serialize, Deserialize)]
    struct Initialize {
        retry: bool,
    }
}
