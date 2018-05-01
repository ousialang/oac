use langserver::lsp::utils::{FileId, ReasonForSavingFile, Uri, WorkspaceEdit};
use serde_json::Value as JsonValue;

#[derive(Serialize, Deserialize)]
pub struct Folders;

#[derive(Serialize, Deserialize)]
pub struct DidChangeFolders {
    event: utils::FoldersChangeEvent,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WillSaveFile {
    #[serde(rename = "textDocument")]
    file: FileId,
    reason: ReasonForSavingFile,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DidSaveFile {
    file: FileId,
    #[serde(skip_serializing_if = "Option::is_none")]
    text: Option<String>,
}

#[derive(Serialize, Deserialize)]
pub struct DidChangeConfiguration {
    settings: JsonValue,
}

#[derive(Serialize, Deserialize)]
pub struct Configuration {
    items: Vec<utils::ConfigurationItem>,
}

#[derive(Serialize, Deserialize)]
pub struct DidChangeWatchedFiles {
    changes: Vec<utils::FileEvent>,
}

#[derive(Serialize, Deserialize)]
pub struct Symbols {
    query: String,
}

#[derive(Serialize, Deserialize)]
pub struct ExecuteCommand {
    commmand: String,
    args: Option<JsonValue>,
}

#[derive(Serialize, Deserialize)]
pub struct ApplyEdit {
    #[serde(skip_serializing_if = "Option::is_none")]
    label: Option<String>,
    edit: WorkspaceEdit,
}

pub mod options {

    #[derive(Serialize, Deserialize)]
    pub struct DidChangeWatchedFiles {
        watchers: Vec<FileSystemWatcher>,
    }

    #[derive(Serialize, Deserialize)]
    pub struct FileSystemWatcher {
        pattern: String,
        events: u64,
    }

    #[derive(Serialize, Deserialize)]
    pub struct ExecuteCommand {
        commands: Vec<String>,
    }
}

pub mod utils {
    use langserver::lsp::utils::Uri;

    #[derive(Serialize, Deserialize)]
    pub struct FoldersChangeEvent {
        added: Vec<Folder>,
        removed: Vec<Folder>,
    }

    #[derive(Serialize, Deserialize)]
    pub struct Folder {
        uri: String,
        name: String,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct ConfigurationItem {
        #[serde(skip_serializing_if = "Option::is_none")]
        scope_uri: Option<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        section: Option<String>,
    }

    #[derive(Serialize, Deserialize)]
    pub struct FileEvent {
        uri: Uri,
        #[serde(rename = "type")]
        kind: FileChangeKind,
    }

    #[derive(Serialize, Deserialize)]
    enum FileChangeKind {
        Created = 1,
        Changed = 2,
        Deleted = 3,
    }
}
