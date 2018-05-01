use langserver::lsp::utils::{FileId, Range, ReasonForSavingFile, VersionedFileId};

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DidChange {
    file: VersionedFileId,
    content_changes: Vec<utils::FileContentChangeEvent>,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WillSave {
    file: FileId,
    reason: ReasonForSavingFile,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DidSave {
    file: FileId,
    text: Option<String>,
}

pub mod utils {
    use langserver::lsp::utils::Range;

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct FileContentChangeEvent {
        #[serde(skip_serializing_if = "Option::is_none")]
        range: Option<Range>,
        #[serde(skip_serializing_if = "Option::is_none")]
        range_length: Option<u64>,
        text: String,
    }
}

pub mod options {
    use langserver::lsp::utils::options::FileSelectorWrapper;

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct DidChange {
        #[serde(flatten)]
        file_selector: FileSelectorWrapper,
        sync_kind: SyncKind,
    }

    #[derive(Serialize, Deserialize)]
    pub enum SyncKind {
        None = 0,
        Full = 1,
        Incremental = 2,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct DidSave {
        #[serde(flatten)]
        file_selector: FileSelectorWrapper,
        #[serde(skip_serializing_if = "Option::is_none")]
        include_text: Option<bool>,
    }
}
