// diagnostics.rs
// ==============
//
// Necessary interfaces for displaying diagnostic messages to end users. The relevant part of
// the LSP can be found here:
//   https://microsoft.github.io/language-server-protocol/specification#textDocument_publishDiagnostics

use langserver::lsp::utils::{Diagnostic, Uri};

#[derive(Serialize, Deserialize)]
pub struct Publish {
    uri: Uri,
    diagnostics: Vec<Diagnostic>,
}
