// lsp/mod.rs
// ==========
//
// This module contains the type declarations necessary for encoding and decoding LSP messages. The
// contents of each submodule are closely-related to the relevent sections of LSP's specification,
// which you can find here:
//   https://microsoft.github.io/language-server-protocol/specification
// For each JSON-RPC method offered by LSP, the relevent submodule follows roughly the same schema:
//   - A Top-level type declaration of the method's paramters.
//   - (Optional.) Any utility type declarations in the 'utils' submodule.
//   - (Optional.) Type declarations for any non-trival successful reponse to that method in the
//   'results' submodule.
//   - (Optional.) Error type declaration that may
//   - (Optional.) Any type declaration for registration options goes in the 'options' submodule.
//
// It is worth mentioning the special role that the 'client', 'server', and 'utils' submodule
// serve.
//   - The 'client' submodule
//   - 'utils' contains the declarations of some generic data types used extensively in LSP's
//   specification. Note that utility data types used for single methods should be declared in that
//   features's own 'utils' submodule. E.g. the top-level 'utils' submodule defines common data
//   types such as 'FileId' or 'Range', but.

pub mod client;
pub mod diagnostics;
pub mod features;
pub mod general;
pub mod sync;
pub mod telemetry;
pub mod utils;
pub mod window;
pub mod workspace;
