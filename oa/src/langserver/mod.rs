// langserver/mod.rs
// =================
//
// The 'langserver' module contains the source code for Ousia's langserver server. The server is
// LSP 3.7.0 compliant (https://microsoft.github.io/language-server-protocol) but also supports
// some non-standard Ousia-specific features via JSON-RPC methods starting with "ousia/".

mod jsonrpc;
mod lsp;
mod server;

use clap::ArgMatches;
use exitcode::ExitCode;
pub use langserver::server::LangServer;

pub fn main(args: ArgMatches) -> ExitCode {
    let ls = LangServer::new();
    ls.wait().exit_code
}
