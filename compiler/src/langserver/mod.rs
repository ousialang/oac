/* This file is part of Oac.
 *
 * Oac is free software: you can redistribute it and/or modify it under the
 * terms of the GNU General Public License as published by the Free Software
 * Foundation, either version 3 of the License, or (at your option) any later
 * version.
 *
 * Oac is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
 * details.
 *
 * You should have received a copy of the GNU General Public License along with
 * Oac.  If not, see <https://www.gnu.org/licenses/>. */

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
use colored::*;
use exitcode::ExitCode;
pub use langserver::server::LangServer;

pub fn main(args: ArgMatches) -> ExitCode {
    let ls = LangServer::new();
    ls.wait().exit_code
}

lazy_static! {
    pub static ref FATAL: ColoredString = "FATAL".bright_red().bold();
    pub static ref ERROR: ColoredString = "ERROR".red().bold();
    pub static ref WARNING: ColoredString = "WARNING".yellow().bold();
    pub static ref NOTE: ColoredString = "NOTE".bold();
}
