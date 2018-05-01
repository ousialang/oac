use langserver::jsonrpc;
use langserver::jsonrpc::general::Exit;
use langserver::server::{self, LangServer, LangServerState};

use exitcode::{self, ExitCode};

impl server::Server<Exit, ExitCode> for LangServer {
    fn reply(&mut self, request: Exit) -> Option<ExitCode> {
        match self.state {
            LangServerState::Shutdown => Some(0),
            _ => Some(1),
        }
    }
}
