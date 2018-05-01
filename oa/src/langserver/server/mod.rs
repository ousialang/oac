// server/mod.rs
// =============
//

use build::Engine;
use langserver::jsonrpc::{BatchRequests, Error as RpcError, Id, Message, Request};
use langserver::lsp::general::utils::{ClientCapabilities, ServerCapabilities};
use langserver::server::error::Error;

use std::io::{Error as IoError, Read, Write};
use std::iter;
use std::net::{TcpListener, TcpStream};
use std::rc::Rc;

use exitcode::ExitCode;
use futures::prelude::Future;
use indexmap::IndexMap;
use rayon::{ThreadPool, ThreadPoolBuilder};
use serde::{Deserialize, Serialize};
use serde_json::Value as JsonValue;
use stopwatch::Stopwatch;

pub struct LangServer {
    listener: TcpListener,
    stream: TcpStream,
    threadpool: ThreadPool,
    pending_by_server: PendingRequests,
    pending_by_client: PendingRequests,
    id_generator: IdGenerator,
    engine: Option<Engine>,
    stopwatch: Stopwatch,
    capabilities: ServerCapabilities,
    state: LangServerState,
}

impl LangServer {
    pub fn new() -> Result<Self, Error> {
        let listener = TcpListener::bind("127.0.0.1:0")?;
        // Note that 'accept' is blocking and might take a while.
        let stream = listener.listen().accept()?;
        let threadpool = ThreadPoolBuilder::new().build()?;
        LangServer {
            listener: listener,
            stream: stream,
            threadpool: threadpool,
            pending_by_server: PendingRequests::new(),
            pending_by_client: PendingRequests::new(),
            id: (0..),
            engine: None,
            stopwatch: Stopwatch::new(),
            state: LangServerState::Instantiated,
        }
    }

    pub fn wait(&mut self) -> ExitCode {
        for s in self.listener.incoming() {
            match Message::from_stream(s) {
                Ok(m) => self.handle(Message::from_stream(s)),
                Err(e) => {
                    self.send(Message::response_to_invalid_stream(e));
                }
            }
        }
    }

    pub fn handle(&mut self, m: Message) {
        match m.content {
            Message::BatchRequests => {}
            Message::BatchResponses => {}
            Message::Request => {}
            Message::Response => match self.history.sent.get(m.content) {},
        }
        self.inbox.push(m);
    }

    fn request<R: Serialize, S: Deserialize<'static>>(
        &mut self,
        request: R,
    ) -> Option<Future<Item = S, Error = RpcError>> {
        let message = Message::request(request);
        let id = self.id.next();
        self.stream.write(message.as_bytes());
        self.pending_by_client
            .insert(self.id.next(), Message::request(request));
    }
}

struct IdGenerator {
    next_id: u64,
}

impl iter::Iterator for IdGenerator {
    type Item = Id;

    fn next(&mut self) -> Self::Item {
        let id = Id::Number(self.next_id);
        self.next_id += 1;
        id
    }
}

pub trait Server<R: Deserialize<'static>, S: Serialize> {
    fn reply(&mut self, request: R) -> Option<S>;
}

struct PendingRequests {
    requests: IndexMap<Id, Request>,
    batches: IndexMap<Id, BatchRequests>,
}

impl PendingRequests {
    fn new() -> PendingRequests {
        PendingRequests {
            requests: IndexMap::new(),
            batches: IndexMap::new(),
        }
    }
}

enum LangServerState {
    Instantiated,
    Initialized,
    Shutdown,
}

pub mod error {
    pub use std::io::Error;
}
