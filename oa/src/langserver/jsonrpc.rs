// jsonrpc.rs
// ==========
//
// This module implements some common operations over LSP messages such as (de)serialization and
// error handling. These operations are independent from the server logic and are thus better
// abstracted.
// care about), as the latter are completely
// content-independent.

use indexmap::IndexMap;
use langserver::lsp;
use serde_json::{self, Value as JsonValue};
use std::net::TcpStream;

pub struct Message {
    header: IndexMap<String, String>,
    content: JsonRpcObject,
}

impl Message {
    fn from_stream(stream: TcpStream) -> Result<Message, Error> {
        let mut header = IndexMap::new();
        // The LS protocol specifies CRLF line endings, but by accepting LF line endings as well we
        // can deal more easily with broken clients.
        let mut lines = stream
            .lines()
            .map(|l| l.unwrap())
            .take_while(|s| !s.is_empty());
        // Parse the header.
        for line in lines {
            let header_field = line.split(": ").collect();
            if header_field.len() < 2 {
                return Err(Error::HeaderError);
            }
            let name = header_field.get(0).unwrap();
            let value = header_field.get(1).unwrap();
            header.insert(name, value);
        }
        let content_length_in_bytes = header
            .get(HEADER_FIELD_CONTENT_LENGTH)
            .ok_or_else(|| Error::Header::MissingHeaderField {
                missing_header_field_name: HEADER_FIELD_CONTENT_LENGTH,
            })?
            .parse()
            .ok_or_else(|| Error::Header::IllegalHeaderField {
                line_number: header.get_index(HEADER_FIELD_CONTENT_LENGTH).unwrap(),
            })?;
        let mut content_buffer = vec![0; content_length_in_bytes];
        stream.read_exact(&mut content_buffer);
        serde_json::from_slice::<JsonRpcObject>(content_buffer)
    }

    fn encoding(&self) -> String {
        match self.header.get(HEADER_FIELD_CONTENT_TYPE) {
            None => "utf-8",
            Some(header_value) => match header_value.split(";").get(1) {
                None => "utf-8",
                Some(charset_declaration) => {
                    charset_declaration
                        .into_iter()
                        // Perform some cautionary sanitization.
                        .filter(|c| !c.is_whitespace())
                        .collect()
                        .split("charset=")
                        .get(1)
                        .unwrap_or("utf-8")
                }
            },
        }
    }

    fn as_bytes(&self) -> String {
        let mut buf = String::new();
        for (key, value) in self.header {
            buf.push_str(key);
            buf.push_str(": ");
            buf.push_str(self.header[value]);
            buf.push_str("\r\n");
        }
        buf.push_str("\r\n");
        buf.push_str(self.content.to_string());
        buf
    }

    fn response_to_invalid_message(err: Error) -> Response {
        use serde_json::error::Category;
        match err {
            Error::Io(_) => Message::wrap(error::responses::PARSE_ERROR),
            Error::Header(_) => Message::wrap(error::responses::PARSE_ERROR),
            Error::Json(err_json) => match err_json.classify() {
                Category::Data => {
                    // TODO
                    Message::wrap(error::responses::PARSE_ERROR)
                }
                _ => Message::wrap(error::responses::PARSE_ERROR),
            },
        }
    }

    fn wrap(json: JsonRpcObject) -> Message {
        let header = IndexMap::new();
        header.insert("Content-Length", json.to_string().len());
        Message {
            header: header,
            content: json,
        }
    }
}

const HEADER_FIELD_CONTENT_LENGTH: &'static str = "Content-Length";
const HEADER_FIELD_CONTENT_TYPE: &'static str = "Content-TYPE";

#[derive(Serialize, Deserialize)]
#[serde(untagged)]
pub enum JsonRpcObject {
    BatchRequest(BatchRequests),
    BatchResponse(BatchResponses),
    Request(Request),
    Response(Response),
}

pub type BatchRequests = Vec<Request>;
pub type BatchResponses = Vec<Response>;

#[derive(Serialize, Deserialize)]
pub enum Id {
    String(String),
    Null,
    Number(f64),
}

#[derive(Serialize, Deserialize)]
pub struct Request {
    #[serde(default)]
    jsonrpc: JsonRpcProtocolVersion,
    #[serde(flatten)]
    rpc: Rpc,
    id: Option<Id>,
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "method", content = "params")]
pub enum Rpc {
    // General
    #[serde(rename = "initialize")]
    Initialize(lsp::general::Initialize),
    #[serde(rename = "initialized")]
    Initialized(lsp::utils::Void),
    #[serde(rename = "shutdown")]
    Shutdown(lsp::utils::Void),
    #[serde(rename = "exit")]
    Exit(lsp::utils::Void),
    #[serde(rename = "$/cancelRequest")]
    CancelRequest(lsp::general::CancelRequest),
    // Workspace
    #[serde(rename = "workspace/didChangeWorkspaceFolders")]
    DidChangeFolders(lsp::workspace::DidChangeFolders),
    #[serde(rename = "workspace/didChangeConfiguration")]
    DidChangeConfiguration(lsp::workspace::DidChangeConfiguration),
    #[serde(rename = "workspace/didChangeWatchedFiles")]
    DidChangeWatchedFiles(lsp::workspace::DidChangeWatchedFiles),
    #[serde(rename = "workspace/symbol")]
    Symbol(lsp::workspace::Symbols),
    #[serde(rename = "workspace/executeCommand")]
    ExecuteCommand(lsp::workspace::ExecuteCommand),
    // Text Synchronization
    #[serde(rename = "textDocument/didOpen")]
    DidOpen(lsp::utils::FileIdWrapper),
    #[serde(rename = "textDocument/didChange")]
    DidChange(lsp::sync::DidChange),
    #[serde(rename = "textDocument/willSave")]
    // TODO: request
    WillSave(lsp::sync::WillSave),
    #[serde(rename = "textDocument/didSave")]
    DidSave(lsp::sync::DidSave),
    #[serde(rename = "textDocument/didClose")]
    DidClose(lsp::utils::FileIdWrapper),
    // Language features
    #[serde(rename = "textDocument/completion")]
    Completion(lsp::features::Completion),
    #[serde(rename = "textDocument/hover")]
    Hover(lsp::features::Hover),
    #[serde(rename = "textDocument/signatureHelp")]
    SignatureHelp(lsp::features::SignatureHelp),
    #[serde(rename = "textDocument/definition")]
    GotoDefinition(lsp::utils::FilePosition),
    #[serde(rename = "textDocument/typeDefinition")]
    GotoTypeDefinition(lsp::utils::FilePosition),
    #[serde(rename = "textDocument/implementation")]
    GotoImplementation(lsp::utils::FilePosition),
    #[serde(rename = "textDocument/references")]
    References(lsp::features::References),
    #[serde(rename = "textDocument/documentHighlight’")]
    Highlights(lsp::features::Highlights),
    #[serde(rename = "textDocument/documentSymbol")]
    Symbols(lsp::utils::FileIdWrapper),
    #[serde(rename = "textDocument/codeAction")]
    CodeAction(lsp::utils::FileIdWrapper),
    #[serde(rename = "textDocument/codeLens")]
    CodeLens(lsp::utils::FileIdWrapper),
    #[serde(rename = "textDocument/documentLink")]
    Links(lsp::utils::FileIdWrapper),
    #[serde(rename = "textDocument/documentColor")]
    Colors(lsp::utils::FileIdWrapper),
    #[serde(rename = "textDocument/colorPresentation")]
    ColorPresentations(lsp::features::ColorPresentations),
    #[serde(rename = "textDocument/formatting")]
    Format(lsp::features::Format),
    #[serde(rename = "textDocument/rangeFormatting")]
    FormatInRange(lsp::features::FormatInRange),
    #[serde(rename = "textDocument/onTypeFormatting")]
    FormatWhileTyping(lsp::features::FormatWhileTyping),
    #[serde(rename = "textDocument/rename")]
    Rename(lsp::features::Rename),
}

#[derive(Serialize, Deserialize)]
pub struct Response {
    #[serde(default)]
    jsonrpc: JsonRpcProtocolVersion,
    #[serde(flatten)]
    body: ResponseBody,
    id: Id,
}

#[derive(Serialize, Deserialize)]
pub enum JsonRpcProtocolVersion {
    #[serde(rename = "2.0")]
    TwoPointOh,
}

impl Default for JsonRpcProtocolVersion {
    fn default() -> JsonRpcProtocolVersion {
        JsonRpcProtocolVersion::TwoPointOh
    }
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ResponseBody {
    Result(JsonValue),
    Error(Error),
}

#[derive(Serialize, Deserialize)]
pub struct Error {
    code: i64,
    message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    data: Option<JsonValue>,
}

pub mod error {

    use std::convert::From;
    use std::error;
    use std::io::Error as IoError;

    use serde_json::{self, Error as JsonError};

    #[derive(Debug)]
    pub enum Error {
        Header(HeaderError),
        Json(JsonError),
        Io(IoError),
    }

    pub enum HeaderError {
        MissingHeaderField { missing_header_field_name: String },
        IllegalHeaderField { line_number: u64 },
    }

    impl From<HeaderError> for Error {
        fn from(err: HeaderError) -> Error {
            Error::Header(err)
        }
    }

    impl From<JsonError> for Error {
        fn from(err: JsonError) -> Error {
            Error::Json(err)
        }
    }

    impl From<IoError> for Error {
        fn from(err: IoError) -> Error {
            Error::Io(err)
        }
    }

    impl error::Error for Error {
        fn description(&self) -> &str {
            match self {
                Error::Header(_) => "The message has an invalid header.",
                Error::Json(err) => err.description(),
                Error::Io(err) => err.description(),
            }
        }
    }

    impl fmt::Display for CliError {
        fn fmt(&self, f: &mut Formatter) -> fmt::Result {
            match *self {
                // Both underlying errors already impl `Display`, so we defer to
                // their implementations.
                CliError::Io(ref err) => write!(f, "IO error: {}", err),
                CliError::Parse(ref err) => write!(f, "Parse error: {}", err),
            }
        }
    }

    pub mod responses {

        use langserver::jsonrpc::{Id, Response, ResponseBody};

        pub const PARSE_ERROR: Response = Response {
            body: ResponseBody::Error {
                code: -32700,
                message: "Parse error",
            },
            id: Id::Null,
        };

        pub const INVALID_REQUEST: Response = Response {
            body: ResponseBody::Error {
                code: -32600,
                message: "Invalid Request",
            },
            id: Id::Null,
        };

        pub const METHOD_NOT_FOUND: Response = Response {
            body: ResponseBody::Error {
                code: -32601,
                message: "Method not found",
            },
            id: Id::Null,
        };

        pub const INVALID_PARAMS: Response = Response {
            body: ResponseBody::Error {
                code: -32602,
                message: "Invalid params",
            },
            id: Id::Null,
        };

        pub const INTERNAL_ERROR: Response = Response {
            body: ResponseBody::Error {
                code: -32603,
                message: "Internal error",
            },
            id: Id::Null,
        };

        pub const REQUEST_CANCELLED: Response = Response {
            body: ResponseBody::Error {
                code: -32800,
                message: "Request cancelled",
            },
            id: Id::Null,
        };
    }
}
