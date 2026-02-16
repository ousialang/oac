use std::collections::HashMap;
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};

use serde::Serialize;
use serde_json::{json, Value};
use url::Url;

use crate::{flat_imports, ir, parser, tokenizer};

#[derive(Debug)]
struct DocumentState {
    text: String,
    version: Option<i64>,
}

#[derive(Debug)]
enum LspControl {
    Continue,
    Exit,
}

#[derive(Clone, Debug, Serialize)]
struct LspPosition {
    line: u32,
    character: u32,
}

#[derive(Clone, Debug, Serialize)]
struct LspRange {
    start: LspPosition,
    end: LspPosition,
}

#[derive(Clone, Debug, Serialize)]
struct LspDiagnostic {
    range: LspRange,
    severity: u32,
    source: String,
    message: String,
}

#[derive(Clone, Debug)]
struct IndexedSymbol {
    name: String,
    kind: u32,
    detail: String,
    uri: String,
    range: LspRange,
    selection_range: LspRange,
}

#[derive(Clone, Debug)]
struct FileContent {
    uri: String,
    text: String,
}

pub fn run() -> anyhow::Result<()> {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut reader = BufReader::new(stdin.lock());
    let mut writer = BufWriter::new(stdout.lock());
    let mut documents: HashMap<String, DocumentState> = HashMap::new();
    let mut shutdown_requested = false;

    while let Some(message) = read_lsp_message(&mut reader)? {
        match handle_lsp_message(
            &message,
            &mut documents,
            &mut writer,
            &mut shutdown_requested,
        )? {
            LspControl::Continue => {}
            LspControl::Exit => break,
        }
    }

    Ok(())
}

fn read_lsp_message(reader: &mut impl BufRead) -> anyhow::Result<Option<Value>> {
    let mut content_length: Option<usize> = None;

    loop {
        let mut line = String::new();
        let bytes_read = reader.read_line(&mut line)?;
        if bytes_read == 0 {
            return Ok(None);
        }

        if line == "\r\n" {
            break;
        }

        if let Some(value) = line.strip_prefix("Content-Length:") {
            content_length = Some(value.trim().parse::<usize>()?);
        }
    }

    let content_length =
        content_length.ok_or_else(|| anyhow::anyhow!("missing Content-Length header"))?;

    let mut body = vec![0_u8; content_length];
    reader.read_exact(&mut body)?;
    let payload: Value = serde_json::from_slice(&body)?;
    Ok(Some(payload))
}

fn write_lsp_message(writer: &mut impl Write, payload: &Value) -> anyhow::Result<()> {
    let bytes = serde_json::to_vec(payload)?;
    write!(writer, "Content-Length: {}\r\n\r\n", bytes.len())?;
    writer.write_all(&bytes)?;
    writer.flush()?;
    Ok(())
}

fn handle_lsp_message(
    message: &Value,
    documents: &mut HashMap<String, DocumentState>,
    writer: &mut impl Write,
    shutdown_requested: &mut bool,
) -> anyhow::Result<LspControl> {
    let method = message.get("method").and_then(Value::as_str);
    let id = message.get("id").cloned();
    let params = message.get("params").cloned().unwrap_or(Value::Null);

    let Some(method) = method else {
        return Ok(LspControl::Continue);
    };

    match method {
        "initialize" => {
            let response = json!({
                "jsonrpc": "2.0",
                "id": id,
                "result": {
                    "capabilities": {
                        "textDocumentSync": {
                            "openClose": true,
                            "change": 1,
                            "save": {
                                "includeText": true
                            }
                        },
                        "definitionProvider": true,
                        "hoverProvider": true,
                        "documentSymbolProvider": true,
                        "referencesProvider": true,
                        "completionProvider": {
                            "resolveProvider": false,
                            "triggerCharacters": ["."]
                        }
                    },
                    "serverInfo": {
                        "name": "oac",
                        "version": env!("CARGO_PKG_VERSION")
                    }
                }
            });
            write_lsp_message(writer, &response)?;
        }
        "initialized" => {}
        "shutdown" => {
            *shutdown_requested = true;
            let response = json!({
                "jsonrpc": "2.0",
                "id": id,
                "result": Value::Null
            });
            write_lsp_message(writer, &response)?;
        }
        "exit" => {
            if !*shutdown_requested {
                return Ok(LspControl::Exit);
            }
            return Ok(LspControl::Exit);
        }
        "textDocument/didOpen" => {
            if let (Some(uri), Some(text)) = (
                json_str(&params, "/textDocument/uri"),
                json_str(&params, "/textDocument/text"),
            ) {
                let version = params
                    .pointer("/textDocument/version")
                    .and_then(Value::as_i64);
                documents.insert(
                    uri.to_string(),
                    DocumentState {
                        text: text.to_string(),
                        version,
                    },
                );
                publish_diagnostics_for_document(uri, documents.get(uri), writer)?;
            }
        }
        "textDocument/didChange" => {
            if let Some(uri) = json_str(&params, "/textDocument/uri") {
                let version = params
                    .pointer("/textDocument/version")
                    .and_then(Value::as_i64);
                if let Some(new_text) = params
                    .pointer("/contentChanges/0/text")
                    .and_then(Value::as_str)
                {
                    documents.insert(
                        uri.to_string(),
                        DocumentState {
                            text: new_text.to_string(),
                            version,
                        },
                    );
                    publish_diagnostics_for_document(uri, documents.get(uri), writer)?;
                }
            }
        }
        "textDocument/didSave" => {
            if let Some(uri) = json_str(&params, "/textDocument/uri") {
                if let Some(saved_text) = params.pointer("/text").and_then(Value::as_str) {
                    let version = documents.get(uri).and_then(|doc| doc.version);
                    documents.insert(
                        uri.to_string(),
                        DocumentState {
                            text: saved_text.to_string(),
                            version,
                        },
                    );
                }
                publish_diagnostics_for_document(uri, documents.get(uri), writer)?;
            }
        }
        "textDocument/didClose" => {
            if let Some(uri) = json_str(&params, "/textDocument/uri") {
                documents.remove(uri);
                publish_diagnostics(uri, &[], None, writer)?;
            }
        }
        "textDocument/definition" => {
            let uri = json_str(&params, "/textDocument/uri");
            let line = params.pointer("/position/line").and_then(Value::as_u64);
            let character = params
                .pointer("/position/character")
                .and_then(Value::as_u64);
            let result = if let (Some(uri), Some(line), Some(character)) = (uri, line, character) {
                definition_response(uri, line as u32, character as u32, documents)
            } else {
                Value::Null
            };
            let response = json!({
                "jsonrpc": "2.0",
                "id": id,
                "result": result
            });
            write_lsp_message(writer, &response)?;
        }
        "textDocument/hover" => {
            let uri = json_str(&params, "/textDocument/uri");
            let line = params.pointer("/position/line").and_then(Value::as_u64);
            let character = params
                .pointer("/position/character")
                .and_then(Value::as_u64);
            let result = if let (Some(uri), Some(line), Some(character)) = (uri, line, character) {
                hover_response(uri, line as u32, character as u32, documents)
            } else {
                Value::Null
            };
            let response = json!({
                "jsonrpc": "2.0",
                "id": id,
                "result": result
            });
            write_lsp_message(writer, &response)?;
        }
        "textDocument/documentSymbol" => {
            let result = if let Some(uri) = json_str(&params, "/textDocument/uri") {
                document_symbol_response(uri, documents)
            } else {
                Value::Array(vec![])
            };
            let response = json!({
                "jsonrpc": "2.0",
                "id": id,
                "result": result
            });
            write_lsp_message(writer, &response)?;
        }
        "textDocument/references" => {
            let uri = json_str(&params, "/textDocument/uri");
            let line = params.pointer("/position/line").and_then(Value::as_u64);
            let character = params
                .pointer("/position/character")
                .and_then(Value::as_u64);
            let include_declaration = params
                .pointer("/context/includeDeclaration")
                .and_then(Value::as_bool)
                .unwrap_or(true);
            let result = if let (Some(uri), Some(line), Some(character)) = (uri, line, character) {
                references_response(
                    uri,
                    line as u32,
                    character as u32,
                    include_declaration,
                    documents,
                )
            } else {
                Value::Array(vec![])
            };
            let response = json!({
                "jsonrpc": "2.0",
                "id": id,
                "result": result
            });
            write_lsp_message(writer, &response)?;
        }
        "textDocument/completion" => {
            let uri = json_str(&params, "/textDocument/uri");
            let line = params.pointer("/position/line").and_then(Value::as_u64);
            let character = params
                .pointer("/position/character")
                .and_then(Value::as_u64);
            let result = if let (Some(uri), Some(line), Some(character)) = (uri, line, character) {
                completion_response(uri, line as u32, character as u32, documents)
            } else {
                Value::Array(vec![])
            };
            let response = json!({
                "jsonrpc": "2.0",
                "id": id,
                "result": result
            });
            write_lsp_message(writer, &response)?;
        }
        _ => {
            if id.is_some() {
                let response = json!({
                    "jsonrpc": "2.0",
                    "id": id,
                    "error": {
                        "code": -32601,
                        "message": format!("method not found: {method}")
                    }
                });
                write_lsp_message(writer, &response)?;
            }
        }
    }

    Ok(LspControl::Continue)
}

fn publish_diagnostics_for_document(
    uri: &str,
    document: Option<&DocumentState>,
    writer: &mut impl Write,
) -> anyhow::Result<()> {
    let Some(document) = document else {
        publish_diagnostics(uri, &[], None, writer)?;
        return Ok(());
    };

    let diagnostics = analyze_document(&document.text, uri_to_path(uri).as_deref());
    publish_diagnostics(uri, &diagnostics, document.version, writer)
}

fn publish_diagnostics(
    uri: &str,
    diagnostics: &[LspDiagnostic],
    version: Option<i64>,
    writer: &mut impl Write,
) -> anyhow::Result<()> {
    let mut params = json!({
        "uri": uri,
        "diagnostics": diagnostics
    });
    if let Some(version) = version {
        params["version"] = json!(version);
    }

    let notification = json!({
        "jsonrpc": "2.0",
        "method": "textDocument/publishDiagnostics",
        "params": params
    });
    write_lsp_message(writer, &notification)
}

fn analyze_document(source: &str, source_path: Option<&Path>) -> Vec<LspDiagnostic> {
    let tokens = match tokenizer::tokenize(source.to_string()) {
        Ok(tokens) => tokens,
        Err(err) => {
            return vec![syntax_error_diagnostic(
                err.message,
                err.position.line,
                err.position.column,
            )]
        }
    };

    let ast = match parser::parse(tokens) {
        Ok(ast) => ast,
        Err(err) => return vec![generic_error_diagnostic(format!("parse error: {err}"))],
    };

    let merged_ast = if let Some(source_path) = source_path {
        match flat_imports::resolve_ast(ast, source_path) {
            Ok(ast) => ast,
            Err(err) => return vec![generic_error_diagnostic(format!("import error: {err}"))],
        }
    } else {
        ast
    };

    if let Err(err) = ir::resolve(merged_ast) {
        // Library files or scratch buffers may intentionally omit `main`.
        if err.to_string().contains("main function not defined") {
            return vec![];
        }
        return vec![generic_error_diagnostic(format!("type error: {err}"))];
    }

    vec![]
}

fn syntax_error_diagnostic(
    message: String,
    line_1_based: u32,
    column_1_based: u32,
) -> LspDiagnostic {
    let line = line_1_based.saturating_sub(1);
    let character = column_1_based.saturating_sub(1);
    LspDiagnostic {
        range: LspRange {
            start: LspPosition { line, character },
            end: LspPosition {
                line,
                character: character + 1,
            },
        },
        severity: 1,
        source: "oac".to_string(),
        message,
    }
}

fn generic_error_diagnostic(message: String) -> LspDiagnostic {
    LspDiagnostic {
        range: LspRange {
            start: LspPosition {
                line: 0,
                character: 0,
            },
            end: LspPosition {
                line: 0,
                character: 1,
            },
        },
        severity: 1,
        source: "oac".to_string(),
        message,
    }
}

fn json_str<'a>(value: &'a Value, pointer: &str) -> Option<&'a str> {
    value.pointer(pointer).and_then(Value::as_str)
}

fn uri_to_path(uri: &str) -> Option<PathBuf> {
    let parsed = Url::parse(uri).ok()?;
    if parsed.scheme() != "file" {
        return None;
    }
    parsed.to_file_path().ok()
}

fn path_to_uri(path: &Path) -> Option<String> {
    Url::from_file_path(path).ok().map(|uri| uri.to_string())
}

fn definition_response(
    uri: &str,
    line: u32,
    character: u32,
    documents: &HashMap<String, DocumentState>,
) -> Value {
    let Some(text) = text_for_uri(uri, documents) else {
        return Value::Null;
    };
    let Some((word, _range)) = word_at_position(&text, line, character) else {
        return Value::Null;
    };
    let symbols = symbols_for_project(uri, documents);
    let mut matches = symbols
        .into_iter()
        .filter(|s| s.name == word)
        .collect::<Vec<_>>();
    if matches.is_empty() {
        return Value::Null;
    }
    matches.sort_by_key(|s| if s.uri == uri { 0 } else { 1 });
    let target = matches.remove(0);
    json!({
        "uri": target.uri,
        "range": target.selection_range
    })
}

fn hover_response(
    uri: &str,
    line: u32,
    character: u32,
    documents: &HashMap<String, DocumentState>,
) -> Value {
    let Some(text) = text_for_uri(uri, documents) else {
        return Value::Null;
    };
    let Some((word, range)) = word_at_position(&text, line, character) else {
        return Value::Null;
    };
    let symbols = symbols_for_project(uri, documents);
    let Some(symbol) = symbols.into_iter().find(|s| s.name == word) else {
        return Value::Null;
    };

    let kind = symbol_kind_name(symbol.kind);
    json!({
        "contents": {
            "kind": "markdown",
            "value": format!("`{kind}` **{}**\n\n{}", symbol.name, symbol.detail)
        },
        "range": range
    })
}

fn document_symbol_response(uri: &str, documents: &HashMap<String, DocumentState>) -> Value {
    let Some(text) = text_for_uri(uri, documents) else {
        return Value::Array(vec![]);
    };
    let symbols = scan_symbols_in_file(uri, &text);
    Value::Array(
        symbols
            .into_iter()
            .map(|symbol| {
                json!({
                    "name": symbol.name,
                    "detail": symbol.detail,
                    "kind": symbol.kind,
                    "range": symbol.range,
                    "selectionRange": symbol.selection_range,
                    "children": []
                })
            })
            .collect(),
    )
}

fn references_response(
    uri: &str,
    line: u32,
    character: u32,
    include_declaration: bool,
    documents: &HashMap<String, DocumentState>,
) -> Value {
    let Some(text) = text_for_uri(uri, documents) else {
        return Value::Array(vec![]);
    };
    let Some((word, _)) = word_at_position(&text, line, character) else {
        return Value::Array(vec![]);
    };
    let symbols = symbols_for_project(uri, documents);
    let project_files = collect_project_files(uri, documents);

    let mut locations = vec![];
    for file in project_files {
        for range in find_identifier_ranges_in_text(&file.text, &word) {
            locations.push((file.uri.clone(), range));
        }
    }

    if !include_declaration {
        let declaration_ranges = symbols
            .iter()
            .filter(|s| s.name == word)
            .map(|s| (s.uri.as_str(), &s.selection_range))
            .collect::<Vec<_>>();
        locations.retain(|(loc_uri, loc_range)| {
            !declaration_ranges.iter().any(|(decl_uri, decl_range)| {
                *decl_uri == loc_uri.as_str() && ranges_equal(loc_range, decl_range)
            })
        });
    }

    Value::Array(
        locations
            .into_iter()
            .map(|(loc_uri, loc_range)| {
                json!({
                    "uri": loc_uri,
                    "range": loc_range
                })
            })
            .collect(),
    )
}

fn completion_response(
    uri: &str,
    line: u32,
    character: u32,
    documents: &HashMap<String, DocumentState>,
) -> Value {
    let Some(text) = text_for_uri(uri, documents) else {
        return Value::Array(vec![]);
    };
    let prefix = identifier_prefix_at_position(&text, line, character);

    let mut items = vec![];
    let mut seen = HashMap::<String, ()>::new();

    for keyword in [
        "fun",
        "struct",
        "enum",
        "template",
        "instantiate",
        "import",
        "if",
        "else",
        "while",
        "return",
        "match",
        "true",
        "false",
    ] {
        if !prefix.is_empty() && !keyword.starts_with(prefix.as_str()) {
            continue;
        }
        if seen.contains_key(keyword) {
            continue;
        }
        seen.insert(keyword.to_string(), ());
        items.push(json!({
            "label": keyword,
            "kind": 14,
            "detail": "keyword"
        }));
    }

    let symbols = symbols_for_project(uri, documents);
    for symbol in symbols {
        if !prefix.is_empty() && !symbol.name.starts_with(prefix.as_str()) {
            continue;
        }
        if seen.contains_key(&symbol.name) {
            continue;
        }
        seen.insert(symbol.name.clone(), ());
        items.push(json!({
            "label": symbol.name,
            "kind": completion_kind_from_symbol_kind(symbol.kind),
            "detail": symbol.detail
        }));
    }

    Value::Array(items)
}

fn symbols_for_project(
    uri: &str,
    documents: &HashMap<String, DocumentState>,
) -> Vec<IndexedSymbol> {
    collect_project_files(uri, documents)
        .iter()
        .flat_map(|file| scan_symbols_in_file(&file.uri, &file.text))
        .collect()
}

fn collect_project_files(
    uri: &str,
    documents: &HashMap<String, DocumentState>,
) -> Vec<FileContent> {
    let Some(root_path) = uri_to_path(uri) else {
        return vec![];
    };
    let Some(root_uri) = path_to_uri(&root_path) else {
        return vec![];
    };

    let mut output = vec![];
    let mut seen = HashMap::<PathBuf, ()>::new();
    let mut stack = vec![(root_path, root_uri)];

    while let Some((path, canonical_uri)) = stack.pop() {
        let canonical_path = path.canonicalize().unwrap_or(path.clone());
        if seen.contains_key(&canonical_path) {
            continue;
        }
        seen.insert(canonical_path.clone(), ());

        let path_uri = path_to_uri(&canonical_path).unwrap_or(canonical_uri.clone());
        let text = if let Some(open_doc) = documents.get(&path_uri) {
            open_doc.text.clone()
        } else if canonical_uri != path_uri {
            if let Some(open_doc) = documents.get(&canonical_uri) {
                open_doc.text.clone()
            } else {
                match std::fs::read_to_string(&canonical_path) {
                    Ok(text) => text,
                    Err(_) => continue,
                }
            }
        } else {
            match std::fs::read_to_string(&canonical_path) {
                Ok(text) => text,
                Err(_) => continue,
            }
        };

        let file = FileContent {
            uri: path_uri.clone(),
            text: text.clone(),
        };
        output.push(file);

        let imports = parse_imports(&text);
        let source_dir = match canonical_path.parent() {
            Some(dir) => dir,
            None => continue,
        };
        for import in imports {
            if let Some(import_path) = resolve_import_path(source_dir, &import) {
                let import_uri = path_to_uri(&import_path).unwrap_or_else(|| path_uri.clone());
                stack.push((import_path, import_uri));
            }
        }
    }

    output
}

fn parse_imports(text: &str) -> Vec<String> {
    let tokens = match tokenizer::tokenize(text.to_string()) {
        Ok(tokens) => tokens,
        Err(_) => return vec![],
    };
    let ast = match parser::parse(tokens) {
        Ok(ast) => ast,
        Err(_) => return vec![],
    };
    ast.imports.into_iter().map(|i| i.path).collect()
}

fn resolve_import_path(source_dir: &Path, import_path: &str) -> Option<PathBuf> {
    let import = Path::new(import_path);
    if import.is_absolute() {
        return None;
    }
    let components = import.components().collect::<Vec<_>>();
    if !(components.len() == 1 && matches!(components[0], std::path::Component::Normal(_))) {
        return None;
    }
    if import.extension().and_then(|ext| ext.to_str()) != Some("oa") {
        return None;
    }
    let candidate = source_dir.join(import);
    if candidate.exists() {
        Some(candidate)
    } else {
        None
    }
}

fn text_for_uri(uri: &str, documents: &HashMap<String, DocumentState>) -> Option<String> {
    if let Some(doc) = documents.get(uri) {
        return Some(doc.text.clone());
    }
    let path = uri_to_path(uri)?;
    std::fs::read_to_string(path).ok()
}

fn scan_symbols_in_file(uri: &str, text: &str) -> Vec<IndexedSymbol> {
    let mut symbols = vec![];
    for (line_idx, line) in text.lines().enumerate() {
        if line.is_empty() {
            continue;
        }
        if line
            .chars()
            .next()
            .map(|ch| ch.is_ascii_whitespace())
            .unwrap_or(false)
        {
            continue;
        }
        if let Some((name, detail, kind)) = parse_symbol_declaration(line) {
            if let Some(start_char) = line.find(&name) {
                let end_char = start_char + name.len();
                let range = LspRange {
                    start: LspPosition {
                        line: line_idx as u32,
                        character: 0,
                    },
                    end: LspPosition {
                        line: line_idx as u32,
                        character: line.len() as u32,
                    },
                };
                let selection_range = LspRange {
                    start: LspPosition {
                        line: line_idx as u32,
                        character: start_char as u32,
                    },
                    end: LspPosition {
                        line: line_idx as u32,
                        character: end_char as u32,
                    },
                };
                symbols.push(IndexedSymbol {
                    name,
                    kind,
                    detail,
                    uri: uri.to_string(),
                    range,
                    selection_range,
                });
            }
        }
    }
    symbols
}

fn parse_symbol_declaration(line: &str) -> Option<(String, String, u32)> {
    if let Some(rest) = line.strip_prefix("fun ") {
        let name = parse_symbol_name(rest)?;
        return Some((name.clone(), format!("fun {name}"), 12));
    }
    if let Some(rest) = line.strip_prefix("struct ") {
        let name = parse_symbol_name(rest)?;
        return Some((name.clone(), format!("struct {name}"), 23));
    }
    if let Some(rest) = line.strip_prefix("enum ") {
        let name = parse_symbol_name(rest)?;
        return Some((name.clone(), format!("enum {name}"), 10));
    }
    if let Some(rest) = line.strip_prefix("template ") {
        let name = parse_symbol_name(rest)?;
        return Some((name.clone(), format!("template {name}"), 5));
    }
    if let Some(rest) = line.strip_prefix("instantiate ") {
        let name = parse_symbol_name(rest)?;
        return Some((name.clone(), format!("instantiate {name}"), 5));
    }
    None
}

fn parse_symbol_name(rest: &str) -> Option<String> {
    let mut out = String::new();
    for ch in rest.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            break;
        }
    }
    if out.is_empty() {
        None
    } else {
        Some(out)
    }
}

fn identifier_prefix_at_position(text: &str, line: u32, character: u32) -> String {
    let Some(line_str) = text.lines().nth(line as usize) else {
        return String::new();
    };
    let chars = line_str.chars().collect::<Vec<_>>();
    let mut idx = (character as usize).min(chars.len());
    while idx > 0 && is_ident_char(chars[idx - 1]) {
        idx -= 1;
    }
    let mut end = idx;
    while end < chars.len() && is_ident_char(chars[end]) && end < character as usize {
        end += 1;
    }
    chars[idx..end].iter().collect()
}

fn find_identifier_ranges_in_text(text: &str, needle: &str) -> Vec<LspRange> {
    let mut out = vec![];
    if needle.is_empty() {
        return out;
    }
    for (line_idx, line) in text.lines().enumerate() {
        let chars = line.chars().collect::<Vec<_>>();
        let n_chars = needle.chars().collect::<Vec<_>>();
        if n_chars.is_empty() || n_chars.len() > chars.len() {
            continue;
        }
        let mut i = 0;
        while i + n_chars.len() <= chars.len() {
            if chars[i..i + n_chars.len()] == n_chars[..] {
                let left_ok = i == 0 || !is_ident_char(chars[i - 1]);
                let right_ok =
                    i + n_chars.len() == chars.len() || !is_ident_char(chars[i + n_chars.len()]);
                if left_ok && right_ok {
                    out.push(LspRange {
                        start: LspPosition {
                            line: line_idx as u32,
                            character: i as u32,
                        },
                        end: LspPosition {
                            line: line_idx as u32,
                            character: (i + n_chars.len()) as u32,
                        },
                    });
                }
                i += n_chars.len();
            } else {
                i += 1;
            }
        }
    }
    out
}

fn ranges_equal(left: &LspRange, right: &LspRange) -> bool {
    left.start.line == right.start.line
        && left.start.character == right.start.character
        && left.end.line == right.end.line
        && left.end.character == right.end.character
}

fn word_at_position(text: &str, line: u32, character: u32) -> Option<(String, LspRange)> {
    let line_str = text.lines().nth(line as usize)?;
    let chars = line_str.chars().collect::<Vec<_>>();
    if chars.is_empty() {
        return None;
    }

    let mut idx = character as usize;
    if idx >= chars.len() {
        idx = chars.len().saturating_sub(1);
    }
    if !is_ident_char(chars[idx]) {
        if idx == 0 || !is_ident_char(chars[idx - 1]) {
            return None;
        }
        idx -= 1;
    }

    let mut start = idx;
    while start > 0 && is_ident_char(chars[start - 1]) {
        start -= 1;
    }
    let mut end = idx + 1;
    while end < chars.len() && is_ident_char(chars[end]) {
        end += 1;
    }

    let word: String = chars[start..end].iter().collect();
    Some((
        word,
        LspRange {
            start: LspPosition {
                line,
                character: start as u32,
            },
            end: LspPosition {
                line,
                character: end as u32,
            },
        },
    ))
}

fn is_ident_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

fn symbol_kind_name(kind: u32) -> &'static str {
    match kind {
        5 => "class",
        10 => "enum",
        12 => "function",
        23 => "struct",
        _ => "symbol",
    }
}

fn completion_kind_from_symbol_kind(kind: u32) -> u32 {
    match kind {
        12 => 3,
        10 => 13,
        23 => 22,
        5 => 7,
        _ => 6,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::fs;

    use super::{
        analyze_document, completion_response, definition_response, document_symbol_response,
        references_response, uri_to_path, DocumentState,
    };

    #[test]
    fn analyze_document_reports_tokenizer_position() {
        let src = "fun main() -> I32 {\n\t$\n}\n";
        let diags = analyze_document(src, None);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("unexpected char '$'"));
        assert_eq!(diags[0].range.start.line, 1);
    }

    #[test]
    fn analyze_document_ok_has_no_diagnostics() {
        let src = "fun main() -> I32 {\n\treturn 0\n}\n";
        let diags = analyze_document(src, None);
        assert!(diags.is_empty());
    }

    #[test]
    fn file_uri_converts_to_path() {
        let uri = "file:///tmp/example.oa";
        let path = uri_to_path(uri).expect("file uri should convert");
        assert!(path.ends_with("example.oa"));
    }

    #[test]
    fn document_symbol_lists_top_level_declarations() {
        let mut docs = HashMap::new();
        let uri = "file:///tmp/doc.oa".to_string();
        docs.insert(
            uri.clone(),
            DocumentState {
                text: "struct Foo {\n\tx: I32,\n}\n\nfun main() -> I32 {\n\treturn 0\n}\n"
                    .to_string(),
                version: Some(1),
            },
        );

        let symbols = document_symbol_response(&uri, &docs);
        let arr = symbols.as_array().expect("document symbols array");
        assert_eq!(arr.len(), 2);
        let names = arr
            .iter()
            .map(|s| s["name"].as_str().unwrap_or_default().to_string())
            .collect::<Vec<_>>();
        assert!(names.contains(&"Foo".to_string()));
        assert!(names.contains(&"main".to_string()));
    }

    #[test]
    fn definition_resolves_imported_symbol() {
        let tmp = tempfile::tempdir().expect("create tempdir");
        let helper_path = tmp.path().join("helper.oa");
        let main_path = tmp.path().join("main.oa");
        fs::write(&helper_path, "fun helper() -> I32 {\n\treturn 7\n}\n").expect("write helper");
        fs::write(
            &main_path,
            "import \"helper.oa\"\n\nfun main() -> I32 {\n\treturn helper()\n}\n",
        )
        .expect("write main");

        let main_uri = url::Url::from_file_path(&main_path)
            .expect("main file uri")
            .to_string();
        let helper_uri = url::Url::from_file_path(&helper_path)
            .expect("helper file uri")
            .to_string();
        let docs = HashMap::new();

        let result = definition_response(&main_uri, 3, 9, &docs);
        let resolved_uri = result["uri"].as_str().expect("definition uri");
        let resolved_path = uri_to_path(resolved_uri)
            .expect("resolved definition uri should map to path")
            .canonicalize()
            .expect("canonical resolved path");
        let expected_path = uri_to_path(&helper_uri)
            .expect("expected helper uri should map to path")
            .canonicalize()
            .expect("canonical expected path");
        assert_eq!(resolved_path, expected_path);
    }

    #[test]
    fn references_find_definition_and_usage_across_imports() {
        let tmp = tempfile::tempdir().expect("create tempdir");
        let lib_path = tmp.path().join("lib.oa");
        let main_path = tmp.path().join("main.oa");
        fs::write(&lib_path, "fun lib_fn() -> I32 {\n\treturn 7\n}\n").expect("write lib");
        fs::write(
            &main_path,
            "import \"lib.oa\"\n\nfun main() -> I32 {\n\treturn lib_fn()\n}\n",
        )
        .expect("write main");

        let main_uri = url::Url::from_file_path(&main_path)
            .expect("main file uri")
            .to_string();
        let refs = references_response(&main_uri, 3, 10, true, &HashMap::new());
        let arr = refs.as_array().expect("references response array");
        assert!(
            arr.len() >= 2,
            "expected at least definition + usage references, got {arr:?}"
        );
    }

    #[test]
    fn completion_suggests_matching_symbol_names() {
        let mut docs = HashMap::new();
        let uri = "file:///tmp/completion.oa".to_string();
        docs.insert(
            uri.clone(),
            DocumentState {
                text:
                    "fun alpha() -> I32 {\n\treturn 1\n}\n\nfun main() -> I32 {\n\treturn al\n}\n"
                        .to_string(),
                version: Some(1),
            },
        );

        let result = completion_response(&uri, 5, 10, &docs);
        let items = result.as_array().expect("completion array");
        assert!(
            items.iter().any(|item| item["label"] == "alpha"),
            "expected alpha completion, got {items:?}"
        );
    }
}
