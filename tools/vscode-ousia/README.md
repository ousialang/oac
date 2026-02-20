# Ousia VS Code Extension

This extension adds language support for Ousia (`.oa`) files in VS Code and connects to the compiler's built-in language server (`oac lsp`).

## Features

- Language registration for `.oa`
- Basic syntax highlighting
- LSP-backed diagnostics, definitions, hover, references, document symbols, and completion via `oac lsp`
- `Ousia: Restart Language Server` command

## Prerequisites

- VS Code 1.90+
- `oac` available on `PATH`, or configured through `ousia.server.path`

## Settings

- `ousia.server.path`: path to the `oac` executable (default: `oac`)
- `ousia.server.args`: extra CLI args inserted before `lsp` (`--stdio` is ignored because `oac lsp` already uses stdio)
- `ousia.trace.server`: LSP trace level (`off`, `messages`, `verbose`)

## Develop Locally

```bash
cd tools/vscode-ousia
npm install
npm run build
```

Then in VS Code:

1. Open `tools/vscode-ousia`
2. Press `F5` to launch an Extension Development Host
3. Open any `.oa` file to activate the extension

## Package

```bash
cd tools/vscode-ousia
npx @vscode/vsce package
```
