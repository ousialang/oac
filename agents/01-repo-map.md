# Repository Map

## Purpose

Ousia is an experimental language and compiler implemented in Rust.

The active compiler workspace is:
- `Cargo.toml` (workspace root)
- `crates/oac` (CLI + tokenizer/parser/type checker/IR/QBE backend/RISC-V SMT)
- `crates/qbe-rs` (QBE Rust bindings/wrapper)
- `crates/qbe-smt` (QBE-to-SMT CHC/fixedpoint encoding support for invariant proving)

Editor tooling in this repository:
- `tools/vscode-ousia` (VS Code extension client for `oac lsp`)

## High-Value Paths

- `crates/oac/src/main.rs`: CLI entrypoint and build pipeline orchestration.
- `crates/oac/src/bench_prove.rs`: proving benchmark suite (`oac bench-prove`) with baseline/report handling.
- `crates/oac/src/diagnostics.rs`: shared compiler diagnostic model and Ariadne rendering used by CLI and LSP.
- `crates/oac/src/flat_imports.rs`: shared flat import resolver used by both user source and stdlib loading.
- `crates/oac/src/ast_walk.rs`: shared AST traversal helpers (expression-path indexing + call walking) reused across resolve and verification passes.
- `crates/oac/src/verification_checker.rs`: shared prove/invariant checker assembly helpers for QBE+CHC verification.
- `crates/oac/src/symbol_keys.rs`: shared trait symbol key/mangling helpers used by resolve + codegen.
- `crates/oac/src/lsp.rs`: stdio LSP server loop (`oac lsp`) and diagnostics publishing.
- `tools/vscode-ousia/src/extension.ts`: VS Code client activation and `oac lsp` process launch.
- `tools/vscode-ousia/package.json`: extension manifest, language registration, and server settings.
- `tools/vscode-ousia/README.md`: extension runtime expectations (notably `oac lsp` launch semantics and settings behavior).
- `crates/oac/src/tokenizer.rs`: eager tokenizer and syntax error model.
- `crates/oac/src/parser.rs`: AST definitions and parser.
- `crates/oac/src/test_framework.rs`: isolated lowering for `test "..." { ... }` declarations into runnable generated functions/main used by `oac test`.
- `crates/oac/src/ir.rs`: type resolution, semantic checks, and resolved IR.
- `crates/oac/src/qbe_backend.rs`: code generation to QBE IR and end-to-end execution tests.
- `crates/oac/src/builtins.rs`: built-in scalar types (including `U8`/`Void`) and builtin type parsing.
- `crates/oac/src/riscv_smt.rs`: ELF -> SMT pipeline for bounded return-to-zero checks.
- `crates/oac/src/verification.rs`: shared proof/invariant verification entrypoint that sequences prove verification before struct-invariant verification.
- `crates/oac/src/prove.rs`: SMT-backed compile-time verification pass for `prove(...)` statement obligations.
- `crates/oac/src/struct_invariants.rs`: SMT-backed compile-time struct invariant verification pass.
- `crates/qbe-smt/src/lib.rs`: public `qbe-smt` API and unit tests.
- `crates/qbe-smt/src/encode.rs`: CHC/Horn fixedpoint encoder for `exit == 1` reachability.
- `crates/qbe-smt/src/encode_extern_models.rs`: shared extern-call model catalog (supported symbols + arity validation metadata) consumed by CHC encoding.
- `crates/qbe-smt/src/classify.rs`: conservative loop non-termination classifier used during `oac build`.
- `crates/oac/src/std/std.oa`: stdlib import entrypoint injected during resolution.
- `crates/oac/src/std/std_*.oa`: split stdlib modules imported by `std/std.oa`.
- `crates/oac/src/std/std_traits.oa`: core trait declarations/impls (`Hash`, `Eq`) used by bounded generics (for example hash table keys).
- `crates/oac/src/std/std_option_result.oa`: core generic sum types (`Option[T]`, `Result[T,E]`) and helper methods.
- `crates/oac/src/std/std_string.oa`: std-owned `Bytes` + `String` representation (`String` enum with literal/heap variants).
- `crates/oac/src/std/std_ref.oa`: pointer wrappers (`Ref[T]`, `Mut[T]`) and typed read/write helper specializations.
- `crates/oac/src/std/std_set.oa`: generic persistent `HashSet[K: Hash + Eq]` operations and set algebra helpers.
- `crates/oac/src/std/std_vec.oa`: generic persistent `Vec[T]` API (`push`/`pop`/`get`/`set`/`reserve`/`clear`).
- `crates/oac/src/std/std_clib.oa`: std-owned C interop declarations for `Clib.*` namespaced API via `namespace Clib { extern fun ... }` (resolver keys remain `Clib__*`; replaces compiler hardcoded libc signature JSON).
- `crates/oac/src/std/std_io.oa`: std-owned `Io.*` wrappers over `Clib.open/read/write/close` with explicit result enums.
- `crates/oac/execution_tests/*.oa`: language behavior fixtures (positive + negative).
- `crates/oac/bench/prove_baseline.json`: committed proving benchmark baseline used by `oac bench-prove`.
- `crates/oac/src/snapshots/*.snap`: canonical snapshots for tests.
- `.github/workflows/ci.yml`: CI checks (`cargo check`, `cargo test`).
- `.githooks/pre-commit`: local Git hook that formats staged Rust files with nightly `rustfmt`.
- `.githooks/pre-push`: local Git hook placeholder (no automatic test execution).
- `rustfmt.toml`: repository Rust formatting policy (nightly import-sorting behavior).

## Secondary/Reference Zones

- `stdlib/` and `examples/`: Ousia sample/library programs.
- `docs/`: language notes/spec drafts (some are historical/incomplete).
- `tools/vscode-ousia/`: editor integration package for local development and packaging (`.vsix`).
- `tools/vscode-ousia/`: VS Code extension workspace and packaging assets.

## Source of Truth Order (When Docs Disagree)

1. Compiler behavior in `crates/oac/src/*.rs`
2. Tests and snapshots in `crates/oac/execution_tests` and `crates/oac/src/snapshots`
3. CI in `.github/workflows/ci.yml`
4. Markdown docs under `docs/`

## Autonomous Sync Rule

When you discover stale context here, update this file and related `agents/*` files in the same PR/commit as the code change.
