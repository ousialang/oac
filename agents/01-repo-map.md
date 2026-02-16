# Repository Map

## Purpose

Ousia is an experimental language and compiler implemented in Rust.

The active compiler workspace is:
- `Cargo.toml` (workspace root)
- `crates/oac` (CLI + tokenizer/parser/type checker/IR/QBE backend/RISC-V SMT)
- `crates/qbe-rs` (QBE Rust bindings/wrapper)
- `crates/qbe-smt` (QBE-to-SMT CHC/fixedpoint encoding support for invariant proving)

## High-Value Paths

- `crates/oac/src/main.rs`: CLI entrypoint and build pipeline orchestration.
- `crates/oac/src/flat_imports.rs`: shared flat import resolver used by both user source and stdlib loading.
- `crates/oac/src/lsp.rs`: stdio LSP server loop (`oac lsp`) and diagnostics publishing.
- `crates/oac/src/tokenizer.rs`: eager tokenizer and syntax error model.
- `crates/oac/src/parser.rs`: AST definitions and parser.
- `crates/oac/src/ir.rs`: type resolution, semantic checks, and resolved IR.
- `crates/oac/src/qbe_backend.rs`: code generation to QBE IR and end-to-end execution tests.
- `crates/oac/src/builtins.rs`: built-in types and libc signatures.
- `crates/oac/src/riscv_smt.rs`: ELF -> SMT pipeline for bounded return-to-zero checks.
- `crates/oac/src/struct_invariants.rs`: SMT-backed compile-time struct invariant verification pass.
- `crates/qbe-smt/src/lib.rs`: public `qbe-smt` API and unit tests.
- `crates/qbe-smt/src/encode.rs`: CHC/Horn fixedpoint encoder for `exit == 1` reachability.
- `crates/qbe-smt/src/classify.rs`: conservative loop non-termination classifier used during `oac build`.
- `crates/oac/src/std.oa`: stdlib import entrypoint injected during resolution.
- `crates/oac/src/std_*.oa`: split stdlib modules imported by `std.oa`.
- `crates/oac/execution_tests/*.oa`: language behavior fixtures (positive + negative).
- `crates/oac/src/snapshots/*.snap`: canonical snapshots for tests.
- `.github/workflows/ci.yml`: CI checks (`cargo check`, `cargo test`).

## Secondary/Reference Zones

- `stdlib/` and `examples/`: Ousia sample/library programs.
- `docs/`: language notes/spec drafts (some are historical/incomplete).
- `tools/selfie/`: external project/reference material; treat as separate domain.

## Source of Truth Order (When Docs Disagree)

1. Compiler behavior in `crates/oac/src/*.rs`
2. Tests and snapshots in `crates/oac/execution_tests` and `crates/oac/src/snapshots`
3. CI in `.github/workflows/ci.yml`
4. Markdown docs under `docs/`

## Autonomous Sync Rule

When you discover stale context here, update this file and related `agents/*` files in the same PR/commit as the code change.
