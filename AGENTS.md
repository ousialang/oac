# AGENTS: Ousia Contributor Intelligence

This file is the entrypoint for LLM contributors. It is a table of contents for high-value project context in `agents/`.

## Non-Optional Maintenance Rule

If code, commands, architecture, semantics, tests, or workflows change, you must update this file and affected files under `agents/` in the same change set.

Do this autonomously. Do not defer it to “later docs cleanup”.

## How To Use This Pack

1. Read `agents/01-repo-map.md` for structure and boundaries.
2. Read `agents/02-compiler-pipeline.md` before touching parser/IR/codegen.
3. Read `agents/03-language-semantics.md` before changing language behavior.
4. Read `agents/04-testing-ci.md` before refactors, bugfixes, or snapshots.
5. Read `agents/05-engineering-playbook.md` before implementing non-trivial changes.

## Index

- `agents/01-repo-map.md`: repository map, ownership zones, and source-of-truth files.
- `agents/02-compiler-pipeline.md`: front-end to backend flow (`tokenizer` -> `parser` -> `ir` -> `qbe` -> asm -> binary).
- `agents/03-language-semantics.md`: language model and invariants implemented today.
- `agents/04-testing-ci.md`: how to run tests, snapshot behavior, CI expectations, and debugging flow.
- `agents/05-engineering-playbook.md`: practical implementation rules for safe compiler evolution.

## Scope Note

This repository currently contains both the Ousia compiler workspace (`crates/*`) and vendored/reference material under `tools/selfie/`. Prefer touching compiler code only unless explicitly requested.

## Current Syntax Notes

- Templates use square brackets for type parameters and instantiation arguments: `template Option[T] { ... }`, `instantiate OptionI32 = Option[I32]`.
- Top-level imports are flat and same-directory only: `import "helpers.oa"`. Imported declarations are merged into one global scope.
- Struct field lists allow optional trailing commas in both type declarations and struct literals.
- The stdlib entrypoint `crates/oac/src/std.oa` is now an import aggregator over split files (`std_newstring.oa`, `std_collections.oa`, `std_json.oa`).
- The CLI now includes an `lsp` subcommand (`oac lsp`) that runs a stdio JSON-RPC language server with diagnostics.
- The LSP currently handles text sync plus `textDocument/definition`, `textDocument/hover`, `textDocument/documentSymbol`, `textDocument/references`, and `textDocument/completion`.
- Struct type invariants are optional and declared with `invariant "Human label" for (v: TypeName) { ... }` or `invariant identifier "Human label" for (...) { ... }`; the compiler synthesizes internal functions named `__struct__<TypeName>__invariant` and still accepts legacy explicit function declarations with that name/signature.
- During `oac build`, struct invariants are verified at user-function call return sites (reachable from `main`) by synthesizing per-site QBE checker functions from compiled QBE: the target call site is instrumented with an invariant check and checker exit is `1` on violation / `0` on success (`unsat` passes, `sat` fails).
- Checker synthesis is now QBE-native: reachable user calls are inlined into the checker before CHC encoding so loop/control-flow reasoning happens on QBE transitions (fixedpoint/Spacer), not via source-level symbolic formula summarization.
- Recursion cycles on the reachable user-call graph are rejected fail-closed for struct invariant verification.
- Build/test environments that hit invariant obligations require `z3`; debug SMT artifacts are emitted under `target/oac/struct_invariants/`.
- `main` signatures are intentionally restricted to `fun main() -> I32` or `fun main(argc: I32, argv: I64) -> I32`.
- Solver encodings treat `argc` as non-negative by default (`argc >= 0`) when enabled by the caller.
- `qbe-smt` is CHC-only (fixedpoint/Spacer): it emits Horn rules over QBE transitions and always queries whether halting with `exit == 1` is reachable.
- `qbe-smt` is strict fail-closed: unsupported instructions/operations are hard encoding errors (no conservative havoc fallback).
- `qbe-smt` is parser-free and consumes in-memory `qbe::Function` directly.
- `qbe-smt` CHC state now tracks predecessor-block identity (`pred`) so `phi` assignments are modeled directly in Horn transitions (with predecessor guards), instead of being rejected.
- `qbe-smt` source split: `lib.rs` (public API + tests), `encode.rs` (CHC/Horn encoding), `classify.rs` (loop classification).
- CHC solving is centralized in `qbe-smt` (`solve_chc_script` / `solve_chc_script_with_diagnostics`); struct invariant verification uses this shared backend runner instead of owning a separate Z3 invocation path.
- CHC encoding only includes reachable QBE blocks from entry; unsupported instructions in unreachable blocks are ignored by design.
- SAT struct-invariant failures now include a control-flow witness summary (checker CFG path + branch choices); for `main(argc, argv)` obligations they also include a concrete solver-derived `argc` witness when extraction succeeds.
- `oac build` no longer emits `target/oac/ir.smt2` sidecar output; SMT artifacts are only produced for struct invariant obligations under `target/oac/struct_invariants/`.
- `oac build` now runs a best-effort non-termination classifier on the generated QBE `main` function; when it proves a canonical while-loop is non-terminating, compilation fails early with the loop header label and proof reason.
- Execution fixture snapshots in `qbe_backend` are based on program stdout even when the process exits with a non-zero code; runtime errors are reserved for spawn failures, timeouts, invalid UTF-8, or signal termination.
