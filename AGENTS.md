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
- The stdlib entrypoint `crates/oac/src/std.oa` is now an import aggregator over split files (`std_newstring.oa`, `std_collections.oa`, `std_json.oa`).
- The CLI now includes an `lsp` subcommand (`oac lsp`) that runs a stdio JSON-RPC language server with diagnostics.
- The LSP currently handles text sync plus `textDocument/definition`, `textDocument/hover`, `textDocument/documentSymbol`, `textDocument/references`, and `textDocument/completion`.
- Struct type invariants are optional and discovered by function name pattern `__struct__<TypeName>__invariant` with required signature `fun __struct__<TypeName>__invariant(v: <TypeName>) -> Bool`.
- During `oac build`, struct invariants are verified at user-function call return sites (reachable from `main`) by generating per-site checker QBE programs that return `1` on violation and `0` on success; proving asks whether exit code `1` is reachable (`unsat` passes, `sat` fails).
- The verifier now supports `while` statements via conservative loop summarization: variables assigned in the loop body are havocked after the loop, while loops containing invariant-obligation call sites or loop-body `return` statements still fail closed.
- Checker QBE lowering keeps `I32` symbolic inputs in `w` arguments and sign-extends to `l` internally, so proofs quantify over the `I32` domain instead of unconstrained 64-bit values.
- Build/test environments that hit invariant obligations require `z3`; debug SMT artifacts are emitted under `target/oac/struct_invariants/`.
- `main` signatures are intentionally restricted to `fun main() -> I32` or `fun main(argc: I32, argv: I64) -> I32`.
- Solver encodings treat `argc` as non-negative by default (`argc >= 0`) when enabled by the caller.
- `qbe-smt` is CHC-only (fixedpoint/Spacer): it emits Horn rules over QBE transitions and always queries whether halting with `exit == 1` is reachable.
- `qbe-smt` is strict fail-closed: unsupported instructions/operations are hard encoding errors (no conservative havoc fallback).
- `oac build` no longer emits `target/oac/ir.smt2` sidecar output; SMT artifacts are only produced for struct invariant obligations under `target/oac/struct_invariants/`.
