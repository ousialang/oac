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

This repository contains the Ousia compiler workspace (`crates/*`) plus editor tooling under `tools/vscode-ousia/`. Prefer touching compiler code only unless explicitly requested.

## API Stability Policy (Pre-Release)

- Ousia is pre-release; source compatibility and stdlib API stability are not guaranteed yet.
- Prefer semantic clarity, correctness, and maintainability over preserving legacy interfaces.
- If a clean fix requires an API break (language surface, stdlib helpers, CLI behavior, or internal crate APIs), take the break instead of adding compatibility shims.
- When introducing a breaking change, update tests/snapshots and all affected `agents/*` documentation in the same change set.

## Testing Runner Preference

- For Rust test execution, use `cargo nextest run` when `cargo-nextest` is available in the environment (it is the preferred default because it is faster).
- Fall back to `cargo test` only when `cargo-nextest` is unavailable or when parity with CI behavior must be verified explicitly.

## Current Syntax Notes

- Generics use square brackets for type parameters and specialization arguments: `generic Option[T] { ... }`, `specialize OptionI32 = Option[I32]`.
- Traits are declaration-only method signature blocks: `trait Hash { fun hash(v: Self) -> I32 }`.
- Trait implementations are explicit and concrete-only in v1: `impl Hash for I32 { fun hash(v: I32) -> I32 { ... } }`.
- Generic bounds are inline on parameters: `generic HashTable[K: Hash + Eq, V] { ... }`.
- Legacy template syntax is hard-removed: `template` and `instantiate` are parser errors with migration hints to `generic` / `specialize`.
- Trait invocation in v1 is namespaced/static (`Trait.method(value, ...)`); calls are rewritten to concrete impl symbols during specialization and remain static dispatch only.
- Top-level imports are flat and same-directory only: `import "helpers.oa"`. Imported declarations are merged into one global scope.
- Namespaces are top-level and declaration-only: `namespace TypeName { fun helper(...) -> ... { ... } }` and `namespace TypeName { extern fun symbol(...) -> ... }`. Namespace calls use `TypeName.helper(...)` syntax and lower to internal lookup names using `TypeName__helper`.
- External declarations use `extern fun name(args...) -> Type` (no body). In v1 they may appear at top level and inside `namespace` blocks (no bodies, no `comptime`).
- In v2 ABI, `extern fun` signatures cannot use struct parameter or return types; C interop boundaries that move struct-like payloads must use manual `PtrInt` wrapper signatures.
- Struct field lists allow optional trailing commas in both type declarations and struct literals.
- Struct values use byte-value semantics at assignment/call/return boundaries: codegen inserts copy barriers (`calloc` + `memcpy`) so pointer identity is not language-visible at those boundaries.
- Struct equality is universal bytewise comparison: `==` / `!=` lower to `memcmp` over full struct size (including pointer-containing structs).
- The stdlib entrypoint `crates/oac/src/std/std.oa` is now an import aggregator over split files in `crates/oac/src/std/` (`std_ascii.oa`, `std_char.oa`, `std_null.oa`, `std_string.oa`, `std_collections.oa`, `std_traits.oa`, `std_json.oa`, `std_clib.oa`).
- `crates/oac/src/std/std_traits.oa` defines core traits (`Hash`, `Eq`) with concrete impls for practical key/value types used by stdlib and user generics.
- The split stdlib now exposes namespaced helper APIs where applicable: JSON parsing helpers are called via `Json.*` (for example `Json.json_kind`, `Json.parse_json_document_result`).
- The split stdlib collections now expose a richer persistent `LinkedList` template API: cached length via `len`/`length` (O(1) from node metadata), constructors/helpers (`empty`, `singleton`, `cons`, `push_front`), accessors (`front`, `tail`, `pop_front`, `at`, `at_or`), transforms (`append`, `reverse`, `take`, `drop`), and compatibility wrappers (`head_or`, `tail_or`, `length`).
- The stdlib also exposes `AsciiChar` and `AsciiCharResult` with namespaced helpers (`AsciiChar.from_code`, `AsciiChar.from_string_at`, `AsciiChar.code`, `AsciiChar.is_digit`, `AsciiChar.is_whitespace`, `AsciiChar.equals`); `AsciiChar` stores a wrapped `Char`.
- The stdlib also exposes `Char` as an `I32` wrapper (`struct Char { code: I32 }`) with namespaced helpers (`Char.from_code`, `Char.code`, `Char.equals`).
- The stdlib now also exposes `Null` as an empty struct (`struct Null {}`) with namespaced constructor helper `Null.value()`.
- The stdlib now also defines `Bytes` (`struct Bytes { ptr: PtrInt, len: I32 }`) and `String` as a tagged enum (`Literal(Bytes)` / `Heap(Bytes)`) in `crates/oac/src/std/std_string.oa`; `String` is no longer a compiler-primitive type.
- The stdlib `HashTable[T]` in `crates/oac/src/std/std_collections.oa` is now a dynamically resizing separate-chaining map (persistent value semantics) with APIs `new`, `with_capacity`, `set` (`SetResult { table, inserted_new }`), `get`, `remove` (`RemoveResult { table, removed }`), `len`, `capacity`, `contains_key`, and `clear`; fixed-size `put`/`size` APIs were removed.
- C interop in std is exposed through namespaced calls (`Clib.*`) and declared in `crates/oac/src/std/std_clib.oa` as `namespace Clib { extern fun ... }`; resolver keeps namespaced internal keys (`Clib__name`) while codegen emits declared extern symbol names for linking (for example `malloc` and `memcmp`).
- Built-in `Void` is available for C-style procedure signatures; in v1 only `extern fun` may return `Void`, and `Void` is rejected as a parameter type.
- Built-in `U8` is available as an unsigned byte-like numeric type (`U8/U8` arithmetic and comparisons are allowed with no implicit coercions).
- The resolver also exposes `PtrInt` as a standard numeric alias hardcoded to `I64` (for pointer-sized integer use sites).
- Runtime byte memory helpers are compiler builtins: `load_u8(addr: PtrInt) -> U8` and `store_u8(addr: PtrInt, value: U8) -> Void`.
- Character literals use single quotes and lower to `Char` construction (`'x'`, escapes like `'\n'` and `'\''`); parser lowers literals to `Char.from_code(...)`.
- Identifier tokenization is EOF-safe: trailing words (including `_`) now lex as `Word` tokens instead of panicking, which keeps `oac lsp` stable on incomplete buffers.
- `AsciiChar` range is enforced by a declaration-based struct invariant over its wrapped `Char` (`0 <= Char.code(ch) <= 127`); stdlib invariant declarations are now merged during `resolve` alongside stdlib types/functions/generics.
- Built-in `FP32` and `FP64` are supported end-to-end. Unsuffixed decimal literals default to `FP32` (for example `1.25`), while `f64` suffix selects `FP64` (for example `1.25f64`). Numeric arithmetic/comparisons do not perform implicit widening/coercion between integer and floating types (`U8`, `I32`, `I64`, `FP32`, `FP64` stay same-type only).
- Generic-specialized helper functions can be called with namespaced syntax (`Alias.helper(...)`), which lowers to generated mangled symbols like `Alias__helper`.
- The CLI now includes an `lsp` subcommand (`oac lsp`) that runs a stdio JSON-RPC language server with diagnostics.
- The LSP currently handles text sync plus `textDocument/definition`, `textDocument/hover`, `textDocument/documentSymbol`, `textDocument/references`, and `textDocument/completion`.
- A VS Code extension scaffold now lives in `tools/vscode-ousia/`; it launches `oac lsp` and is configured via `ousia.server.path`, `ousia.server.args`, and `ousia.trace.server`.
- The VS Code extension must launch `oac lsp` without appending `--stdio`; `ousia.server.args` are sanitized to ignore `--stdio`.
- Top-level tests use declaration syntax: `test "Name" { ... }`.
- The CLI now includes `oac test <file.oa>`: it lowers `test` declarations into generated helper functions plus a generated `main`, compiles under `target/oac/test/`, and executes tests fail-fast (assert failures exit with `242`).
- `prove(cond)` and `assert(cond)` are statement-only builtins with call syntax. `prove` is compile-time (fail-closed); `assert` is runtime and exits with code `242` on failure.
- Function names `prove` and `assert` are reserved and cannot be user-defined.
- Struct type invariants are optional and declared with `invariant "Human label" for (v: TypeName) { ... }` or `invariant identifier "Human label" for (...) { ... }`; the compiler synthesizes internal functions named `__struct__<TypeName>__invariant` and still accepts legacy explicit function declarations with that name/signature.
- During `oac build`, prove obligations are verified first at reachable `prove(...)` sites by synthesizing per-site QBE checker functions that return `1` on violated proof conditions and `0` on success (`unsat` passes, `sat` fails). Debug artifacts are emitted under `target/oac/prove/`.
- During `oac build`, struct invariants are verified at user-function call return sites (reachable from `main`) by synthesizing per-site QBE checker functions from compiled QBE: the target call site is instrumented with an invariant check and checker exit is `1` on violation / `0` on success (`unsat` passes, `sat` fails).
- Checker synthesis is now QBE-native: reachable user calls are inlined into the checker before CHC encoding so loop/control-flow reasoning happens on QBE transitions (fixedpoint/Spacer), not via source-level symbolic formula summarization.
- Recursion cycles on the reachable user-call graph are rejected fail-closed for struct invariant verification.
- Build/test environments that hit invariant obligations require `z3`; debug SMT artifacts are emitted under `target/oac/struct_invariants/`.
- `main` signatures are intentionally restricted to `fun main() -> I32`, `fun main(argc: I32, argv: I64) -> I32`, or `fun main(argc: I32, argv: PtrInt) -> I32`.
- Solver encodings treat `argc` as non-negative by default (`argc >= 0`) when enabled by the caller.
- `qbe-smt` is CHC-only (fixedpoint/Spacer): it emits Horn rules over QBE transitions and always queries whether halting with `exit == 1` is reachable.
- `qbe-smt` is strict fail-closed: unsupported instructions/operations are hard encoding errors (no conservative havoc fallback).
- `qbe-smt` is parser-free and consumes in-memory `qbe::Function` directly.
- `qbe-smt` remains fail-closed for floating-point obligations (including FP32/FP64 literals/comparisons); prove/struct-invariant obligations that require float reasoning are currently unsupported.
- Snapshot coverage now includes float-literal tokenizer fixtures and a parser AST snapshot regression (`parser_float_literals_ast`) to lock float literal parsing behavior.
- `qbe-smt` CHC state now tracks predecessor-block identity (`pred`) so `phi` assignments are modeled directly in Horn transitions (with predecessor guards), instead of being rejected.
- `qbe-smt` source split: `lib.rs` (public API + tests), `encode.rs` (CHC/Horn encoding), `classify.rs` (loop classification).
- CHC solving is centralized in `qbe-smt` (`solve_chc_script` / `solve_chc_script_with_diagnostics`); struct invariant verification uses this shared backend runner instead of owning a separate Z3 invocation path.
- `qbe-smt` now models a wider CLib call set in CHC encoding: `malloc`, `free`, `calloc`, `realloc`, `memcpy`, `memmove`, `memcmp`, `memset`, `strlen`, `strcmp`, `strcpy`, `strncpy`, `open`, `read`, `write`, `close`, plus `exit(code)` halting transitions (and variadic `printf` for compiler builtin `print` inlining).
- CLib byte-effect models are bounded with deterministic inline precision (`limit = 16`) and sound fallback branches; unknown extern call targets remain strict fail-closed errors.
- CHC encoding only includes reachable QBE blocks from entry; unsupported instructions in unreachable blocks are ignored by design.
- SAT struct-invariant failures now include a control-flow witness summary (checker CFG path + branch choices); for `main(argc, argv)` obligations they also include a concrete solver-derived `argc` witness when extraction succeeds.
- `oac build` no longer emits `target/oac/ir.smt2` sidecar output; SMT artifacts are only produced for struct invariant obligations under `target/oac/struct_invariants/`.
- Build/test environments that hit prove obligations also require `z3`; debug SMT artifacts are emitted under `target/oac/prove/`.
- `oac build` now runs a best-effort non-termination classifier on the generated QBE `main` function; when it proves a canonical while-loop is non-terminating, compilation fails early with the loop header label and proof reason.
- Build/test linking now uses C compiler drivers (`cc`/`clang`/target-prefixed `*-gcc`) instead of Zig. Link step is fail-closed and supports `OAC_CC` (single explicit command), `CC` (preferred first attempt), `OAC_CC_TARGET`, and `OAC_CC_FLAGS`.
- Execution fixture snapshots in `qbe_backend` are based on program stdout even when the process exits with a non-zero code; runtime errors are reserved for spawn failures, timeouts, invalid UTF-8, or signal termination.
- GitHub Actions CI now provisions backend test/build dependencies before Rust checks (`z3`, Zig via `goto-bus-stop/setup-zig@v2` pinned to `0.13.0`, and `qbe` built from upstream `qbe-1.2` source tarball in `.github/workflows/ci.yml`).

## Hard-Cut Migration Cheatsheet

- Old: `template Option[T] { ... }` -> New: `generic Option[T] { ... }`
- Old: `instantiate OptionI32 = Option[I32]` -> New: `specialize OptionI32 = Option[I32]`
- Old key ops in generic hash tables: direct integer hash/`==` -> New: trait-bounded calls (`Hash.hash(k)`, `Eq.equals(a, b)`) with bounds like `[K: Hash + Eq, V]`
