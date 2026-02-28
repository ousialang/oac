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
- Tracked Git hooks live under `.githooks/`; enable them locally with `git config core.hooksPath .githooks`.
- The local `pre-commit` hook formats staged Rust files with nightly `rustfmt` (using `rustfmt.toml` with nightly import-sorting options), and the local `pre-push` hook is intentionally a no-op (no automatic test execution).

## Current Syntax Notes

- Generics use square brackets for type parameters and specialization arguments: `generic Option[T] { ... }`, `specialize OptionI32 = Option[I32]`.
- Traits are declaration-only method signature blocks: `trait Hash { fun hash(v: Self) -> I32 }`.
- Trait implementations are explicit and concrete-only in v1: `impl Hash for I32 { fun hash(v: I32) -> I32 { ... } }`.
- Generic bounds are inline on parameters: `generic HashTable[K: Hash + Eq, V] { ... }`.
- Legacy template syntax is hard-removed: `template` and `instantiate` are parser errors with migration hints to `generic` / `specialize`.
- Trait invocation in v1 is namespaced/static (`Trait.method(value, ...)`); calls are rewritten to concrete impl symbols during specialization and remain static dispatch only.
- Top-level imports are flat and same-directory only: `import "helpers.oa"`. Imported declarations are merged into one global scope.
- Same-directory import validation now lives in `crates/oac/src/flat_imports.rs` as shared helper `validate_same_dir_oa_import(...)` and is reused by both compiler import resolution and LSP project symbol/import traversal.
- Namespaces are top-level and declaration-only: `namespace TypeName { fun helper(...) -> ... { ... } }` and `namespace TypeName { extern fun symbol(...) -> ... }`. Namespace calls use `TypeName.helper(...)` syntax and lower to internal lookup names using `TypeName__helper`.
- External declarations use `extern fun name(args...) -> Type` (no body). In v1 they may appear at top level and inside `namespace` blocks (no bodies, no `comptime`).
- In v2 ABI, `extern fun` signatures cannot use struct parameter or return types; C interop boundaries that move struct-like payloads must use manual `PtrInt` wrapper signatures.
- Struct field lists allow optional trailing commas in both type declarations and struct literals.
- Struct values use byte-value semantics at assignment/call/return boundaries: codegen inserts copy barriers (`calloc` + `memcpy`) so pointer identity is not language-visible at those boundaries.
- Struct equality is universal bytewise comparison: `==` / `!=` lower to `memcmp` over full struct size (including pointer-containing structs).
- The stdlib entrypoint `crates/oac/src/std/std.oa` is now an import aggregator over split files in `crates/oac/src/std/` (`std_ascii.oa`, `std_char.oa`, `std_null.oa`, `std_option_result.oa`, `std_string.oa`, `std_ref.oa`, `std_collections.oa`, `std_traits.oa`, `std_json.oa`, `std_clib.oa`).
- `crates/oac/src/std/std_traits.oa` defines core traits (`Hash`, `Eq`) with concrete impls for practical key/value types used by stdlib and user generics.
- The split stdlib now exposes namespaced helper APIs where applicable: JSON parsing helpers are called via `Json.*` (for example `Json.json_kind`, `Json.parse_json_document_result`).
- The split stdlib collections now expose a richer persistent `LinkedList` template API: cached length via `len`/`length` (O(1) from node metadata), constructors/helpers (`empty`, `singleton`, `cons`, `push_front`), accessors (`front`, `tail`, `pop_front`, `at`, `at_or`), transforms (`append`, `reverse`, `take`, `drop`), and compatibility wrappers (`head_or`, `tail_or`, `length`).
- `LinkedList[T]::Node` now carries a declaration-based struct invariant (`len >= 1`), and `LinkedList.make_node` normalizes/saturates cached `len` metadata before constructing nodes to keep that invariant provable fail-closed.
- The stdlib also exposes `AsciiChar` and `AsciiCharResult` with namespaced helpers (`AsciiChar.from_code`, `AsciiChar.from_string_at`, `AsciiChar.code`, `AsciiChar.is_digit`, `AsciiChar.is_whitespace`, `AsciiChar.equals`); `AsciiChar` stores a wrapped `Char`.
- The stdlib also exposes `Char` as an `I32` wrapper (`struct Char { code: I32 }`) with namespaced helpers (`Char.from_code`, `Char.code`, `Char.equals`).
- The stdlib now also exposes `Null` as an empty struct (`struct Null {}`) with namespaced constructor helper `Null.value()`.
- The stdlib now also defines `Bytes` (`struct Bytes { ptr: PtrInt, len: I32 }`) and `String` as a tagged enum (`Literal(Bytes)` / `Heap(Bytes)`) in `crates/oac/src/std/std_string.oa`; `String` is no longer a compiler-primitive type.
- The stdlib `String` namespace now also exposes convenience helpers in `crates/oac/src/std/std_string.oa`: `is_empty`, `equals`, `starts_with`, `ends_with`, `char_at_or`, and `slice_clamped`.
- The stdlib now also defines generic `Option[T]` / `Result[T, E]` in `crates/oac/src/std/std_option_result.oa` with namespaced constructors/helpers (`none`/`some`/`is_some`/`is_none`/`unwrap_or` and `ok`/`err`/`is_ok`/`is_err`/`unwrap_or`/`unwrap_err_or`).
- The stdlib now also defines generic `Ref[T]` and `Mut[T]` in `crates/oac/src/std/std_ref.oa` with pointer helpers (`from_ptr`, `ptr`, `is_null`, `add_bytes`); concrete specializations expose read-only dereference helpers (`U8Ref.read`, `I32Ref.read`, `I64Ref.read`, `PtrIntRef.read`, `BoolRef.read`) and mutable wrappers with read/write helpers (`U8Mut.*`, `I32Mut.*`, `I64Mut.*`, `PtrIntMut.*`, `BoolMut.*`).
- The stdlib `HashTable[K: Hash + Eq, V]` in `crates/oac/src/std/std_collections.oa` is now a dynamically resizing separate-chaining map (persistent value semantics) with APIs `new`, `with_capacity`, `set` (`SetResult { table, inserted_new }`), `get`, `remove` (`RemoveResult { table, removed }`), `len`, `capacity`, `contains_key`, and `clear`; fixed-size `put`/`size` APIs were removed.
- C interop in std is exposed through namespaced calls (`Clib.*`) and declared in `crates/oac/src/std/std_clib.oa` as `namespace Clib { extern fun ... }`; resolver keeps namespaced internal keys (`Clib__name`) while codegen emits declared extern symbol names for linking (for example `malloc`).
- Built-in `Void` is available for C-style procedure signatures; in v1 only `extern fun` may return `Void`, and `Void` is rejected as a parameter type.
- Built-in `U8` is available as an unsigned byte-like numeric type (`U8/U8` arithmetic and comparisons are allowed with no implicit coercions).
- The resolver also exposes `PtrInt` as a standard numeric alias hardcoded to `I64` (for pointer-sized integer use sites).
- Runtime pointer memory helpers are compiler builtins: `load_u8(addr: PtrInt) -> U8`, `load_i32(addr: PtrInt) -> I32`, `load_i64(addr: PtrInt) -> I64`, `load_bool(addr: PtrInt) -> Bool`, `store_u8(addr: PtrInt, value: U8) -> Void`, `store_i32(addr: PtrInt, value: I32) -> Void`, `store_i64(addr: PtrInt, value: I64) -> Void`, and `store_bool(addr: PtrInt, value: Bool) -> Void`.
- Character literals use single quotes and lower to `Char` construction (`'x'`, escapes like `'\n'` and `'\''`); parser lowers literals to `Char.from_code(...)`.
- Identifier tokenization is EOF-safe: trailing words (including `_`) now lex as `Word` tokens instead of panicking, which keeps `oac lsp` stable on incomplete buffers.
- `AsciiChar` range is enforced by a declaration-based struct invariant over its wrapped `Char` (`0 <= Char.code(ch) <= 127`); stdlib invariant declarations are now merged during `resolve` alongside stdlib types/functions/generics.
- `Bytes` length is enforced by a declaration-based struct invariant (`len >= 0`) in `crates/oac/src/std/std_string.oa`.
- `String.make_bytes` in `crates/oac/src/std/std_string.oa` normalizes `Bytes.len` fail-closed (`len < 0` clamps to `0`) and is used by `String.bytes`, `String.from_literal_parts`, and `String.from_heap_parts` so `Bytes` invariants remain provable at call sites.
- Built-in `FP32` and `FP64` are supported end-to-end. Unsuffixed decimal literals default to `FP32` (for example `1.25`), while `f64` suffix selects `FP64` (for example `1.25f64`). Numeric arithmetic/comparisons do not perform implicit widening/coercion between integer and floating types (`U8`, `I32`, `I64`, `FP32`, `FP64` stay same-type only).
- Generic-specialized helper functions can be called with namespaced syntax (`Alias.helper(...)`), which lowers to generated mangled symbols like `Alias__helper`.
- The CLI now includes an `lsp` subcommand (`oac lsp`) that runs a stdio JSON-RPC language server with diagnostics.
- The LSP currently handles text sync plus `textDocument/definition`, `textDocument/hover`, `textDocument/documentSymbol`, `textDocument/references`, and `textDocument/completion`.
- Compiler diagnostics are centralized in `crates/oac/src/diagnostics.rs` and rendered with Ariadne for both CLI output and `oac lsp` diagnostic conversion.
- `oac build` / `oac test` stage failures are now mapped to stable diagnostic codes (for example `OAC-PARSE-001`, `OAC-RESOLVE-001`, `OAC-LINK-001`, `OAC-LINK-002`) and emitted as Ariadne reports; execution fixture compilation-error snapshots therefore reflect Ariadne plain-report text.
- A VS Code extension scaffold now lives in `tools/vscode-ousia/`; it launches `oac lsp` and is configured via `ousia.server.path`, `ousia.server.args`, and `ousia.trace.server`.
- The VS Code extension must launch `oac lsp` without appending `--stdio`; `ousia.server.args` are sanitized to ignore `--stdio`.
- Top-level tests use declaration syntax: `test "Name" { ... }`.
- The CLI now includes `oac test <file.oa>`: it lowers `test` declarations into generated helper functions plus a generated `main`, compiles under `target/oac/test/`, and executes tests fail-fast (assert failures exit with `242`).
- The CLI now also includes `oac bench-prove`: end-to-end proving benchmark runner over curated execution fixtures with suites `full` (default) and `quick`, configurable iterations, optional baseline/report path overrides, and deterministic `--update-baseline` rewriting.
- Proving benchmark baseline is committed at `crates/oac/bench/prove_baseline.json`; default report output is `target/oac/bench/prove/latest.json`, and isolated per-fixture benchmark run artifacts are emitted under `target/oac/bench/runs/<fixture>/iter_<n>/`.
- `oac bench-prove` uses report-only timing regression policy in v1 (regression when both `delta_ms >= 200` and `delta_pct >= 20.0`), but still fails fail-closed on unexpected fixture outcomes (unexpected success/failure or diagnostic code mismatch).
- `prove(cond)` and `assert(cond)` are statement-only builtins with call syntax. `prove` is compile-time (fail-closed); `assert` is runtime and exits with code `242` on failure.
- Function names `prove` and `assert` are reserved and cannot be user-defined.
- Struct type invariants are optional and support both single and grouped forms with one keyword: `invariant [identifier]? "Human label" for (v: TypeName) { ... }` and `invariant for (v: TypeName) { [identifier]? "Human label" { ... } ... }` (display string required, identifier optional in both forms).
- Each invariant declaration clause is tracked independently per struct type; the compiler synthesizes internal functions named `__struct__<TypeName>__invariant__<key>` (`<key>` is identifier-based or deterministic anonymous ordinal such as `anon_0`) and still accepts legacy explicit functions named `__struct__<TypeName>__invariant(v: TypeName) -> Bool`.
- During `oac build`, proof obligations are orchestrated by `crates/oac/src/verification.rs`: it runs prove verification first and only runs struct-invariant verification if prove obligations pass.
- During `oac build`, prove obligations are verified first at reachable `prove(...)` sites by synthesizing per-site QBE checker functions that return `1` on violated proof conditions and `0` on success (`unsat` passes, `sat` fails). Debug artifacts are emitted under `target/oac/prove/`.
- During `oac build`, struct invariants are verified per `(call-site, invariant)` pair at user-function call return sites (reachable from `main`) by synthesizing per-site QBE checker functions from compiled QBE: the target call site is instrumented with one invariant check and checker exit is `1` on violation / `0` on success (`unsat` passes, `sat` fails).
- Struct-invariant obligation identifiers now include the invariant key suffix in diagnostics/debug artifacts (`<caller>#<site>#<ordinal>#<invariant_key>`), and generated checker artifacts follow the same suffixing pattern (`site_<caller>_<site>_<ordinal>_<invariant_key>.qbe` / `.smt2`).
- Checker synthesis is QBE-native and interprocedural: each site emits a checker entry function plus reachable user callees, and CHC encoding models user calls via per-function summary relations (`*_ret` / `*_abort`) instead of checker-time call inlining.
- Prove and struct-invariant pipelines now share checker assembly utilities in `crates/oac/src/verification_checker.rs` (site-id sanitization, solver excerpt summarization, checker return normalization, reachable-callee module closure, and main-argc assumption gate).
- Parser-AST recursion helpers are centralized in `crates/oac/src/ast_walk.rs` and reused by resolve, verification-cycle analysis, and struct-invariant site indexing/call collection to keep traversal semantics aligned.
- Trait symbol key helpers are centralized in `crates/oac/src/symbol_keys.rs` and reused by resolve and QBE codegen (`Trait::method`, impl-target keys, impl-method keys, mangled impl function names).
- Checker encoding now adds function-entry preconditions for invariant-bearing arguments in both verification pipelines: for each checker function argument whose semantic type has struct invariants, `qbe-smt` assumes each corresponding invariant relation holds and returns non-zero at entry (assumption-only; entry memory/heap state is not replaced with invariant-call outputs).
- The legacy struct-invariant checker call-inliner has been removed; struct-invariant obligations now only use module-level CHC encoding (`qbe_module_to_smt_with_assumptions`, wrapped by `qbe_module_to_smt`) for checker entry plus reachable callees.
- Shared recursion-cycle analysis is implemented in `crates/oac/src/verification_cycles.rs` using SCCs over the combined verification graph with deterministic witness diagnostics.
- Call-only recursion cycles are allowed during struct invariant and prove verification; cycles that include argument-invariant precondition edges are rejected fail-closed on the combined verification graph.
- Build/test environments that hit invariant obligations require `z3`; debug SMT artifacts are emitted under `target/oac/struct_invariants/`.
- `main` signatures are intentionally restricted to `fun main() -> I32`, `fun main(argc: I32, argv: I64) -> I32`, or `fun main(argc: I32, argv: PtrInt) -> I32`.
- Solver encodings treat `argc` as non-negative by default (`argc >= 0`) when enabled by the caller.
- `qbe-smt` is CHC-only (fixedpoint/Spacer): it emits Horn rules over QBE transitions and always queries whether halting with `exit == 1` is reachable.
- `qbe-smt` is strict fail-closed: unsupported instructions/operations are hard encoding errors (no conservative havoc fallback).
- `qbe-smt` is parser-free and consumes in-memory QBE IR directly as modules (`qbe::Module` via `qbe_module_to_smt` / `qbe_module_to_smt_with_assumptions`).
- `qbe-smt` remains fail-closed for floating-point obligations (including FP32/FP64 literals/comparisons); prove/struct-invariant obligations that require float reasoning are currently unsupported.
- Snapshot coverage now includes float-literal tokenizer fixtures and a parser AST snapshot regression (`parser_float_literals_ast`) to lock float literal parsing behavior.
- `qbe-smt` CHC state now tracks predecessor-block identity (`pred`) so `phi` assignments are modeled directly in Horn transitions (with predecessor guards), instead of being rejected.
- `qbe-smt` source split: `lib.rs` (public API + tests), `encode.rs` (core CHC/Horn encoding), `encode_extern_models.rs` (extern call model catalog/arity), `classify.rs` (loop classification).
- CHC solving is centralized in `qbe-smt` (`solve_chc_script` / `solve_chc_script_with_diagnostics`); struct invariant verification uses this shared backend runner instead of owning a separate Z3 invocation path.
- `qbe-smt` solver stdin writes now treat `BrokenPipe` as an early solver termination signal and still read solver stdout/stderr for result classification (`sat`/`unsat`/`unknown`), instead of surfacing transport-layer pipe errors directly.
- `qbe-smt` now exposes Ariadne report helpers on `QbeSmtError` (`render_report_plain`, `render_report_terminal_auto`) and `oac` includes those reports in prove/invariant failure notes.
- `qbe-smt` now models a wider CLib call set in CHC encoding: `malloc`, `free`, `calloc`, `realloc`, `memcpy`, `memmove`, `memcmp`, `memset`, `strlen`, `strcmp`, `strcpy`, `strncpy`, `open`, `read`, `write`, `close`, plus `exit(code)` halting transitions (and variadic `printf` for compiler builtin `print` inlining).
- CLib byte-effect models are bounded with deterministic inline precision (`limit = 16`) and sound fallback branches; unknown extern call targets remain strict fail-closed errors.
- `qbe-smt` now models bounded `strlen` NUL-scan and bounded `strcmp` first-event scan (`difference` or shared NUL) with tri-state outcomes (`-1/0/1`) and fail-open fallback to constrained unknowns when precision bounds are exceeded.
- `qbe-smt` now models `strcpy` as bounded byte copy until first NUL (including terminator) with fallback to unconstrained memory when no terminator is found within the inline bound.
- `qbe-smt` now constrains modeled syscall-like return values: `open` returns `-1` or non-negative, `close` returns `0` or `-1`, and `read`/`write` return `-1` or a non-negative value bounded above by `count`.
- CHC encoding only includes reachable QBE blocks from entry; unsupported instructions in unreachable blocks are ignored by design.
- SAT struct-invariant failures now include a control-flow witness summary (checker CFG path + branch choices).
- `oac build` no longer emits `target/oac/ir.smt2` sidecar output; SMT artifacts are only produced for struct invariant obligations under `target/oac/struct_invariants/`.
- Build/test environments that hit prove obligations also require `z3`; debug SMT artifacts are emitted under `target/oac/prove/`.
- `oac build` now runs a best-effort non-termination classifier on the generated QBE `main` function; when it proves a canonical while-loop is non-terminating, compilation fails early with the loop header label and proof reason.
- Build/test linking now uses C compiler drivers (`cc`/`clang`/target-prefixed `*-gcc`) instead of Zig. Link step is fail-closed and supports `OAC_CC` (single explicit command), `CC` (preferred first attempt), `OAC_CC_TARGET`, and `OAC_CC_FLAGS`.
- Linker-stage diagnostics now use `DiagnosticStage::Linker` and stable codes `OAC-LINK-001` / `OAC-LINK-002` (legacy `OAC-ZIG-*` names are removed).
- Execution fixture snapshots in `qbe_backend` are based on program stdout even when the process exits with a non-zero code; runtime errors are reserved for spawn failures, timeouts, invalid UTF-8, or signal termination.
- `crates/oac/src/qbe_backend.rs` execution fixtures now compile/execute in parallel worker threads inside one test harness, but snapshot assertions stay deterministic by sorting fixture paths/results before asserting; worker count defaults to `min(available_parallelism, 8)` and can be overridden with `OAC_EXECUTION_TEST_JOBS=<n>`.
- Snapshot hygiene is test-gated: committed `*.snap.new` files, execution snapshots without matching `execution_tests/*.oa` fixtures, and duplicated Ariadne prefixes (`Error: error[...]`) are treated as test failures.
- GitHub Actions CI now runs Rust checks in parallel jobs in `.github/workflows/ci.yml`: `cargo check --all-targets --all-features` (`check`) and `cargo nextest run --all-targets --all-features` (`nextest`).
- The `nextest` CI job provisions backend test/build dependencies (`z3`, Zig via `goto-bus-stop/setup-zig@v2` pinned to `0.13.0`, and `qbe` built from upstream `qbe-1.2` source tarball) and installs `cargo-nextest` via `taiki-e/install-action@nextest`.

## Hard-Cut Migration Cheatsheet

- Old: `template Option[T] { ... }` -> New: `generic Option[T] { ... }`
- Old: `instantiate OptionI32 = Option[I32]` -> New: `specialize OptionI32 = Option[I32]`
- Old key ops in generic hash tables: direct integer hash/`==` -> New: trait-bounded calls (`Hash.hash(k)`, `Eq.equals(a, b)`) with bounds like `[K: Hash + Eq, V]`
