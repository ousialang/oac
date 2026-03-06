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
- `agents/02-compiler-pipeline.md`: front-end to backend flow (`tokenizer` -> `parser` -> `ir` -> QBE verification -> runtime backend -> binary).
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
- Repo root `install-vscode-extension.sh` is the canonical helper for packaging `tools/vscode-ousia` into a `.vsix` and installing it through the VS Code CLI (`CODE_BIN` can override the `code` executable).

## Current Syntax Notes

- Generics use square brackets for type parameters and specialization arguments: `generic Option[T] { ... }`, `specialize OptionI32 = Option[I32]`.
- Generic bodies also support local specialization aliases (`specialize LocalAlias = Name[TypeArgs...]`) so generic helpers can reuse other generics after specialization.
- Traits are declaration-only method signature blocks: `trait Hash { fun hash(v: Self) -> I32 }`.
- Trait implementations are explicit and concrete-only in v1: `impl Hash for I32 { fun hash(v: I32) -> I32 { ... } }`.
- Generic bounds are inline on parameters: `generic HashTable[K: Hash + Eq, V] { ... }`.
- Legacy template syntax is hard-removed: `template` and `instantiate` are parser errors with migration hints to `generic` / `specialize`.
- Trait invocation in v1 is namespaced/static (`Trait.method(value, ...)`); calls are rewritten to concrete impl symbols during specialization and remain static dispatch only.
- Top-level imports are flat and same-directory only: `import "helpers.oa"`. Imported declarations are merged into one global scope.
- Same-directory import validation now lives in `crates/oac/src/flat_imports.rs` as shared helper `validate_same_dir_oa_import(...)` and is reused by both compiler import resolution and LSP project symbol/import traversal.
- Namespaces are top-level and declaration-only: `namespace TypeName { fun helper(...) -> ... { ... } }` and `namespace TypeName { extern fun symbol(...) -> ... }`. Namespace calls use `TypeName.helper(...)` syntax and lower to internal lookup names using `TypeName__helper`.
- Call-only receiver method sugar is also supported: `value.helper(args...)` resolves through the receiver's concrete type namespace and rewrites to `TypeName.helper(value, args...)` before ownership/codegen. Plain field access remains variable-only, so `(expr).field` is still rejected while `(expr).helper(...)` is allowed.
- Stdlib sources and execution fixtures now prefer receiver method syntax whenever the helper's first parameter is the owning concrete type or specialization alias (`text.equals(other)`, `table.get(key)`, `vec.push(x)`); keep static namespace form for constructors, helpers whose receiver is not parameter 0 (for example `push_front(value, list)`), trait dispatch, and explicit namespace-vs-method syntax coverage.
- External declarations use `extern fun name(args...) -> Type` (no body). In v1 they may appear at top level and inside `namespace` blocks (no bodies, no `comptime`).
- In v2 ABI, `extern fun` signatures cannot use struct parameter or return types; C interop boundaries that move struct-like payloads must use manual `PtrInt` wrapper signatures.
- Struct field lists allow optional trailing commas in both type declarations and struct literals.
- Parser brace handling is newline-tolerant for braced declaration/block headers, so constructs like `enum Name` newline `{` and `if cond` newline `{` remain valid and format back to same-line braces.
- Ownership is move-only by default: reading a non-`Copy` value moves it, and subsequent reads fail (`use of moved value ...` / `cannot move from uninitialized value ...` diagnostics).
- `Copy` controls implicit cloning: when a concrete type implements `Copy`, read sites lower through static dispatch to the concrete `Copy.copy(...)` impl; the canonical trait shape is `copy(v: Ref[Self]) -> Self`, and the backend synthesizes a temporary `Ref` wrapper at read sites for ref-style impls (legacy by-value impl params are still accepted for now).
- `Drop` controls deterministic destruction: the resolver inserts `Drop.drop(value)` calls at reassignment overwrite points and lexical scope exits (reverse declaration order), skipping moved/uninitialized bindings.
- Struct equality is universal bytewise comparison: `==` / `!=` lower to `memcmp` over full struct size (including pointer-containing structs).
- The stdlib entrypoint `crates/oac/src/std/std.oa` is now an import aggregator over split files in `crates/oac/src/std/` (`std_ascii.oa`, `std_char.oa`, `std_null.oa`, `std_option_result.oa`, `std_string.oa`, `std_ref.oa`, `std_collections.oa`, `std_set.oa`, `std_vec.oa`, `std_traits.oa`, `std_json.oa`, `std_clib.oa`, `std_io.oa`).
- `crates/oac/src/std/std_traits.oa` defines core traits (`Hash`, `Eq`, `Copy`, `Drop`) and concrete scalar `Copy` impls (`Bool`, `U8`, `I32`, `I64`, `FP32`, `FP64`, `Char`, `AsciiChar`).
- The split stdlib now exposes namespaced helper APIs where applicable: JSON parsing helpers are called via `Json.*` (for example `Json.json_kind`, `Json.parse_json_document_result`, `Json.parse_json_document_value_result`).
- `crates/oac/src/std/std_json.oa` now defines a structured JSON value surface (`JsonValue`, `JsonMembers`, `JsonValues`) plus typed lookup helpers (`Json.object_get`, `Json.array_get`, `Json.value_string`, `Json.value_number`) so callers can parse into and inspect object/array trees.
- JSON booleans in the structured value surface now use payload form `JsonValue.Bool(Bool)` (replacing separate `True`/`False` variants), and `JsonKind` now reports booleans as `JsonKind.Bool`.
- JSON string scanning in `crates/oac/src/std/std_json.oa` now accepts `\uXXXX` escape forms (hex-validated, fail-closed on malformed escapes).
- The split stdlib collections now expose a richer persistent `LinkedList` template API: cached length via `len`/`length` (O(1) from node metadata), constructors/helpers (`empty`, `singleton`, `cons`, `push_front`), accessors (`front`, `tail`, `pop_front`, `at`, `at_or`), transforms (`append`, `reverse`, `take`, `drop`), and compatibility wrappers (`head_or`, `tail_or`, `length`); accessors now use local `Option` specializations (`FrontOption`, `TailOption`, `PopFrontOption`).
- `LinkedList[T]::Node` now carries a declaration-based struct invariant (`len >= 1`), and `LinkedList.make_node` normalizes/saturates cached `len` metadata before constructing nodes to keep that invariant provable fail-closed.
- The stdlib also exposes `AsciiChar` and `AsciiCharResult` with namespaced helpers (`AsciiChar.from_code`, `AsciiChar.from_string_at`, `AsciiChar.code`, `AsciiChar.is_digit`, `AsciiChar.is_whitespace`, `AsciiChar.equals`); `AsciiChar` stores a wrapped `Char`.
- The stdlib also exposes `Char` as an `I32` wrapper (`struct Char { code: I32 }`) with namespaced helpers (`Char.from_code`, `Char.code`, `Char.equals`).
- The stdlib now also exposes `Null` as an empty struct (`struct Null {}`) with namespaced constructor helper `Null.value()`.
- The stdlib now also defines `Bytes` (`struct Bytes { ptr: PtrInt, len: I32 }`) and `String` as a tagged enum (`Literal(Bytes)` / `Heap(Bytes)`) in `crates/oac/src/std/std_string.oa`; `String` is no longer a compiler-primitive type.
- The stdlib `String` namespace now also exposes convenience helpers in `crates/oac/src/std/std_string.oa`: `is_empty`, `equals`, `starts_with`, `ends_with`, `char_at_or`, and `slice_clamped`.
- The stdlib now also defines generic `Option[T]` / `Result[T, E]` in `crates/oac/src/std/std_option_result.oa` with namespaced constructors/helpers (`none`/`some`/`is_some`/`is_none`/`unwrap_or` and `ok`/`err`/`is_ok`/`is_err`/`unwrap_or`/`unwrap_err_or`).
- The stdlib now also defines generic `Ref[T]` and `Mut[T]` in `crates/oac/src/std/std_ref.oa` with pointer helpers (`from_ptr`, `ptr`, `is_null`, `add_bytes`); concrete specializations expose read-only dereference helpers (`U8Ref.read`, `I32Ref.read`, `I64Ref.read`, `PtrIntRef.read`, `BoolRef.read`) and mutable wrappers with read/write helpers (`U8Mut.*`, `I32Mut.*`, `I64Mut.*`, `PtrIntMut.*`, `BoolMut.*`).
- The stdlib `HashTable[K: Hash + Eq, V]` in `crates/oac/src/std/std_collections.oa` is now a dynamically resizing separate-chaining map (persistent value semantics) with APIs `new`, `with_capacity`, `set` (`SetResult { table, inserted_new }`), `get`, `remove` (`RemoveResult { table, removed }`), `len`, `capacity`, `contains_key`, and `clear`; fixed-size `put`/`size` APIs were removed.
- `HashTable[K: Hash + Eq, V]` currently has no declaration-based struct invariant; the previous `coherent_state` invariant was removed after fail-closed `solver unknown` obligations on the resize/rehash path, and behavior is now covered by runtime execution snapshots.
- Hash table metadata now has explicit runtime assertion guards in `HashTable.assert_metadata(...)` (`len >= 0`, `resize_threshold >= 1`, `len <= resize_threshold`) and this helper is applied on constructor/mutation return paths (`with_capacity`, `set_no_resize`, `rehash`, `maybe_resize_before_insert` passthrough, `remove`, `clear`).
- The stdlib now also defines generic `HashSet[K: Hash + Eq]` in `crates/oac/src/std/std_set.oa` as a persistent separate-chaining set with APIs `new`, `with_capacity`, `insert` (`InsertResult { set, inserted_new }`), `remove` (`RemoveResult { set, removed }`), `contains`, `len`, `capacity`, `clear`, `union`, `intersection`, and `difference`.
- The stdlib now also defines generic `Vec[T]` in `crates/oac/src/std/std_vec.oa` as a persistent vector-style container with APIs `new`, `with_capacity`, `push`, `pop` (`PopResult`), `get` (`Lookup`), `set` (`SetResult`), `len`, `capacity`, `reserve`, and `clear`.
- The stdlib now also defines `Io` wrappers in `crates/oac/src/std/std_io.oa` over `Clib` file-descriptor calls with explicit result enums (`IoError`, `IoReadResult`, `IoWriteResult`) and namespaced helpers `Io.read_all`, `Io.write_all`, `Io.read_file`, and `Io.write_file`.
- C interop in std is exposed through namespaced calls (`Clib.*`) and declared in `crates/oac/src/std/std_clib.oa` as `namespace Clib { extern fun ... }`; resolver keeps namespaced internal keys (`Clib__name`) while codegen emits declared extern symbol names for linking (for example `malloc`).
- Built-in `Void` is available for procedure-style signatures; `Void` is rejected as a parameter type, and both extern and non-extern functions may return `Void`.
- Built-in `U8` is available as an unsigned byte-like numeric type (`U8/U8` arithmetic and comparisons are allowed with no implicit coercions).
- The resolver also exposes `PtrInt` as a standard numeric alias hardcoded to `I64` (for pointer-sized integer use sites).
- Runtime pointer memory helpers are compiler builtins: `load_u8(addr: PtrInt) -> U8`, `load_i32(addr: PtrInt) -> I32`, `load_i64(addr: PtrInt) -> I64`, `load_bool(addr: PtrInt) -> Bool`, `store_u8(addr: PtrInt, value: U8) -> Void`, `store_i32(addr: PtrInt, value: I32) -> Void`, `store_i64(addr: PtrInt, value: I64) -> Void`, and `store_bool(addr: PtrInt, value: Bool) -> Void`.
- Character literals use single quotes and lower to `Char` construction (`'x'`, escapes like `'\n'` and `'\''`); parser lowers literals to `Char.from_code(...)`.
- Identifier tokenization is EOF-safe: trailing words (including `_`) now lex as `Word` tokens instead of panicking, which keeps `oac lsp` stable on incomplete buffers.
- `AsciiChar` range is enforced by a declaration-based struct invariant over its wrapped `Char` (`0 <= Char.code(ch) <= 127`); stdlib invariant declarations are now merged during `resolve` alongside stdlib types/functions/generics.
- `Bytes` length is enforced by a declaration-based struct invariant (`len >= 0`) in `crates/oac/src/std/std_string.oa`.
- Stdlib now also declares solver-stable global model invariants (2+ args) for function-law checks across core helpers: `Char` constructor/accessor/equality consistency (`from_code_roundtrip`, `equals_matches_code_equality`), `String` constructor normalization laws (`make_bytes_normalizes_len_and_keeps_ptr`, `normalize_len_is_non_negative`), `Option.none` predicate consistency, and pointer-wrapper round-trip laws for `Ref`/`Mut` (`from_ptr`/`ptr`).
- `String.make_bytes` in `crates/oac/src/std/std_string.oa` normalizes `Bytes.len` fail-closed (`len < 0` clamps to `0`) and is used by `String.from_literal_parts` / `String.from_heap_parts`; `String.bytes` now normalizes inline via `String.normalize_len` before constructing `Bytes` so invariant obligations stay solver-stable in execution fixtures.
- Built-in `FP32` and `FP64` are supported end-to-end. Unsuffixed decimal literals default to `FP32` (for example `1.25`), while `f64` suffix selects `FP64` (for example `1.25f64`). Numeric arithmetic/comparisons do not perform implicit widening/coercion between integer and floating types (`U8`, `I32`, `I64`, `FP32`, `FP64` stay same-type only).
- Fixed-width integer arithmetic uses runtime-faithful two's-complement wrapping semantics in both codegen and verification; `prove(...)` and struct/model-invariant obligations therefore quantify over wrapped `I32`/`I64` behavior rather than mathematical integers.
- Source-level integer arithmetic on `U8`, `I32`, `I64`, and `PtrInt` is now fail-closed at compile time: every reachable `+`, `-`, `*`, and `/` site in runtime code plus struct/model-invariant bodies must be proven overflow/underflow-safe during `check proofs`, and comptime `I32` evaluation now uses checked arithmetic with deterministic overflow/divide-by-zero diagnostics.
- Generic-specialized helper functions can be called with namespaced syntax (`Alias.helper(...)`), which lowers to generated mangled symbols like `Alias__helper`.
- The CLI now includes an `lsp` subcommand (`oac lsp`) that runs a stdio JSON-RPC language server with diagnostics.
- The CLI now also includes `oac fmt <file.oa>`, which applies the comment-safe formatter in place and fails closed on invalid input.
- Runtime codegen now supports two backends selected by flags on `oac build` / `oac test`: `--backend qbe|llvm` (default `qbe`), optional `--qbe-arch` (QBE-only), optional `--target` (shared linker/clang target triple override), and output controls `--quiet` / `--no-color`.
- Positional `arch` on `oac build` / `oac test` was removed; backend/target configuration is now flag-based.
- QBE remains mandatory as the verification source of truth: prove obligations, struct-invariant obligations, and loop non-termination classification always run on in-memory QBE output, regardless of runtime backend.
- Runtime artifact outputs are backend-specific: QBE emits `target/oac/ir.qbe` + `target/oac/assembly.s`; LLVM emits `target/oac/ir.ll` + `target/oac/object.o`.
- LLVM runtime lowering now compiles directly from `ir::ResolvedProgram` in `crates/oac/src/llvm_backend.rs` (no production IR->QBE->LLVM path and no `compile_with_qbe` runtime coupling).
- In the LLVM runtime backend, `prove(...)` remains verification-only and lowers as runtime no-op codegen.
- The LSP currently handles text sync plus `textDocument/definition`, `textDocument/hover`, `textDocument/documentSymbol`, `textDocument/references`, `textDocument/completion`, and whole-document `textDocument/formatting`.
- Compiler diagnostics are centralized in `crates/oac/src/diagnostics.rs` and rendered with Ariadne for both CLI output and `oac lsp` diagnostic conversion.
- `oac build` / `oac test` stage failures are now mapped to stable diagnostic codes (for example `OAC-PARSE-001`, `OAC-RESOLVE-001`, `OAC-INV-001`, `OAC-MINV-001`, `OAC-LINK-001`, `OAC-LINK-002`) and emitted as Ariadne reports; execution fixture compilation-error snapshots therefore reflect Ariadne plain-report text.
- `oac build` and `oac test` now emit a compact staged progress UI to `stderr` by default with user-facing stage labels (`prepare source`, `check program`, `check proofs`, `check data rules`, `check global rules`, `check loops`, `generate backend`, `link executable`; plus `collect tests`/`run tests` for test flows), aligned durations, and low-noise ASCII status prefixes (`...`, `ok`, `!!`).
- `--quiet` suppresses build/test harness/progress output (success path fully silent) while keeping diagnostics and `oac test` runtime program stdout/stderr forwarding behavior.
- `--no-color` disables ANSI color for both staged progress rows and Ariadne diagnostic rendering for that build/test invocation.
- `oac build`, `oac test`, and `oac bench-prove` now accept `--proof-cache trust|strict|off`; build/test default to `trust`, while `bench-prove` defaults to `strict`.
- A VS Code extension scaffold now lives in `tools/vscode-ousia/`; it launches `oac lsp` and is configured via `ousia.server.path`, `ousia.server.args`, and `ousia.trace.server`.
- The VS Code extension manifest is categorized under both `Programming Languages` and `Formatters` so formatter-filtered extension discovery includes Ousia.
- Repo root `install-vscode-extension.sh` installs the VS Code extension end-to-end by running dependency install, TypeScript build, `@vscode/vsce package`, and `code --install-extension ... --force`.
- The VS Code extension must launch `oac lsp` without appending `--stdio`; `ousia.server.args` are sanitized to ignore `--stdio`.
- Repo workspace settings in `.vscode/settings.json` point the VS Code extension at `cargo run -q -p oac -- lsp`, set `ousia-lang.ousia-vscode` as the default formatter for `[ousia]` files, and enable format-on-save for that language.
- Formatter snapshot inputs now live under `crates/oac/formatter_tests/*.oa`, with invalid formatter fixtures under `crates/oac/formatter_invalid_tests/*.oa`; formatted output snapshots are stored in `crates/oac/src/snapshots/`.
- Top-level tests use declaration syntax: `test "Name" { ... }`.
- The CLI now includes `oac test <file.oa>`: it lowers `test` declarations into generated helper functions plus a generated `main`, compiles under `target/oac/test/`, and executes tests fail-fast (assert failures exit with `242`).
- The CLI now also includes `oac bench-prove`: end-to-end proving benchmark runner over curated execution fixtures with suites `full` (default) and `quick`, configurable iterations, optional baseline/report path overrides, deterministic `--update-baseline` rewriting, and optional `--strict-outcome-gate` baseline-vs-candidate verification outcome checks.
- Repo-local proof summaries are cached under `target/oac/verification_cache/` as content-hash-keyed JSON summaries; ordinary-function summaries combine all local `prove(...)` and struct-invariant obligations for one root function, while model invariants cache one summary per invariant checker function.
- Ordinary-function proof summaries now also include integer-safety obligations, so one cache hit for a root function simultaneously trusts explicit `prove(...)`, reachable source-level integer arithmetic checks, and struct-invariant return-site checks for that root.
- Proving benchmark baseline is committed at `crates/oac/bench/prove_baseline.json`; default report output is `target/oac/bench/prove/latest.json`, and isolated per-fixture benchmark run artifacts are emitted under `target/oac/bench/runs/<fixture>/iter_<n>/`.
- In the current benchmark fixture contract, `template_hash_table_i32` is expected to compile/verify successfully (`expected_code = null`) rather than fail with `OAC-INV-001`.
- The benchmark full suite now also includes model-invariant fixtures (`model_invariant_pass`, `model_invariant_fail`), and benchmark invariant artifact metrics aggregate both `struct_invariants/*.smt2` and `model_invariants/*.smt2`.
- Strict outcome-gate artifacts are emitted under `target/oac/verification_outcomes/` as `baseline.json` and `candidate.json` (schema version `1`), with per-profile compile runs under `target/oac/verification_outcomes/runs/`.
- `oac bench-prove` uses report-only timing regression policy in v1 (regression when both `delta_ms >= 200` and `delta_pct >= 20.0`), but still fails fail-closed on unexpected fixture outcomes (unexpected success/failure or diagnostic code mismatch).
- `oac bench-prove --strict-outcome-gate` enforces outcome-transition safety: baseline `sat`/`unsat` obligations must remain identical in candidate runs; only baseline `unknown` obligations may change (`unknown -> sat|unsat|unknown`), and obligation-key set drift is fail-closed.
- Verification-outcome capture for strict outcome-gate is fixture-scoped via thread-local context (`verification_outcomes::with_fixture_context`); untagged records are ignored so parallel test execution cannot pollute baseline/candidate obligation sets.
- `bench-prove` treats proof-cache access as read-only in v1 so benchmark timings and strict outcome-gate runs stay live-solve measurements; cache hits never shorten the default benchmark path.
- `prove(cond)` and `assert(cond)` are statement-only builtins with call syntax. `prove` is compile-time (fail-closed); `assert` is runtime and exits with code `242` on failure.
- Function names `prove` and `assert` are reserved and cannot be user-defined.
- Invariant declarations accept one or more parameters in `for (...)` for both single and grouped forms (`invariant [identifier]? "label" for (...) { ... }` and `invariant for (...) { ... }`).
- Arity-sensitive semantics: arity `1` remains struct-invariant behavior; arity `2+` declarations become global model invariants.
- Unary struct-invariant clauses are tracked independently per struct type; the compiler synthesizes internal functions named `__struct__<TypeName>__invariant__<key>` (`<key>` is identifier-based or deterministic anonymous ordinal such as `anon_0`) and still accepts legacy explicit functions named `__struct__<TypeName>__invariant(v: TypeName) -> Bool`.
- Multi-argument model-invariant clauses synthesize internal functions named `__model__invariant__<key>` (`<key>` from identifier or deterministic anonymous ordinal such as `anon_0`), and identifiers must be unique across model invariants.
- Model invariants are resolve-validated as a strict pure subset: transitive user-call graph traversal rejects `prove`/`assert`, extern calls, pointer load/store builtins, and side-effect builtins (`print`, `print_str`).
- During `oac build`, verification obligations are orchestrated by `crates/oac/src/verification.rs`: it runs prove verification first, then struct-invariant verification, then model-invariant verification.
- During `oac build`, prove obligations are verified first at reachable `prove(...)` sites by synthesizing per-site QBE checker functions that return `1` on violated proof conditions and `0` on success (`unsat` passes, `sat` fails). Before reachable-callee closure, the cloned checker entry CFG is pruned to blocks that can still reach the targeted prove site, so off-target branches and their callees do not enter the obligation. Debug artifacts are emitted under `target/oac/prove/`.
- During `oac build`, source-level integer arithmetic obligations are also verified in `check proofs`: `qbe_backend` emits lightweight `.oac_integer_site_<type>__<op>__<id>` marker copies around integer `+/-/*//` expressions, `integer_safety.rs` collects sites reachable from `main` and all struct/model-invariant roots, and per-site checker artifacts are emitted under `target/oac/integer_safety/`. Integer-safety checkers use the same shared target-reachability pruning on the cloned caller CFG before checker-module closure.
- During `oac build`, struct invariants are verified per `(call-site, invariant)` pair at user-function call return sites (reachable from `main`) by synthesizing per-site QBE checker functions from compiled QBE: the target call site is instrumented with one invariant check and checker exit is `1` on violation / `0` on success (`unsat` passes, `sat` fails). Like prove checkers, the cloned checker entry CFG is pruned to blocks that can still reach the targeted call site before reachable-callee closure.
- During `oac build`, model invariants are verified globally (independent of `main` reachability): each declaration emits one checker obligation where checker `main` returns `1` on invariant violation (`ret == 0`) and `0` on success; checker artifacts are emitted under `target/oac/model_invariants/`.
- Prove, struct-invariant, and model-invariant CHC solving keeps baseline two-step retries (`10s`, `30s`) and optionally adds a third attempt for candidate profile only when the SMT obligation is large and still `unknown` after retry.
- Candidate third-attempt tuning is controlled by `OAC_Z3_LARGE_OBLIGATION_BYTES` (default `8000000`) and `OAC_Z3_TIMEOUT_LARGE_OBLIGATION_SECS` (default `90`); solver engine/result semantics remain unchanged (`sat` fail, `unsat` pass, `unknown` fail-closed).
- Unknown diagnostics now include solver-attempt ladders (`attempts=[...]`) with timeout/result/reason snippets in prove, struct-invariant, and model-invariant failures.
- Struct-invariant obligation identifiers now include the invariant key suffix in diagnostics/debug artifacts (`<caller>#<site>#<ordinal>#<invariant_key>`), and generated checker artifacts follow the same suffixing pattern (`site_<caller>_<site>_<ordinal>_<invariant_key>.qbe` / `.smt2`).
- Checker synthesis is QBE-native and interprocedural: each site emits a checker entry function plus reachable user callees, and CHC encoding models user calls via per-function summary relations (`*_ret` / `*_abort`) instead of checker-time call inlining.
- Prove, struct-invariant, and model-invariant pipelines now share checker assembly utilities in `crates/oac/src/verification_checker.rs` (site-id sanitization, solver excerpt summarization, checker return normalization, reachable-callee module closure, and main-argc assumption gate).
- Reachable-callee discovery in `verification_checker::direct_user_callees` now traverses only entry-reachable CFG blocks (and stops scanning a block after terminators), preventing dead-block calls from polluting checker module closure and argument-invariant assumptions.
- Verification checker entry functions now rewrite only the compiler-generated assert-fail pattern (`call $exit(w 242)` immediately followed by `hlt`) into safe `ret 0` before SMT encoding, so assertion-failure paths in the entry clone stop cheaply without letting helper callees continue after terminal asserts; other `exit(...)` uses stay modeled as aborts.
- Verification profile/policy plumbing lives in `crates/oac/src/verification_profile.rs`, `crates/oac/src/verification_solver.rs`, and `crates/oac/src/verification_cache.rs`; ordinary-root verification-session orchestration lives in `crates/oac/src/verification.rs`, and outcome capture/comparison helpers live in `crates/oac/src/verification_outcomes.rs`.
- Parser-AST recursion helpers are centralized in `crates/oac/src/ast_walk.rs` and reused by resolve, verification-cycle analysis, and struct-invariant site indexing/call collection to keep traversal semantics aligned.
- Trait symbol key helpers are centralized in `crates/oac/src/symbol_keys.rs` and reused by resolve and QBE codegen (`Trait::method`, impl-target keys, impl-method keys, mangled impl function names).
- Checker encoding now adds function-entry preconditions for invariant-bearing arguments in prove, struct-invariant, and model-invariant pipelines: for each checker function argument whose semantic type has struct invariants, `qbe-smt` assumes each corresponding invariant relation holds and returns non-zero at entry (assumption-only; entry memory/heap state is not replaced with invariant-call outputs).
- Checker encoding also adds fail-closed integer range assumptions where available: `qbe-smt` now accepts per-function argument range assumptions, and all verification pipelines inject `[0,255]` entry assumptions for semantic `U8` parameters in checker modules.
- The legacy struct-invariant checker call-inliner has been removed; struct-invariant obligations now only use module-level CHC encoding (`qbe_module_to_smt_with_assumptions`, wrapped by `qbe_module_to_smt`) for checker entry plus reachable callees.
- Shared recursion-cycle analysis is implemented in `crates/oac/src/verification_cycles.rs` using SCCs over the combined verification graph with deterministic witness diagnostics.
- Call-only recursion cycles are allowed during struct invariant, prove, and model-invariant verification; cycles that include argument-invariant precondition edges are rejected fail-closed on the combined verification graph.
- Build/test environments that hit invariant obligations require `z3`; debug SMT artifacts are emitted under `target/oac/struct_invariants/` and `target/oac/model_invariants/`.
- `main` signatures are intentionally restricted to `fun main() -> I32`, `fun main(argc: I32, argv: I64) -> I32`, or `fun main(argc: I32, argv: PtrInt) -> I32`.
- Solver encodings treat `argc` as non-negative by default (`argc >= 0`) when enabled by the caller.
- `qbe-smt` is CHC-only (fixedpoint/Spacer): it emits Horn-style transition rules over QBE and always queries whether halting with `exit == 1` is reachable. Encoder scripts use `(set-logic HORN)` for non-FP obligations and `(set-logic ALL)` when reachable FP32 or FP64 operations are present.
- `qbe-smt` is strict fail-closed: unsupported instructions/operations are hard encoding errors (no conservative havoc fallback).
- `qbe-smt` is parser-free and consumes in-memory QBE IR directly as modules (`qbe::Module` via `qbe_module_to_smt` / `qbe_module_to_smt_with_assumptions`).
- `qbe-smt` now supports FP32/FP64 obligations end-to-end in prove/struct-invariant/model-invariant checking for the currently emitted subset (FP32/FP64 args/results, `copy`, `add/sub/mul/div`, `cmp` `eq/ne/lt/le/gt/ge/o/uo`, `phi`, `exts`/`truncd`, `stosi`/`stoui`/`dtosi`/`dtoui` with `RTZ`, `swtof`/`uwtof`/`sltof`/`ultof` with `RNE`, and `loads`/`stores`) using SMT IEEE floating-point semantics.
- Float-conversion edge cases follow solver IEEE-SMT semantics in `qbe-smt` and may differ from CPU-specific runtime behavior for NaN/out-of-range float-to-int conversions.
- `qbe-smt` remains fail-closed for unsupported instructions and invalid conversion assignment-type combinations.
- Snapshot coverage now includes float-literal tokenizer fixtures and a parser AST snapshot regression (`parser_float_literals_ast`) to lock float literal parsing behavior.
- `qbe-smt` now tracks predecessor-block identity (`pred`) only for functions whose reachable QBE contains `phi`; PC relations for functions without reachable `phi` omit `pred`, while `phi`-bearing functions keep predecessor-guarded Horn transitions.
- `qbe-smt` source split: `lib.rs` (public API + tests), `encode.rs` (core CHC/Horn encoding), `encode_extern_models.rs` (extern call model catalog/arity), `classify.rs` (loop classification).
- Bounded CLib/string helper expression builders in `crates/qbe-smt/src/encode.rs` (`bounded_copy_expr`, `bounded_set_expr`, `bounded_havoc_expr`, `bounded_strcpy_expr`, `bounded_memcmp_result_expr`, `bounded_strlen_result_expr`, `bounded_strcmp_result_expr`) now use linearized `let`-chain construction to reduce SMT expression blow-up while preserving precision/fallback policy.
- Legacy bounded-helper implementations are retained in test-only scope in `encode.rs` and checked with solver-backed equivalence tests (`legacy == refactored` over symbolic inputs and representative limits).
- CHC solving is centralized in `qbe-smt` (`solve_chc_script` / `solve_chc_script_with_diagnostics`); struct invariant verification uses this shared backend runner instead of owning a separate Z3 invocation path.
- `qbe-smt` solver stdin writes now treat `BrokenPipe` as an early solver termination signal and still read solver stdout/stderr for result classification (`sat`/`unsat`/`unknown`), instead of surfacing transport-layer pipe errors directly.
- `qbe-smt` now exposes Ariadne report helpers on `QbeSmtError` (`render_report_plain`, `render_report_terminal_auto`) and `oac` includes those reports in prove/struct-invariant/model-invariant failure notes.
- `qbe-smt` now models a wider CLib call set in CHC encoding: `malloc`, `free`, `calloc`, `realloc`, `memcpy`, `memmove`, `memcmp`, `memset`, `strlen`, `strcmp`, `strcpy`, `strncpy`, `open`, `read`, `write`, `close`, plus `exit(code)` halting transitions (and variadic `printf` for compiler builtin `print` inlining).
- CLib byte-effect models are bounded with deterministic inline precision (`limit = 16`) and sound fallback branches; unknown extern call targets remain strict fail-closed errors.
- `qbe-smt` now models bounded `strlen` NUL-scan and bounded `strcmp` first-event scan (`difference` or shared NUL) with tri-state outcomes (`-1/0/1`) and fail-open fallback to constrained unknowns when precision bounds are exceeded.
- `qbe-smt` now models `strcpy` as bounded byte copy until first NUL (including terminator) with fallback to unconstrained memory when no terminator is found within the inline bound.
- `qbe-smt` now constrains modeled syscall-like return values: `open` returns `-1` or non-negative, `close` returns `0` or `-1`, and `read`/`write` return `-1` or a non-negative value bounded above by `count`.
- CHC encoding only includes reachable QBE blocks from entry; unsupported instructions in unreachable blocks are ignored by design.
- SAT struct-invariant failures now include a control-flow witness summary (checker CFG path + branch choices).
- `oac build` no longer emits `target/oac/ir.smt2` sidecar output; SMT artifacts are produced only for verification obligations under `target/oac/prove/`, `target/oac/struct_invariants/`, and `target/oac/model_invariants/`.
- Build/test environments that hit prove obligations also require `z3`; debug SMT artifacts are emitted under `target/oac/prove/`.
- `oac build` now runs a best-effort non-termination classifier on the generated QBE `main` function; when it proves a canonical while-loop is non-terminating, compilation fails early with the loop header label and proof reason.
- Build/test linking now uses C compiler drivers (`cc`/`clang`/target-prefixed `*-gcc`) instead of Zig. Link step is fail-closed and supports `OAC_CC` (single explicit command), `CC` (preferred first attempt), `OAC_CC_TARGET`, and `OAC_CC_FLAGS`.
- LLVM runtime lowering lives in `crates/oac/src/llvm_backend.rs`, is consumed through `crates/oac/src/codegen_runtime.rs`, and runtime backend dispatch never changes verification backend selection.
- Shared runtime data-layout constants/helpers for both QBE and LLVM backends live in `crates/oac/src/runtime_layout.rs`.
- Linker-stage diagnostics now use `DiagnosticStage::Linker` and stable codes `OAC-LINK-001` / `OAC-LINK-002` (legacy `OAC-ZIG-*` names are removed).
- Execution fixture snapshots in `qbe_backend` are based on program stdout even when the process exits with a non-zero code; runtime errors are reserved for spawn failures, timeouts, invalid UTF-8, or signal termination.
- `crates/oac/src/qbe_backend.rs` execution fixtures compile/execute inside a fail-fast worker harness: each fixture asserts its snapshot as soon as it finishes, the queue is cleared on the first snapshot mismatch, and the first failure is rethrown on the main test thread. Worker count defaults to serial (`1`) for stability and can be overridden with `OAC_EXECUTION_TEST_JOBS=<n>` for explicit parallel runs.
- Snapshot hygiene is test-gated: committed `*.snap.new` files, execution snapshots without matching `execution_tests/*.oa` fixtures, and duplicated Ariadne prefixes (`Error: error[...]`) are treated as test failures.
- Treat metadata-only insta churn (`assertion_line` / `expression` header updates) the same way: accept into the canonical `.snap` or delete the `.snap.new` artifact so no tracked `*.snap.new` files remain.
- GitHub Actions CI now runs Rust checks in parallel jobs in `.github/workflows/ci.yml`: `cargo check --all-targets --all-features` (`check`) and `cargo nextest run --all-targets --all-features` (`nextest`).
- The `nextest` CI job provisions backend test/build dependencies (`z3`, Zig via `goto-bus-stop/setup-zig@v2` pinned to `0.13.0`, and `qbe` built from upstream `qbe-1.2` source tarball) and installs `cargo-nextest` via `taiki-e/install-action@nextest`.

## Hard-Cut Migration Cheatsheet

- Old: `template Option[T] { ... }` -> New: `generic Option[T] { ... }`
- Old: `instantiate OptionI32 = Option[I32]` -> New: `specialize OptionI32 = Option[I32]`
- Old key ops in generic hash tables: direct integer hash/`==` -> New: trait-bounded calls (`Hash.hash(k)`, `Eq.equals(a, b)`) with bounds like `[K: Hash + Eq, V]`
