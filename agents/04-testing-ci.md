# Testing and CI

## CI Contract

Defined in `.github/workflows/ci.yml`:
- `cargo check --all-targets --all-features`
- `cargo test --all-targets --all-features`
- backend dependency provisioning before Rust checks:
  - `z3` (required for struct invariant/prove obligations)
  - `qbe` (required for backend assembly generation in execution-style tests; CI builds/installs upstream `qbe-1.2` from `https://c9x.me/compile/release/`)
  - Zig via `goto-bus-stop/setup-zig@v2` (pinned to `0.13.0`, used as `zig cc`)

Any change should keep both green.

Note: CI does not currently build the VS Code extension under `tools/vscode-ousia`; validate it locally when touching editor integration files.

## Local Commands

From repository root:

```bash
cargo check --all-targets --all-features
# Prefer nextest when available (faster local execution).
cargo nextest run --all-targets --all-features
```

Fallback when `cargo-nextest` is not installed:

```bash
cargo test --all-targets --all-features
```

Targeted crate:

```bash
# Prefer nextest when available.
cargo nextest run -p oac
cargo nextest run -p qbe-smt
```

Fallback when `cargo-nextest` is not installed:

```bash
cargo test -p oac
cargo test -p qbe-smt
```

VS Code extension (when changing files under `tools/vscode-ousia`):

```bash
cd tools/vscode-ousia
npm install
npm run build
npm run lint
```

When debugging extension startup, verify the server command is exactly `oac lsp` (no extra `--stdio` argument).

## Local Git Hooks

This repository tracks local hooks under `.githooks/`.

Enable once per clone/worktree:

```bash
git config core.hooksPath .githooks
```

Install/update formatter toolchain used by `pre-commit`:

```bash
rustup toolchain install nightly --component rustfmt
```

Hook behavior:
- `pre-commit`: formats staged `*.rs` files with nightly `rustfmt` using `rustfmt.toml` (import sorting/grouping enabled for lower merge-conflict churn), then re-stages those files.
- `pre-push`: no-op placeholder (does not run tests automatically).

Bypass for exceptional WIP cases:
- `git commit --no-verify`
- `git push --no-verify`

## Snapshot-Based Testing

Key tests:
- `crates/oac/src/tokenizer.rs` test loads `crates/oac/tokenizer_tests/*`.
- `crates/oac/tokenizer_tests/float_literals.oa` snapshots tokenization for mixed float literals (`1.25`, `2.5f64`) via `tokenizer::tests::tokenize_files`.
- `crates/oac/tokenizer_tests/char_literals.oa` snapshots tokenization for char literals (including escapes) via `tokenizer::tests::tokenize_files`.
- `crates/oac/src/tokenizer.rs` also has a unit regression for FP32 decimal tokenization (`TokenData::Float`).
- `crates/oac/src/tokenizer.rs` also covers `f64` suffix tokenization (`Float` token followed by `Word(\"f64\")`).
- `crates/oac/src/tokenizer.rs` includes EOF word-lexing regressions to prevent LSP crash loops on partial files (`tokenizes_identifier_at_eof_without_panicking`, `tokenizes_underscore_identifier_at_eof_without_panicking`).
- `crates/oac/src/parser.rs` tests assert generic bracket syntax parsing (including multi-parameter inline bounds), nested generic type arguments, trait/impl parsing, hard-cut legacy `template`/`instantiate` rejection with migration hints, struct-invariant declaration syntax for both single and grouped forms (`invariant [id]? "label" for (...)` and `invariant for (...) { ... }`, including inside generics), mandatory display labels, and optional identifiers.
- `crates/oac/src/parser.rs` also includes top-level test declaration parsing coverage (`test "..." { ... }`).
- `crates/oac/src/parser.rs` tests also cover namespace declaration parsing and namespaced call syntax (`TypeName.helper(...)`).
- `crates/oac/src/parser.rs` also covers top-level `extern fun` parsing plus namespace-scoped extern parsing (`namespace Name { extern fun ... }`) including internal-name mangling and preserved extern symbol names.
- `crates/oac/src/parser.rs` includes an AST snapshot regression (`parser_float_literals_ast`) for mixed FP32/FP64 literal parsing.
- `crates/oac/src/parser.rs` also includes a regression for FP32 literal parsing (`Literal::Float32`).
- `crates/oac/src/parser.rs` also includes a regression for FP64 literal parsing (`Literal::Float64` from `f64` suffix).
- `crates/oac/src/parser.rs` also includes a char-literal AST snapshot regression (`parser_char_literals_ast`) that locks lowering (`'x'` -> `Char__from_code` call).
- `crates/oac/src/flat_imports.rs` tests assert flat import resolution: merge behavior, same-directory path constraints, and cycle detection.
- `crates/oac/src/flat_imports.rs` merge coverage also includes imported test declaration propagation.
- `crates/oac/src/ir.rs` includes a regression test that stdlib split files are loaded through `crates/oac/src/std/std.oa` imports.
- That regression currently asserts representative split-stdlib symbols including JSON (`Json__parse_json_document`), trait symbols (`Hash::hash`, `Eq::equals`, and synthesized impl functions like `Hash__I32__hash`), ASCII helpers (`AsciiChar`, `AsciiChar__from_code`), char/null/string helpers (`Char__from_code`, `Null__value`, `String__from_literal_parts`, `String__from_heap_parts`, `String__equals`, `String__starts_with`, `String__ends_with`, `String__slice_clamped`), option/result generics (`Option`, `Result` generic declarations), ref/mut helpers (`U8Ref`, `I32Ref`, `I64Ref`, `PtrIntRef`, `BoolRef`, `U8Mut`, `I32Mut`, `I64Mut`, `PtrIntMut`, `BoolMut`, plus `*Ref__read` and `*Mut__write` functions), C externs (`Clib__malloc`, `Clib__free`, `Clib__memcmp`), and standard aliases/types (`PtrInt`, `U8`, `Void`, `Bytes`, std-defined `String` enum).
- The same regression also asserts stdlib invariant registration/synthesis for `AsciiChar` and `Bytes` (`struct_invariants[...]` metadata plus synthesized `__struct__*__invariant__<key>` functions).
- `crates/oac/src/ir.rs` also validates accepted `main` signatures (`main()`, `main(argc: I32, argv: I64)`, and `main(argc: I32, argv: PtrInt)`).
- `crates/oac/src/ir.rs` includes alias coverage for `PtrInt` behaving as `I64` in function calls/equality and type-definition mapping.
- `crates/oac/src/ir.rs` also validates namespace call resolution/type-checking by lowering to mangled function names (`TypeName__helper`).
- `crates/oac/src/ir.rs` also validates trait-system behavior: duplicate impl rejection, impl signature mismatch rejection, missing bound impl failures at specialization, and trait-call dispatch/type-check through concrete impl symbols.
- `crates/oac/src/ir.rs` also validates `Void`/extern constraints: accepted statement calls to `Void` externs, rejection of `Void` parameters, and rejection of non-extern `Void` returns.
- `crates/oac/src/ir.rs` also validates v2 extern ABI restrictions by rejecting struct parameters/returns in `extern fun` signatures with diagnostics that direct users to `PtrInt` wrappers.
- `crates/oac/src/ir.rs` also includes FP32 resolve/type-check regression coverage (FP32 arithmetic + comparison in `main`).
- `crates/oac/src/ir.rs` also includes FP64 resolve/type-check regression coverage (FP64 arithmetic + comparison in `main`).
- `crates/oac/src/ir.rs` also includes `U8` coverage for accepted same-type arithmetic/comparison and rejection of mixed `U8`/`I32` arithmetic.
- `crates/oac/src/ir.rs` also includes resolve coverage for builtin pointer-memory helpers (`load_u8`, `load_i32`, `load_i64`, `load_bool`, `store_u8`, `store_i32`, `store_i64`, `store_bool`) with `PtrInt` addresses.
- `crates/oac/src/ir.rs` also includes resolve/type-check coverage for std `Char` API usage together with char literals.
- `crates/qbe-smt/src/lib.rs` tests (built from in-memory `qbe::Function` and `qbe::Module` fixtures) cover CHC/fixedpoint encoding shape (`HORN`, relation declarations, `(query bad)`), branch/loop rule generation, integer+memory modeling, interprocedural user-call summaries (including self-recursive user calls), argument-invariant precondition assumptions, and strict rejection of unsupported operations.
- `crates/qbe-smt/src/lib.rs` validates modeled CLib call coverage (`memcpy`, `memmove`, `memcmp`, `memset`, `calloc`/`realloc`/`free`) in addition to `exit(code)` halting transitions and malformed exit-call rejection.
- `crates/qbe-smt/src/lib.rs` additionally covers `phi` encoding via predecessor-state guards and rejection of malformed/unknown `phi` labels.
- `crates/qbe-smt/src/lib.rs` also verifies reachable-only encoding behavior (unsupported instructions inside unreachable blocks are ignored).
- `crates/qbe-smt/src/lib.rs` is also the shared CHC solver entrypoint (`solve_chc_script` and `solve_chc_script_with_diagnostics`) used by struct invariant verification.
- `crates/qbe-smt/src/lib.rs` also covers Ariadne rendering helpers on `QbeSmtError` (`render_report_plain` / `render_report_terminal_auto`).
- `crates/qbe-smt/src/lib.rs` also tests loop classification (`classify_simple_loops`) for proven non-termination patterns (identity updates, including `call $sub(..., 0)`) vs unknown/progress loops.
- `crates/oac/src/diagnostics.rs` tests cover tokenizer span conversion, plain (no ANSI) report rendering, and no-span fallback rendering.
- `crates/oac/src/diagnostics.rs` tests also enforce diagnostic headline quality for Ariadne plain reports (no duplicated `Error: error[...]` prefixing) and message/cause dedup behavior in `diagnostic_from_anyhow`.
- `crates/oac/src/lsp.rs` tests cover diagnostics, definition/references lookup (including across flat imports), hover (including namespaced function calls), completion, document symbols, and file-URI handling.
- `crates/oac/src/invariant_metadata.rs` tests cover multi-binding discovery per struct and argument-assumption cross-product expansion when parameter types carry multiple invariants.
- `crates/oac/src/struct_invariants.rs` tests cover invariant discovery/validation for declaration-based invariants, grouped invariant declarations, legacy function-name compatibility, generic concrete-name support, obligation-site scoping, deterministic call-site ordinals, per-`(call-site, invariant)` obligation expansion, argument-invariant checker preconditions, recursion-cycle policy (call-only cycles allowed, cycles with arg-invariant edges rejected fail-closed), and module-level QBE-native checker synthesis/CHC encoding behavior (including modeled `memcpy` encoding and fail-closed unknown external calls).
- `crates/oac/src/prove.rs` verifies compile-time `prove(...)` obligations over QBE-native checker synthesis and CHC solving, including multi-invariant argument preconditions, recursion-cycle policy (call-only cycles allowed, cycles with arg-invariant edges rejected fail-closed), and no-op behavior when no prove sites exist.
- SAT invariant failures emitted by `struct_invariants.rs` include a compact control-flow witness summary (`cfg_path` + branch steps) and attempt to include concrete `program_input` data (`argc` witness for `main(argc, argv)` sites).
- Struct-invariant obligation IDs and checker artifact names now include invariant-key suffixes (for example `main#1#0#stable_envelope` and `site_main_1_0_stable_envelope.{qbe,smt2}`); older unsuffixed snapshot text should be treated as stale.
- `crates/oac/src/main.rs` tests cover build-time rejection when `main` contains a loop proven non-terminating by QBE loop classification.
- `crates/oac/src/test_framework.rs` tests cover isolated lowering behavior for `oac test`: generated test functions/main plus error cases (no tests, user-defined `main`).
- `crates/oac/src/qbe_backend.rs` test loads `crates/oac/execution_tests/*`, compiles fixtures, and snapshots either compiler errors or program stdout (non-zero exit codes are allowed; only spawn/timeout/signal/UTF-8 failures are runtime errors). Compiler-error snapshots now capture Ariadne plain-report output from the shared diagnostics layer.
- `crates/oac/src/qbe_backend.rs` also enforces snapshot hygiene contracts for execution snapshots: no committed `*.snap.new` files, no orphan execution snapshots without matching fixtures, and no duplicated Ariadne prefix artifacts (`Error: error[...]`) in snapshot content.
- `crates/oac/src/qbe_backend.rs` also has a unit test that asserts QBE emission for namespaced calls contains mangled function call symbols.
- `crates/oac/src/qbe_backend.rs` also has a unit test that asserts statement-position `Void` extern calls are emitted (`call $free`).
- `crates/oac/src/qbe_backend.rs` also has a unit test that asserts `i32_to_i64` lowering uses signed extension (`extsw`) and not byte extension (`extub`).
- `crates/oac/src/qbe_backend.rs` also has a unit test that asserts FP32 lowering emits single-precision constants/ops and ordered float comparisons.
- `crates/oac/src/qbe_backend.rs` also has a unit test that asserts FP64 lowering emits double-precision constants/ops and ordered float comparisons.
- `crates/oac/src/qbe_backend.rs` also has a unit test that asserts `U8` lowers with unsigned comparison/division ops (`cultw`, `udiv`).
- `crates/oac/src/qbe_backend.rs` also has a unit test that asserts pointer-memory builtins lower to expected QBE ops (`loadub`, `loadw`, `loadl`, compare-to-zero for bool, `storeb`, `storew`, `storel`).
- `crates/oac/src/qbe_backend.rs` also has a unit test that asserts char literals lower through `call $Char__from_code`.
- `crates/oac/src/qbe_backend.rs` also has a unit regression that asserts struct by-value barriers and equality lowering emit `calloc`/`memcpy` clones plus `call $memcmp` (`qbe_codegen_structs_use_copy_barriers_and_memcmp_equality`).
- `crates/qbe-rs/src/tests.rs` includes coverage for FP32/FP64 constant formatting (`s_<literal>`, `d_<literal>`) and ordered float compare formatting (`clts`, `cgtd`).
- Execution fixtures now include dedicated prove/assert coverage:
  - `prove_pass.oa`
  - `prove_fail.oa`
  - `prove_statement_only.oa`
  - `assert_pass.oa`
  - `assert_fail.oa`
- Execution fixtures also include namespace call coverage:
  - `namespace_basic.oa`
- Execution fixtures also include large-string length regression coverage:
  - `string_len_large.oa`
- Execution fixtures now include trait-bounded generic hash table coverage:
  - `generic_hash_table_custom_key.oa` (currently a fail-closed invariant-check diagnostic snapshot; this fixture now reaches struct-invariant solving and exits with `OAC-INV-001` unknown-solver status for a large obligation)
  - `generic_hash_table_missing_impl.oa` (negative missing bound impl diagnostic)
- Execution fixtures also include struct V2 equality semantics coverage:
  - `struct_equality_v2_memcmp.oa` (equal and unequal struct comparisons plus pointer-containing struct bytewise-equality behavior)
- Execution fixtures also include read-only ref/deref coverage:
  - `std_ref_read_only.oa` (read-only typed dereference via `Ref[T]` specializations and zero-initialized memory checks)
- Execution fixtures also include mutable pointer-wrapper coverage:
  - `std_mut_read_write.oa` (`Mut[T]` typed read/write helpers over `U8`, `I32`, `I64`, `PtrInt`, and `Bool`; `U8` write assertions are validated through `U8` read/write round-trip equality flags because integer literals are `I32` and do not implicitly coerce to `U8`)
- Execution fixtures also include canonical option/result stdlib coverage:
  - `std_option_result.oa` (`Option[T]` and `Result[T,E]` constructors/predicates/unwrapping helpers)
- Execution fixtures also include string utility helper coverage:
  - `std_string_helpers.oa` (`String.equals`, `String.starts_with`, `String.ends_with`, `String.char_at_or`, `String.slice_clamped`, `String.is_empty`)
- Stdlib namespacing coverage in execution fixtures:
  - JSON helpers are exercised through `Json.*` calls in `json_parser.oa`, `json_document.oa`, and `json_scan_utils.oa`.
  - Generic-specialized stdlib helpers are exercised through namespaced call syntax (`IntList.*`, `IntTable.*`) in `template_linked_list_i32.oa`, `template_linked_list_v2_i32.oa`, and `template_hash_table_i32.oa` (fixture filenames are legacy-prefixed, syntax is `generic/specialize`).
  - The v2 linked-list fixture (`template_linked_list_v2_i32.oa`) covers cached length (`len`), result-enum accessors (`front` / `tail` / `pop_front`), and transform helpers (`append`, `reverse`, `take`, `drop`, `at`, `at_or`) in addition to compatibility wrappers.
  - `template_hash_table_i32.oa` currently snapshots a fail-closed invariant-check compile error (`OAC-INV-001`, solver unknown on a large `IntTable__insert_all_buckets` obligation) rather than runtime output.

Snapshots live in:
- `crates/oac/src/snapshots/*.snap`

If behavior intentionally changes, update snapshots deliberately and review diffs for semantic regressions.
Do not commit `.snap.new` files; accept or delete them before finishing.

## Runtime Tooling Dependencies

`oac build` path requires external tools available in environment:
- `qbe`
- C compiler/linker driver (`cc`, `clang`, or target-prefixed `*-gcc`)
- `z3` (required when struct invariant or prove obligations are present)

`oac` links assembly through a fail-closed linker attempt sequence and supports env overrides:
- `OAC_CC` to force a single explicit linker command (no default fallbacks)
- `CC` to prefer a linker command first while still keeping default fallbacks
- `OAC_CC_TARGET` to force `--target=<triple>`
- `OAC_CC_FLAGS` to append extra linker flags
- Linker diagnostics for this stage are reported under `DiagnosticStage::Linker` with stable codes `OAC-LINK-001` (configuration resolution) and `OAC-LINK-002` (all linker attempts failed).

`oac test` has the same backend dependencies as `oac build` (`qbe`, C compiler driver, and `z3` when obligations are present), and additionally executes the produced binary under `target/oac/test/app`.

VS Code extension development under `tools/vscode-ousia` requires:
- `node` and `npm`

Missing tools can cause test/build failures unrelated to Rust logic.

## Debugging Flow for Compiler Regressions

1. Reproduce with a minimal `.oa` fixture in `crates/oac/execution_tests`.
2. Inspect generated intermediates (`tokens.json`, `ast.json`, `ir.json`, `ir.qbe`) and checker artifacts (`target/oac/prove/site_*.qbe`, `site_*.smt2`, `target/oac/struct_invariants/site_*.qbe`, `site_*.smt2`) when applicable. Checker `.qbe` artifacts are rendered from in-memory checker modules (entry checker + reachable user callees).
3. Isolate stage failure: tokenize, parse, resolve, codegen, or external tool invocation.
4. Add/adjust snapshot to encode fixed behavior.
5. Run full test suite (prefer `cargo nextest run`; use `cargo test` fallback only if nextest is unavailable).

## Autonomous Sync Rule

When tests/CI commands/snapshot conventions change, update this file and `AGENTS.md` in the same change.
