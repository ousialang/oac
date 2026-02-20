# Testing and CI

## CI Contract

Defined in `.github/workflows/ci.yml`:
- `cargo check --all-targets --all-features`
- `cargo test --all-targets --all-features`
- `z3` installation (required for struct invariant verification obligations)

Any change should keep both green.

Note: CI does not currently build the VS Code extension under `tools/vscode-ousia`; validate it locally when touching editor integration files.

## Local Commands

From repository root:

```bash
cargo check --all-targets --all-features
cargo test --all-targets --all-features
```

Targeted crate:

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

## Snapshot-Based Testing

Key tests:
- `crates/oac/src/tokenizer.rs` test loads `crates/oac/tokenizer_tests/*`.
- `crates/oac/src/parser.rs` tests assert template bracket syntax parsing, legacy `()` rejection, struct-invariant declaration syntax (`invariant ... for (...)`, with optional identifier, including inside templates), and optional trailing commas for struct declarations/literals.
- `crates/oac/src/parser.rs` tests also cover namespace declaration parsing and namespaced call syntax (`TypeName.helper(...)`).
- `crates/oac/src/flat_imports.rs` tests assert flat import resolution: merge behavior, same-directory path constraints, and cycle detection.
- `crates/oac/src/ir.rs` includes a regression test that stdlib split files are loaded through `std.oa` imports.
- `crates/oac/src/ir.rs` also validates accepted `main` signatures (`main()` and `main(argc, argv)`).
- `crates/oac/src/ir.rs` also validates namespace call resolution/type-checking by lowering to mangled function names (`TypeName__helper`).
- `crates/qbe-smt/src/lib.rs` tests (built from in-memory `qbe::Function` fixtures) cover CHC/fixedpoint encoding shape (`HORN`, relation declarations, `(query bad)`), branch/loop rule generation, integer+memory modeling, and strict rejection of unsupported operations.
- `crates/qbe-smt/src/lib.rs` also validates `exit(code)` call modeling as halting transitions and rejects malformed exit calls (for example missing exit code argument).
- `crates/qbe-smt/src/lib.rs` additionally covers `phi` encoding via predecessor-state guards and rejection of malformed/unknown `phi` labels.
- `crates/qbe-smt/src/lib.rs` also verifies reachable-only encoding behavior (unsupported instructions inside unreachable blocks are ignored).
- `crates/qbe-smt/src/lib.rs` is also the shared CHC solver entrypoint (`solve_chc_script` and `solve_chc_script_with_diagnostics`) used by struct invariant verification.
- `crates/qbe-smt/src/lib.rs` also tests loop classification (`classify_simple_loops`) for proven non-termination patterns (identity updates, including `call $sub(..., 0)`) vs unknown/progress loops.
- `crates/oac/src/lsp.rs` tests cover diagnostics, definition/references lookup (including across flat imports), hover (including namespaced function calls), completion, document symbols, and file-URI handling.
- `crates/oac/src/struct_invariants.rs` tests cover invariant discovery/validation for declaration-based invariants, legacy function-name compatibility, template concrete-name support, obligation-site scoping, deterministic call-site ordinals, recursion rejection, and QBE-native checker synthesis/CHC encoding behavior (including fail-closed unsupported external calls).
- `crates/oac/src/prove.rs` verifies compile-time `prove(...)` obligations over QBE-native checker synthesis and CHC solving (including no-op behavior when no prove sites exist).
- SAT invariant failures emitted by `struct_invariants.rs` include a compact control-flow witness summary (`cfg_path` + branch steps) and attempt to include concrete `program_input` data (`argc` witness for `main(argc, argv)` sites).
- `crates/oac/src/main.rs` tests cover build-time rejection when `main` contains a loop proven non-terminating by QBE loop classification.
- `crates/oac/src/qbe_backend.rs` test loads `crates/oac/execution_tests/*`, compiles fixtures, and snapshots either compiler errors or program stdout (non-zero exit codes are allowed; only spawn/timeout/signal/UTF-8 failures are runtime errors).
- `crates/oac/src/qbe_backend.rs` also has a unit test that asserts QBE emission for namespaced calls contains mangled function call symbols.
- Execution fixtures now include dedicated prove/assert coverage:
  - `prove_pass.oa`
  - `prove_fail.oa`
  - `prove_statement_only.oa`
  - `assert_pass.oa`
  - `assert_fail.oa`
- Execution fixtures also include namespace call coverage:
  - `namespace_basic.oa`

Snapshots live in:
- `crates/oac/src/snapshots/*.snap`

If behavior intentionally changes, update snapshots deliberately and review diffs for semantic regressions.

## Runtime Tooling Dependencies

`oac build` path requires external tools available in environment:
- `qbe`
- `zig` (used as `zig cc`)
- `z3` (required when struct invariant or prove obligations are present)

VS Code extension development under `tools/vscode-ousia` requires:
- `node` and `npm`

Missing tools can cause test/build failures unrelated to Rust logic.

## Debugging Flow for Compiler Regressions

1. Reproduce with a minimal `.oa` fixture in `crates/oac/execution_tests`.
2. Inspect generated intermediates (`tokens.json`, `ast.json`, `ir.json`, `ir.qbe`) and checker artifacts (`target/oac/prove/site_*.qbe`, `site_*.smt2`, `target/oac/struct_invariants/site_*.qbe`, `site_*.smt2`) when applicable. Checker `.qbe` artifacts are rendered from in-memory `qbe::Function` obligations.
3. Isolate stage failure: tokenize, parse, resolve, codegen, or external tool invocation.
4. Add/adjust snapshot to encode fixed behavior.
5. Run full test suite.

## Autonomous Sync Rule

When tests/CI commands/snapshot conventions change, update this file and `AGENTS.md` in the same change.
