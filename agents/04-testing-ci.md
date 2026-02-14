# Testing and CI

## CI Contract

Defined in `.github/workflows/ci.yml`:
- `cargo check --all-targets --all-features`
- `cargo test --all-targets --all-features`

Any change should keep both green.

## Local Commands

From repository root:

```bash
cargo check --all-targets --all-features
cargo test --all-targets --all-features
```

Targeted crate:

```bash
cargo test -p oac
```

## Snapshot-Based Testing

Key tests:
- `crates/oac/src/tokenizer.rs` test loads `crates/oac/tokenizer_tests/*`.
- `crates/oac/src/parser.rs` tests assert template bracket syntax parsing and legacy `()` rejection.
- `crates/oac/src/qbe_backend.rs` test loads `crates/oac/execution_tests/*`, compiles fixtures, and snapshots either compiler errors or program output.

Snapshots live in:
- `crates/oac/src/snapshots/*.snap`

If behavior intentionally changes, update snapshots deliberately and review diffs for semantic regressions.

## Runtime Tooling Dependencies

`oac build` path requires external tools available in environment:
- `qbe`
- `zig` (used as `zig cc`)

Missing tools can cause test/build failures unrelated to Rust logic.

## Debugging Flow for Compiler Regressions

1. Reproduce with a minimal `.oa` fixture in `crates/oac/execution_tests`.
2. Inspect generated intermediates (`tokens.json`, `ast.json`, `ir.json`, `ir.qbe`).
3. Isolate stage failure: tokenize, parse, resolve, codegen, or external tool invocation.
4. Add/adjust snapshot to encode fixed behavior.
5. Run full test suite.

## Autonomous Sync Rule

When tests/CI commands/snapshot conventions change, update this file and `AGENTS.md` in the same change.
