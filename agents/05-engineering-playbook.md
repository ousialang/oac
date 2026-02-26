# Engineering Playbook for LLM Contributors

## Mission

Act like a compiler engineer, not a text editor:
- preserve language invariants
- protect existing behavior with tests
- make changes stage-aware (tokenizer -> parser -> IR -> backend)
- treat backward compatibility as secondary while Ousia is pre-release

## Working Model

1. Identify affected compiler stage(s).
2. Create or update a fixture that demonstrates expected behavior.
3. Implement the minimal coherent change across all impacted stages.
4. Run tests and inspect snapshots.
5. Update `agents/*` docs when behavior/workflow changed.

## Practical Rules

- Prefer small semantic deltas over broad rewrites.
- Prefer coherent, cleaner APIs over compatibility shims when the two conflict.
- Do not change parser shape without corresponding IR/type-check updates.
- Do not change IR assumptions without auditing backend lowering paths.
- Preserve or explicitly migrate snapshot expectations.
- Keep error messages actionable and stable where possible.

## Pre-Release Compatibility Posture

- Ousia is pre-release; breaking API and language-surface changes are acceptable when they simplify or correct the design.
- Do not keep obsolete interfaces solely for compatibility. Remove or reshape them when needed.
- Ship breaks as complete migrations: update parser/IR/backend behavior, fixtures, snapshots, and `agents/*` docs together.
- Make breakage explicit in change descriptions so downstream users can adjust quickly.

## Change Patterns

### New syntax/operator
- Extend tokenizer symbols/lexing if required.
- Extend parser AST and precedence handling.
- Extend type inference/checks in IR.
- Extend QBE lowering and tests.

### New type or enum behavior
- Update built-in/type-resolution logic.
- Validate match exhaustiveness and payload rules.
- Add positive and negative fixtures.
- For integer-width additions (for example `U8`), audit signedness-sensitive ops in codegen (`cmp`, `div/rem`) and keep resolver/codegen rules aligned.

### Backend/runtime behavior change
- Inspect generated QBE text and runtime output snapshots.
- Check interop assumptions with std-declared `extern fun` bindings (`std_clib.oa`) and helper functions.

### Interop/bindings behavior change
- Prefer stdlib declarations (`extern fun`) over compiler hardcoded signature tables.
- Audit `Void` constraints end-to-end (signature validation, type-checking, and backend lowering in statement position).

## Pre-Commit Checklist

- `cargo check --all-targets --all-features`
- `cargo nextest run --all-targets --all-features` (preferred when `cargo-nextest` is available)
- `cargo test --all-targets --all-features` (fallback when `cargo-nextest` is unavailable)
- Review snapshot diffs for unintended behavior changes.
- Update docs in `agents/` and root `AGENTS.md` if any context changed.

## Autonomous Sync Rule (Mandatory)

If you notice any drift between these docs and the repository, fix the docs immediately as part of your current task, without waiting for a separate request.
