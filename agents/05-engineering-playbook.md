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
- When editing stdlib `.oa` files or execution fixtures, prefer receiver method syntax for eligible namespace/specialized helpers; keep static calls only when parameter 0 is not the receiver or when the fixture is explicitly covering namespace-vs-method syntax.
- Runtime backend behavior and verification backend behavior are separate contracts: runtime codegen may use `qbe` or `llvm`, but prove/invariant/loop checks must remain QBE-based unless explicitly redesigned.
- Keep LLVM runtime lowering as direct `ResolvedProgram` lowering; do not reintroduce production IR->QBE->LLVM translation coupling.
- Preserve or explicitly migrate snapshot expectations.
- Keep error messages actionable and stable where possible.
- Route user-visible compiler errors through `crates/oac/src/diagnostics.rs` so CLI/LSP/snapshot behavior stays consistent (Ariadne plain output for deterministic tests).
- Treat diagnostic quality as a product contract: avoid internal debug dumps in user-facing messages, avoid duplicated Ariadne prefixes (`Error: error[...]`), and keep linker-stage diagnostics on `OAC-LINK-*`.
- For proving/invariant performance-sensitive changes, run `oac bench-prove` and inspect delta/regression output against `crates/oac/bench/prove_baseline.json`.
- For unknown-mitigation/verification-solver changes, run `oac bench-prove --strict-outcome-gate` and require zero forbidden transitions (baseline `sat`/`unsat` must not drift).
- When touching proof-cache behavior, validate both trusted build/test reuse and live benchmark behavior: `build` / `test` default to `--proof-cache trust`, while `bench-prove` defaults to `--proof-cache strict` with read-only cache policy.
- When touching integer arithmetic or stdlib helpers that use it, audit both runtime lowering and proof-stage obligations: source-level `U8`/`I32`/`I64`/`PtrInt` `+/-/*//` sites now create compile-time proof obligations, so helper arithmetic often needs explicit local guards/asserts to stay provable.

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
- For generic/trait changes, keep expansion-first architecture intact: specialize to concrete declarations before normal type-check/codegen, and preserve static dispatch (no runtime trait dictionaries/vtables).

### New type or enum behavior
- Update built-in/type-resolution logic.
- Validate match exhaustiveness and payload rules.
- Add positive and negative fixtures.
- For integer-width additions (for example `U8`), audit signedness-sensitive ops in codegen (`cmp`, `div/rem`) and keep resolver/codegen rules aligned.
- For comptime numeric changes, keep evaluator behavior deterministic: do not rely on Rust panics for overflow or divide-by-zero, and add direct unit regressions in `comptime.rs`.

### Backend/runtime behavior change
- Inspect generated QBE text and runtime output snapshots.
- For runtime backend changes, inspect generated backend artifacts (`ir.qbe`/`assembly.s` or `ir.ll`/`object.o`) and keep linker path fail-closed.
- Preserve runtime parity semantics across backends (for example struct copy barriers, struct bytewise equality, and LLVM runtime-noop lowering for `prove(...)`).
- If integer-safety behavior changes, inspect emitted `.oac_integer_site_*` markers in QBE and the generated checker artifacts under `target/oac/integer_safety/`; regressions often come from unexpected marker reachability or from checker CFG branches that were not pruned tightly enough.
- When touching checker synthesis or CHC schema shape, audit all three site-checker pipelines together (`prove`, integer-safety, struct invariants): target-reachability pruning, entry-function assert-fail rewriting, and per-function `pred` omission are shared proof-cost optimizations and should stay behaviorally aligned across those entrypoints.
- Check interop assumptions with std `Clib.*` bindings in `crates/oac/src/std/std_clib.oa` (`namespace`-scoped `extern fun` declarations that resolve to `Clib__*` internal keys while preserving declared link symbols) and helper functions.

### Interop/bindings behavior change
- Prefer stdlib declarations (`extern fun`) over compiler hardcoded signature tables.
- Audit `Void` constraints end-to-end (signature validation, type-checking, and backend lowering in statement position).

## Pre-Commit Checklist

- One-time setup per clone/worktree: `git config core.hooksPath .githooks`
- `cargo check --all-targets --all-features`
- `cargo nextest run --all-targets --all-features` (preferred when `cargo-nextest` is available)
- `cargo test --all-targets --all-features` (fallback when `cargo-nextest` is unavailable)
- `cargo run -p oac -- bench-prove --suite quick --iterations 1` for quick proving-regression signal when touching verification/codegen paths.
- `cargo run -p oac -- bench-prove --suite full --iterations 1 --strict-outcome-gate` when touching solver retry/unknown handling or SMT helper generation.
- `cargo run -p oac -- build <fixture.oa> --proof-cache trust` twice (or targeted cache unit tests) when changing proof-summary cache keying, trust/strict policy, or verification-session orchestration.
- Review snapshot diffs for unintended behavior changes.
- Ensure snapshot hygiene gates pass (`*.snap.new` absent and execution snapshots aligned with fixtures).
- Update docs in `agents/` and root `AGENTS.md` if any context changed.

Local hook policy in this repository:
- `pre-commit` auto-formats staged Rust files with nightly `rustfmt` (`rustfmt.toml`).
- `pre-push` is an intentional no-op placeholder (no automatic test execution on push).
- Emergency bypass is explicit via `--no-verify`.

## Autonomous Sync Rule (Mandatory)

If you notice any drift between these docs and the repository, fix the docs immediately as part of your current task, without waiting for a separate request.
