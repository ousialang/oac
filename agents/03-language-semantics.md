# Language Semantics (Implemented Today)

This describes behavior implemented in current compiler code, not aspirational docs.

## Built-In Types

From `crates/oac/src/builtins.rs`:
- `I32`
- `I64`
- `String`
- `Bool`

## Core Language Constructs

Observed in parser/IR implementation:
- Function definitions with typed params and return type.
- Variable assignment.
- `return` statements.
- Arithmetic/logical/comparison operators.
- Unary `!` for boolean negation.
- `if` / `else` and `while`.
- Struct definitions and struct literal construction.
- Field access.
- Enum definitions with optional payloads.
- Pattern matching on enums (`match`) as statement and expression.
- Template definitions and template instantiation aliases with square-bracket type arguments (`template Name[T]`, `instantiate Alias = Name[ConcreteType]`).
- Flat same-directory imports with no namespace: `import "helper.oa"` merges imported declarations into the same global scope.

## Semantic Rules You Must Preserve

- Match subject must resolve to an enum.
- Match must be exhaustive over enum variants.
- Duplicate match arms are invalid.
- Variant payload binders are required only for payload variants.
- `if` and `while` conditions must type-check to `Bool`.
- Function return paths must not mix incompatible return types.
- `main` must use one of two signatures: `fun main() -> I32` or `fun main(argc: I32, argv: I64) -> I32`.
- Assignments bind variable type to expression type.
- Imports are file-local-only and flat: import paths must be string literals naming `.oa` files in the same directory.
- The built-in stdlib is composed through flat imports from `std.oa` into split sibling files, then merged into one global scope before user type-checking.
- Struct invariants are optional per struct type and identified by function name `__struct__<TypeName>__invariant`.
- If an invariant function exists, it must have exact signature `fun __struct__<TypeName>__invariant(v: <TypeName>) -> Bool`; malformed signatures are compile errors.
- Build-time verification checks struct invariants at return sites of user-defined function calls reachable from `main` (excluding invariant function bodies).
- Verification compiles each site formula into a checker-style QBE program that returns `1` on violation and `0` otherwise, then asks if exit code `1` is reachable; `unsat` means invariant proven at the site, `sat` means compile failure.
- Checker lowering keeps symbolic `I32` inputs at `w` width and sign-extends internally for integer arithmetic, preventing accidental quantification over unconstrained 64-bit argument domains.
- Solver assumptions include `argc >= 0` when `main` uses the `(argc: I32, argv: I64)` form.
- `while` is supported with conservative summarization: body-assigned variables are havocked at loop exit.
- `while` still fails closed if the loop region contains invariant-obligation call sites or loop-body `return` statements.
- Unsupported verifier constructs (for example `match`, postfix calls, recursion cycles in analyzed paths, or missing return on a reachable path) fail closed.
- Struct-invariant proof obligations are encoded by `qbe-smt` as CHC/fixedpoint Horn rules over QBE transitions and queried via reachability of a `bad` relation (`exit == 1` at halt).
- `qbe-smt` is strict fail-closed: unsupported QBE operations are hard errors (no conservative havoc fallback).
- `oac build` does not emit a general-purpose QBE SMT sidecar; SMT artifacts are produced only for struct invariant obligations under `target/oac/struct_invariants/`.

## Notes on Specs vs Reality

Some files in `docs/specs/` describe historical or broader language concepts (`package`, `import`, argument forms) that do not map 1:1 with the current compiler implementation in `crates/oac/src`.

Before implementing spec-driven changes, verify parser + IR behavior and extend tests first.

## Safe Evolution Pattern

1. Encode behavior in an execution fixture (`crates/oac/execution_tests/*.oa`).
2. Make parser/IR/backend changes.
3. Validate snapshot output.
4. Update this file and `agents/02-compiler-pipeline.md`.

## Autonomous Sync Rule

Whenever semantics change, update this file in the same commit as code and snapshots.
