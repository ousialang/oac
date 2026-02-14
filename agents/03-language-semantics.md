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
- Template definitions and template instantiation aliases.

## Semantic Rules You Must Preserve

- Match subject must resolve to an enum.
- Match must be exhaustive over enum variants.
- Duplicate match arms are invalid.
- Variant payload binders are required only for payload variants.
- `if` and `while` conditions must type-check to `Bool`.
- Function return paths must not mix incompatible return types.
- Assignments bind variable type to expression type.

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
