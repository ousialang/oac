# Compiler Pipeline

## End-to-End Build Flow

Defined in `crates/oac/src/main.rs` (`compile` function):

1. Read source file.
2. Tokenize with `tokenizer::tokenize`.
3. Parse with `parser::parse`.
4. Resolve/type-check with `ir::resolve`.
5. Lower to QBE with `qbe_backend::compile`.
6. Emit QBE IR to `target/oac/ir.qbe`.
7. Optionally emit QBE SMT sidecar `target/oac/ir.smt2`.
8. Invoke `qbe` to produce assembly (`target/oac/assembly.s`).
9. Invoke `zig cc` to link executable (`target/oac/app`).

Artifacts emitted during build:
- `target/oac/tokens.json`
- `target/oac/ast.json`
- `target/oac/ir.json`
- `target/oac/ir.qbe`
- `target/oac/ir.smt2` (best-effort)
- `target/oac/assembly.s`
- `target/oac/app`

## Front-End Details

### Tokenizer (`tokenizer.rs`)

- Eager tokenization model (whole file first).
- Token kinds include newline, parenthesis, number, string, word, symbol, comment.
- Supports escaped string chars (`\\`, `\"`, `\n`, `\t`, `\r`).
- Produces `SyntaxError` with position metadata.

### Parser (`parser.rs`)

Core AST includes:
- Type defs: `Struct`, `Enum`
- Templates and template instantiations
- Statements: assign, return, expression, while, if/else, match
- Expressions: literals, vars, calls, postfix calls, unary/binary ops, field access, struct values, match-expr

Operator precedence is explicitly encoded in parser.

## Semantic Resolution (`ir.rs`)

`resolve(ast)` performs:
- stdlib injection via `include_str!("std.oa")`
- type definition graph creation
- function signature collection
- function body semantic checks

Important enforced invariants include:
- match subject must be enum type
- match arms must use correct enum type
- no duplicate match variants
- payload binder rules must match variant payload presence
- match exhaustiveness required
- conditions in `if` / `while` must be `Bool`
- consistent return types inside a function

## Backend (`qbe_backend.rs`)

- Generates QBE module/functions/data.
- Includes builtins and interop helpers (for example integer ops, print, string utilities).
- Handles expression lowering and control-flow generation.
- Produces snapshots in tests for codegen and runtime behavior.

## SMT Adjacent Paths

- `main.rs` also exposes `riscv-smt` subcommand.
- `riscv_smt.rs` parses RISC-V ELF and emits SMT-LIB constraints for bounded cycle checking.
- Build path also tries to emit QBE->SMT sidecar using `qbe-smt` crate.

## Implementation Guidance

When changing syntax/semantics:
1. Update tokenizer/parser/IR in lock-step.
2. Add or update execution fixtures under `crates/oac/execution_tests`.
3. Refresh snapshots.
4. Update `agents/03-language-semantics.md` and this file.
