# Compiler Pipeline

## End-to-End Build Flow

Defined in `crates/oac/src/main.rs` (`compile` function):

1. Read source file.
2. Tokenize with `tokenizer::tokenize`.
3. Parse with `parser::parse`.
4. Resolve flat imports (`import "file.oa"`) from the same directory via `flat_imports` and merge declarations into one AST scope.
5. Resolve/type-check with `ir::resolve`.
6. Verify struct invariants with `struct_invariants::verify_struct_invariants` (SMT-based, fail-closed).
7. Lower to QBE with `qbe_backend::compile`.
8. Emit QBE IR to `target/oac/ir.qbe`.
9. Invoke `qbe` to produce assembly (`target/oac/assembly.s`).
10. Invoke `zig cc` to link executable (`target/oac/app`).

Artifacts emitted during build:
- `target/oac/tokens.json`
- `target/oac/ast.json`
- `target/oac/ir.json`
- `target/oac/ir.qbe`
- `target/oac/struct_invariants/site_*.qbe` (generated checker programs, when obligations exist)
- `target/oac/struct_invariants/site_*.smt2` (when invariant obligations exist)
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
- Templates and template instantiations (`template Name[T]`, `instantiate Alias = Name[ConcreteType]`)
- Flat import declarations (`import "file.oa"`) for same-directory file inclusion.
- Statements: assign, return, expression, while, if/else, match
- Expressions: literals, vars, calls, postfix calls, unary/binary ops, field access, struct values, match-expr

Operator precedence is explicitly encoded in parser.

## Semantic Resolution (`ir.rs`)

`resolve(ast)` performs:
- stdlib loading from `crates/oac/src/std.oa` (which imports split `std_*.oa` modules) using the same flat import resolver.
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
- `main` must be either `fun main() -> I32` or `fun main(argc: I32, argv: I64) -> I32`
- optional struct invariants (`__struct__<TypeName>__invariant`) must have exact signature `fun ...(v: TypeName) -> Bool` when present
- reachable user-call return sites for struct-typed values are verified with generated checker QBE programs where return code `1` means violation; proving asks reachability of exit code `1` (`unsat` = success)
- verifier `while` handling is conservative: loop-body assigned variables are havocked at loop exit; loops containing invariant-obligation call sites or loop-body returns are rejected (fail-closed)

## Backend (`qbe_backend.rs`)

- Generates QBE module/functions/data.
- Includes builtins and interop helpers (for example integer ops, print, string utilities).
- Handles expression lowering and control-flow generation.
- Produces snapshots in tests for codegen and runtime behavior.

## SMT Adjacent Paths

- `main.rs` also exposes `riscv-smt` subcommand.
- `riscv_smt.rs` parses RISC-V ELF and emits SMT-LIB constraints for bounded cycle checking.
- `qbe-smt` is used by struct invariant verification to encode checker QBE programs into CHC/fixedpoint (Horn) constraints.
- `qbe-smt` models a broad integer + memory QBE subset:
  - integer ALU/comparison ops (`add/sub/mul/div/rem`, unsigned variants, bitwise/shift ops)
  - `call` with explicit support for `malloc` heap effects
  - `load*`/`store*` byte-addressed memory operations
  - `alloc4/alloc8/alloc16` heap-pointer modeling
  - control flow via Horn transition rules (`jnz`, `jmp`, `ret`, halt relation)
- Register state is encoded as an SMT array and threaded through relation arguments.
- Property surface is fixed: query whether halt with `exit == 1` is reachable (`(query bad)`).
- Unsupported constructs are fail-closed hard errors (no havoc fallback path).
- Main-argument-aware assumption remains available: when enabled and main has `argc`, encoding asserts `argc >= 0`.

## LSP Path

- `main.rs` also exposes `lsp` subcommand (`oac lsp`).
- `lsp.rs` runs JSON-RPC over stdio, handles `initialize`/`shutdown`/`exit`, text document open/change/save/close notifications, and requests for definition/hover/document symbols/references/completion.
- Diagnostics are produced from tokenizer/parser/import-resolution/type-resolution, and published via `textDocument/publishDiagnostics`.

## Implementation Guidance

When changing syntax/semantics:
1. Update tokenizer/parser/IR in lock-step.
2. If imports/build pipeline are affected, update `flat_imports.rs` and CLI integration in `main.rs`.
3. Add or update execution fixtures under `crates/oac/execution_tests`.
4. Refresh snapshots.
5. Update `agents/03-language-semantics.md` and this file.
