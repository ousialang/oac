# Compiler Pipeline

## End-to-End Build Flow

Defined in `crates/oac/src/main.rs` (`compile` function):

1. Read source file.
2. Tokenize with `tokenizer::tokenize`.
3. Parse with `parser::parse`.
4. Resolve flat imports (`import "file.oa"`) from the same directory via `flat_imports` and merge declarations into one AST scope.
5. Resolve/type-check with `ir::resolve`.
6. Lower to QBE with `qbe_backend::compile`.
7. Verify `prove(...)` obligations with `prove::verify_prove_obligations_with_qbe` (SMT-based, fail-closed, consumes in-memory QBE module).
8. Verify struct invariants with `struct_invariants::verify_struct_invariants_with_qbe` (SMT-based, fail-closed, consumes in-memory QBE module).
9. Run best-effort loop non-termination classification on in-memory QBE `main` (`qbe::Function`) via `qbe_smt::classify_simple_loops`; if a loop is proven non-terminating, fail build before backend toolchain calls.
10. Emit QBE IR to `target/oac/ir.qbe`.
11. Invoke `qbe` to produce assembly (`target/oac/assembly.s`).
12. Invoke `zig cc` to link executable (`target/oac/app`).

Artifacts emitted during build:
- `target/oac/tokens.json`
- `target/oac/ast.json`
- `target/oac/ir.json`
- `target/oac/ir.qbe`
- `target/oac/prove/site_*.qbe` (generated checker programs, when prove obligations exist)
- `target/oac/prove/site_*.smt2` (when prove obligations exist)
- `target/oac/struct_invariants/site_*.qbe` (generated checker programs, when obligations exist)
- `target/oac/struct_invariants/site_*.smt2` (when invariant obligations exist)
- `target/oac/assembly.s`
- `target/oac/app`

## Front-End Details

### Tokenizer (`tokenizer.rs`)

- Eager tokenization model (whole file first).
- Token kinds include newline, parenthesis, integer number, decimal float literal (`Float`), char literal (`Char`), string, word, symbol, comment.
- Supports escaped string chars (`\\`, `\"`, `\n`, `\t`, `\r`).
- Word tokenization follows `[A-Za-z_][A-Za-z0-9_]*` and is EOF-safe (for example a file ending in `identifier` or `_` no longer panics during lexing).
- Produces `SyntaxError` with position metadata.

### Parser (`parser.rs`)

Core AST includes:
- Type defs: `Struct`, `Enum`
- Templates and template instantiations (`template Name[T]`, `instantiate Alias = Name[ConcreteType]`)
- Flat import declarations (`import "file.oa"`) for same-directory file inclusion.
- Top-level namespaces (`namespace Name { fun ... }`) flattened into mangled function symbols (`Name__fn`).
- Statements: assign, return, expression, `prove(...)`, `assert(...)`, while, if/else, match
- Expressions: literals, vars, calls, postfix calls, unary/binary ops, field access, struct values, match-expr (`Name.fn(args)` parses as postfix call and resolves either as enum constructor or namespace call)
- Char literals are parsed from single quotes (for example `'x'`, `'\n'`) and lowered to a namespaced constructor call (`Char.from_code(<i32>)`).

Operator precedence is explicitly encoded in parser.

## Semantic Resolution (`ir.rs`)

`resolve(ast)` performs:
- stdlib loading from `crates/oac/src/std.oa` (which imports split `std_*.oa` modules) using the same flat import resolver, including stdlib invariant declarations.
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
- `prove(...)` and `assert(...)` conditions must be `Bool`
- `prove(...)` and `assert(...)` are statement-only; expression usage is rejected
- user-defined functions named `prove` or `assert` are rejected (reserved builtin names)
- namespace function calls (`Name.fn(args)`) are type-checked as regular function calls using mangled names (`Name__fn`) when such a function exists; otherwise postfix call semantics continue to serve enum payload constructors
- namespace call lowering is also used for template-instantiated helpers (`Alias.fn(args)` resolving to generated `Alias__fn` symbols)
- built-in `FP32`/`FP64` exist alongside integer primitives; unsuffixed decimal literals type-check as `FP32`, and `f64`-suffixed decimal literals type-check as `FP64`
- arithmetic/comparison on numerics requires matching widths/types (`I32/I32`, `I64/I64`, `FP32/FP32`, `FP64/FP64`), with no implicit int/float coercions
- stdlib split modules intentionally expose namespaced helper APIs for JSON/newstring (`Json.*`, `NewString.print(...)`) while keeping JSON enums as top-level types
- stdlib split modules also include `AsciiChar`/`AsciiCharResult` helpers in `std_ascii.oa`, loaded through `std.oa` like other std modules
- stdlib split modules also include `Char` helper API in `std_char.oa`, loaded through `std.oa` like other std modules
- stdlib split modules now also include `Null` as an empty struct in `std_null.oa` (with `Null.value()` helper), loaded through `std.oa` like other std modules
- resolver builtins include numeric aliases `Int` -> `I32` and `PtrInt` -> `I64`
- declaration-based stdlib invariants (for example `AsciiChar` range checks over wrapped `Char.code`) are synthesized and registered during resolve like user-declared invariants
- consistent return types inside a function
- `main` must be either `fun main() -> I32`, `fun main(argc: I32, argv: I64) -> I32`, or `fun main(argc: I32, argv: PtrInt) -> I32`
- optional struct invariants are declared as `invariant ... for (v: TypeName) { ... }` (optionally named with an identifier); the compiler synthesizes `__struct__<TypeName>__invariant` and also validates legacy explicit invariant functions using that naming/signature pattern
- `prove(...)` sites reachable from `main` are verified by checker QBE synthesis: the site condition is marked in QBE, checker returns `1` when the proof condition is false at the site, and proving asks reachability of exit code `1` (`unsat` = proven, `sat` = compile failure)
- reachable user-call return sites for struct-typed values are verified with generated checker QBE programs where return code `1` means violation; proving asks reachability of exit code `1` (`unsat` = success)
- checker generation is QBE-native: site instrumentation happens on compiled caller QBE, then reachable user calls are inlined into a single checker function before CHC encoding
- recursion cycles on the reachable user-call graph are rejected fail-closed during struct invariant verification
- recursion cycles on the reachable user-call graph are also rejected fail-closed when prove obligations exist

## Backend (`qbe_backend.rs`)

- Generates QBE module/functions/data.
- Includes builtins and interop helpers (for example integer ops, print, string utilities).
- Handles expression lowering and control-flow generation.
- Maps `FP32` to QBE `s` (`Type::Single`) and `FP64` to QBE `d` (`Type::Double`), emitting ordered float comparisons (`clt*/cle*/cgt*/cge*`) for `< <= > >=`.
- Produces snapshots in tests for codegen and runtime behavior.

## SMT Adjacent Paths

- `main.rs` also exposes `riscv-smt` subcommand.
- `riscv_smt.rs` parses RISC-V ELF and emits SMT-LIB constraints for bounded cycle checking.
- `qbe-smt` is used by prove verification and struct invariant verification to encode checker QBE functions into CHC/fixedpoint (Horn) constraints.
- `qbe-smt` also owns CHC solver execution (`solve_chc_script`), so struct invariant verification now shares the same encode+solve backend path.
- `main.rs` also uses `qbe-smt` loop classification on generated in-memory `main` QBE as an early non-termination guard.
- `qbe-smt` is parser-free: it consumes in-memory `qbe::Function` directly. Internals are split by concern across `crates/qbe-smt/src/lib.rs` (API + tests), `crates/qbe-smt/src/encode.rs` (Horn encoding), and `crates/qbe-smt/src/classify.rs` (loop classification).
- `qbe-smt` models a broad integer + memory QBE subset:
  - integer ALU/comparison ops (`add/sub/mul/div/rem`, unsigned variants, bitwise/shift ops)
  - `phi` merging via predecessor-tracking state in CHC (`pred`)
  - `call` with explicit support for `malloc` heap effects and `exit(code)` halting transitions
  - `load*`/`store*` byte-addressed memory operations
  - `alloc4/alloc8/alloc16` heap-pointer modeling
  - control flow via Horn transition rules (`jnz`, `jmp`, `ret`, halt relation)
- Register state is encoded as an SMT array and threaded through relation arguments.
- Relation state also threads predecessor-block identity so branch-edge semantics for `phi` are explicit.
- Property surface is fixed: query whether halt with `exit == 1` is reachable (`(query bad)`).
- Unsupported constructs are fail-closed hard errors (no havoc fallback path).
- Floating-point SMT reasoning is intentionally unsupported today; FP32/FP64 values/compares in obligations are rejected fail-closed.
- Encoding/validation is reachable-code-aware: only blocks reachable from function entry are flattened into Horn rules, so unreachable unsupported code does not block proving.
- Main-argument-aware assumption remains available: when enabled and main has `argc`, encoding asserts `argc >= 0`.
- Struct-invariant SAT failures include a compact checker CFG witness (block path + branch directions); for `main(argc, argv)` obligations, `oac` also extracts a concrete `argc` witness via additional CHC range queries.
- Loop classification is intentionally conservative: currently proves only a narrow canonical while-loop shape where the guard is initially true on entry and the body preserves the guard variable (`x' = x`), otherwise result is unknown and build proceeds.

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
