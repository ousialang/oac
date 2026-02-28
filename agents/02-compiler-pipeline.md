# Compiler Pipeline

## End-to-End Build Flow

Defined in `crates/oac/src/main.rs` (`compile` function):

1. Read source file.
2. Tokenize with `tokenizer::tokenize`.
3. Parse with `parser::parse`.
4. Resolve flat imports (`import "file.oa"`) from the same directory via `flat_imports` and merge declarations into one AST scope.
5. Resolve/type-check with `ir::resolve`.
6. Lower to QBE with `qbe_backend::compile`.
7. Verify proof obligations through `verification::verify_all_obligations_with_qbe` (single orchestrator over in-memory QBE module):
   - runs reachable `prove(...)` obligations first (`prove` batch)
   - short-circuits on prove failure
   - runs reachable struct-invariant obligations second (`struct_invariants` batch)
8. Run best-effort loop non-termination classification on in-memory QBE `main` (`qbe::Function`) via `qbe_smt::classify_simple_loops`; if a loop is proven non-terminating, fail build before backend toolchain calls.
9. Emit QBE IR to `target/oac/ir.qbe`.
10. Invoke `qbe` to produce assembly (`target/oac/assembly.s`).
11. Invoke C linker/compiler driver attempts to link executable (`target/oac/app`): default `cc` (plus `--target=<triple>` when arch mapping is known), then fallbacks (`clang --target=<triple>`, target-prefixed `*-gcc`, plain `cc`). Respect `OAC_CC` (single explicit command), `CC` (preferred first attempt), `OAC_CC_TARGET`, and `OAC_CC_FLAGS` overrides, and fail compilation if all attempts fail.
12. Map stage failures into shared compiler diagnostics (`crates/oac/src/diagnostics.rs`) and render Ariadne reports for CLI users.

Artifacts emitted during build:
- `target/oac/tokens.json`
- `target/oac/ast.json`
- `target/oac/ir.json`
- `target/oac/ir.qbe`
- `target/oac/prove/site_*.qbe` (generated checker programs, when prove obligations exist)
- `target/oac/prove/site_*.smt2` (when prove obligations exist)
- `target/oac/struct_invariants/site_*.qbe` (generated checker programs, when invariant obligations exist)
- `target/oac/struct_invariants/site_*.smt2` (when invariant obligations exist)
- `target/oac/assembly.s`
- `target/oac/app`

## End-to-End Test Flow

Defined in `crates/oac/src/main.rs` (`run_tests` function):

1. Read source file.
2. Tokenize with `tokenizer::tokenize`.
3. Parse with `parser::parse`.
4. Resolve flat imports via `flat_imports` and execute comptime applies.
5. Lower top-level `test "..." { ... }` declarations via `test_framework::lower_tests_to_program` into generated test functions plus a generated `main`.
6. Resolve/type-check with `ir::resolve`.
7. Lower to QBE, run prove/invariant checks, run non-termination classification, emit QBE/assembly, and link executable (same backend path as `oac build`).
8. Execute `target/oac/test/app` and treat non-zero exit status as test failure.
9. Map failures into shared compiler diagnostics and render Ariadne reports for CLI users.

Artifacts emitted during test runs:
- `target/oac/test/tokens.json`
- `target/oac/test/ast.json`
- `target/oac/test/ir.json`
- `target/oac/test/ir.qbe`
- `target/oac/test/assembly.s`
- `target/oac/test/app`
- prove/invariant debug artifacts under `target/oac/test/prove/` and `target/oac/test/struct_invariants/` when obligations exist

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
- Generic definitions and specializations (`generic Name[T]`, `specialize Alias = Name[ConcreteType]`)
- Trait declarations and concrete impl blocks (`trait Name { ... }`, `impl Name for Type { ... }`)
- Flat import declarations (`import "file.oa"`) for same-directory file inclusion.
- Top-level test declarations (`test "Name" { ... }`).
- Top-level namespaces (`namespace Name { ... }`) support `fun` and `extern fun`; declarations are flattened to mangled internal function keys (`Name__fn`).
- External declarations (`extern fun name(...) -> Type`) are signature-only AST nodes and may appear at top-level or inside namespace blocks.
- Statements: assign, return, expression, `prove(...)`, `assert(...)`, while, if/else, match
- Expressions: literals, vars, calls, postfix calls, unary/binary ops, field access, struct values, match-expr (`Name.fn(args)` parses as postfix call and resolves either as enum constructor or namespace call)
- Char literals are parsed from single quotes (for example `'x'`, `'\n'`) and lowered to a namespaced constructor call (`Char.from_code(<i32>)`).
- Legacy `template` / `instantiate` are hard-cut parser errors with migration hints to `generic` / `specialize`.

Operator precedence is explicitly encoded in parser.

## Semantic Resolution (`ir.rs`)

`resolve(ast)` performs:
- stdlib loading from `crates/oac/src/std/std.oa` (which imports split `std/std_*.oa` modules including `std/std_clib.oa`, `std/std_string.oa`, `std/std_ref.oa`, and `std/std_traits.oa`) using the same flat import resolver, including stdlib invariant declarations.
- trait metadata collection (signature registry, impl coherence checks, and synthesized concrete impl methods)
- generic expansion (`specialize`) into concrete type/function/invariant declarations before normal type-checking/codegen stages
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
- namespace call lowering is also used for generic-specialized helpers (`Alias.fn(args)` resolving to generated `Alias__fn` symbols)
- trait calls are v1 namespaced calls (`Trait.method(value, ...)`) that type-check against trait signatures and resolve to concrete impl function names (`Trait__Type__method`)
- trait coherence is enforced globally: duplicate `impl Trait for Type` is rejected, and missing impls for generic bounds are rejected at specialization time
- built-in `U8`/`FP32`/`FP64` exist alongside integer primitives; unsuffixed decimal literals type-check as `FP32`, and `f64`-suffixed decimal literals type-check as `FP64`
- arithmetic/comparison on numerics requires matching widths/types (`U8/U8`, `I32/I32`, `I64/I64`, `FP32/FP32`, `FP64/FP64`), with no implicit int/float coercions
- `U8` comparisons/codegen are unsigned (`ult/ule/ugt/uge`), and `U8` division lowers to unsigned division (`udiv`)
- stdlib split modules intentionally expose namespaced helper APIs for JSON (`Json.*`) while keeping JSON enums as top-level types
- stdlib split modules also include `AsciiChar`/`AsciiCharResult` helpers in `crates/oac/src/std/std_ascii.oa`, loaded through `crates/oac/src/std/std.oa` like other std modules
- stdlib split modules also include `Char` helper API in `crates/oac/src/std/std_char.oa`, loaded through `crates/oac/src/std/std.oa` like other std modules
- stdlib split modules now also include `Null` as an empty struct in `crates/oac/src/std/std_null.oa` (with `Null.value()` helper), loaded through `crates/oac/src/std/std.oa` like other std modules
- stdlib split modules now also include `Bytes` + `String` in `crates/oac/src/std/std_string.oa`; `String` is std-defined as a tagged enum (`Literal(Bytes)`, `Heap(Bytes)`) and is no longer a resolver primitive
- stdlib split modules now also include generic `Ref[T]` plus read-only specializations/helpers in `crates/oac/src/std/std_ref.oa` (`U8Ref.read`, `I32Ref.read`, `I64Ref.read`, `PtrIntRef.read`, `BoolRef.read`)
- C interop signatures are no longer compiler-injected from JSON; stdlib exposes them via `namespace Clib { extern fun ... }` in `crates/oac/src/std/std_clib.oa` (resolver keys are still mangled as `Clib__*` for namespaced-call lookup)
- resolver builtins include numeric aliases `Int` -> `I32` and `PtrInt` -> `I64`
- resolver builtins also include `Void` for procedure-like extern signatures
- resolver builtins also include pointer-memory helpers `load_u8(addr: PtrInt) -> U8`, `load_i32(addr: PtrInt) -> I32`, `load_i64(addr: PtrInt) -> I64`, `load_bool(addr: PtrInt) -> Bool`, and `store_u8(addr: PtrInt, value: U8) -> Void`
- `extern fun` declarations are signature-only (`extern` cannot be `comptime` and extern functions must not have bodies)
- v2 ABI restriction: `extern fun` signatures cannot use struct parameter or return types; use manual `PtrInt` wrappers at C ABI boundaries when struct-like payloads are needed
- `Void` is restricted in v1: function parameters cannot be `Void`, and only `extern fun` may return `Void`
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
- Includes builtins and interop helpers (for example integer ops, print, string utilities) plus user/std-declared extern call targets.
- Extern calls emit symbol names from signature metadata; namespace externs (for example `Clib.malloc`) therefore call raw declared extern symbols (for example `malloc`) while keeping namespaced lookup keys internal.
- Struct literals allocate zero-initialized storage via `calloc` before field stores, so padding bytes are deterministic for bytewise equality.
- Struct assignment, struct call arguments, and struct returns insert copy barriers (`calloc` + `memcpy`) to enforce by-value byte-copy semantics at language boundaries.
- Struct `==` / `!=` lower through `memcmp(lhs, rhs, size)` and compare the result with zero.
- Handles expression lowering and control-flow generation.
- Trait calls are lowered with static dispatch only (resolved concrete impl symbols), with no runtime dictionaries or vtables.
- Lowers `Void`-return calls only as statement calls; `Void` calls used as expression values are rejected.
- Lowers pointer-memory builtins to QBE loads/stores: `load_u8` -> `loadub`, `load_i32` -> `loadw`, `load_i64` -> `loadl`, `load_bool` -> `loadw` + compare-to-zero, and `store_u8` -> `storeb`.
- Lowers string literals to std-owned `String.Literal(Bytes{ptr,len})` heap objects (compiler allocates `Bytes` payload and tagged-union `String` wrapper).
- String helper builtins (`char_at`, `string_len`, `slice`, `print_str`) operate over std `String`/`Bytes` layout rather than raw C-string pointers.
- Maps `FP32` to QBE `s` (`Type::Single`) and `FP64` to QBE `d` (`Type::Double`), emitting ordered float comparisons (`clt*/cle*/cgt*/cge*`) for `< <= > >=`.
- Maps `U8` to QBE word temporaries with unsigned compare/div lowering for `U8` arithmetic relations.
- Produces snapshots in tests for codegen and runtime behavior.

## SMT Adjacent Paths

- `main.rs` also exposes `riscv-smt` subcommand.
- `riscv_smt.rs` parses RISC-V ELF and emits SMT-LIB constraints for bounded cycle checking.
- `verification.rs` is the shared in-crate orchestrator for proof obligations: it builds shared reachability/function-map context once, runs prove and struct-invariant batches in order, and reuses one generic per-obligation QBE->SMT->solve loop.
- `qbe-smt` is used by both verification batches to encode checker QBE functions into CHC/fixedpoint (Horn) constraints.
- `qbe-smt` also owns CHC solver execution (`solve_chc_script`), so struct invariant verification now shares the same encode+solve backend path.
- `main.rs` also uses `qbe-smt` loop classification on generated in-memory `main` QBE as an early non-termination guard.
- `qbe-smt` is parser-free: it consumes in-memory `qbe::Function` directly. Internals are split by concern across `crates/qbe-smt/src/lib.rs` (API + tests), `crates/qbe-smt/src/encode.rs` (Horn encoding), and `crates/qbe-smt/src/classify.rs` (loop classification).
- `qbe-smt` models a broad integer + memory QBE subset:
  - integer ALU/comparison ops (`add/sub/mul/div/rem`, unsigned variants, bitwise/shift ops)
  - `phi` merging via predecessor-tracking state in CHC (`pred`)
  - `call` modeling for `malloc`, `free`, `calloc`, `realloc`, `memcpy`, `memmove`, `memcmp`, `memset`, `strlen`, `strcmp`, `strcpy`, `strncpy`, `open`, `read`, `write`, `close`, `exit(code)`, and variadic `printf` (for builtin `print` lowering)
  - `load*`/`store*` byte-addressed memory operations
  - `alloc4/alloc8/alloc16` heap-pointer modeling
  - control flow via Horn transition rules (`jnz`, `jmp`, `ret`, halt relation)
- Register state is encoded as an SMT array and threaded through relation arguments.
- Relation state also threads predecessor-block identity so branch-edge semantics for `phi` are explicit.
- Property surface is fixed: query whether halt with `exit == 1` is reachable (`(query bad)`).
- Unsupported constructs are fail-closed hard errors (no havoc fallback path).
- For modeled CLib memory operations, encoding uses bounded precise expansion (`limit = 16`) plus sound fallback branches (for example, unconstrained `mem_next` when bounds are exceeded).
- Floating-point SMT reasoning is intentionally unsupported today; FP32/FP64 values/compares in obligations are rejected fail-closed.
- Encoding/validation is reachable-code-aware: only blocks reachable from function entry are flattened into Horn rules, so unreachable unsupported code does not block proving.
- Main-argument-aware assumption remains available: when enabled and main has `argc`, encoding asserts `argc >= 0`.
- Struct-invariant SAT failures include a compact checker CFG witness (block path + branch directions).
- Loop classification is intentionally conservative: currently proves only a narrow canonical while-loop shape where the guard is initially true on entry and the body preserves the guard variable (`x' = x`), otherwise result is unknown and build proceeds.

## LSP Path

- `main.rs` also exposes `test` subcommand (`oac test <file.oa>`) for lowered test-declaration execution.
- `main.rs` also exposes `lsp` subcommand (`oac lsp`).
- `lsp.rs` runs JSON-RPC over stdio, handles `initialize`/`shutdown`/`exit`, text document open/change/save/close notifications, and requests for definition/hover/document symbols/references/completion.
- Symbol indexing includes `extern fun` declarations in document symbols.
- Completion keywords include `generic`, `specialize`, `trait`, and `impl` (legacy `template`/`instantiate` are removed).
- Diagnostics are produced from tokenizer/parser/import-resolution/type-resolution through the shared `diagnostics` module and then converted to LSP ranges (`textDocument/publishDiagnostics`), using span labels when available and a `0:0` fallback range otherwise.

## Implementation Guidance

When changing syntax/semantics:
1. Update tokenizer/parser/IR in lock-step.
2. If imports/build pipeline are affected, update `flat_imports.rs` and CLI integration in `main.rs`.
3. Add or update execution fixtures under `crates/oac/execution_tests`.
4. Refresh snapshots.
5. Update `agents/03-language-semantics.md` and this file.
