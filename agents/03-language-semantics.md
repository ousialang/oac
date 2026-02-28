# Language Semantics (Implemented Today)

This describes behavior implemented in current compiler code, not aspirational docs.

Pre-release policy: this compiler and stdlib are intentionally allowed to evolve with breaking API changes when needed for correctness or language design clarity.

## Built-In Types

From `crates/oac/src/builtins.rs`:
- `U8`
- `I32`
- `I64`
- `FP32`
- `FP64`
- `Bool`
- `Void`
- `Semantic` (internal-only marker for comptime semantic pseudo-types, not user-addressable)

Resolver-defined numeric aliases in `crates/oac/src/ir.rs`:
- `Int` aliases to `I32`
- `PtrInt` aliases to `I64`

## Core Language Constructs

Observed in parser/IR implementation:
- Function definitions with typed params and return type.
- Variable assignment.
- `return` statements.
- Arithmetic/logical/comparison operators.
- Decimal float literals with explicit width selection: unsuffixed `1.25` is `FP32`, and `1.25f64` is `FP64`.
- Unary `!` for boolean negation.
- `if` / `else` and `while`.
- Struct definitions and struct literal construction.
- Field access.
- Enum definitions with optional payloads.
- Pattern matching on enums (`match`) as statement and expression.
- Generic definitions and specialization aliases with square-bracket type arguments (`generic Name[T]`, `specialize Alias = Name[ConcreteType]`).
- Trait declarations and concrete impl blocks (`trait Name { fun method(v: Self, ...) -> ... }`, `impl Name for Type { ... }`).
- Generic inline bounds (`generic Map[K: Hash + Eq, V] { ... }`).
- Flat same-directory imports with no namespace: `import "helper.oa"` merges imported declarations into the same global scope.
- Top-level namespaces for helper/interop declarations: `namespace TypeName { fun helper(...) -> ... { ... } }` and `namespace TypeName { extern fun symbol(...) -> ... }`, callable as `TypeName.helper(...)`.
- External function declarations are signature-only (`extern fun name(args...) -> Type`, no body) and may appear at top-level or inside namespace blocks.
- Char literals with single quotes are supported (`'x'`, escape forms like `'\n'`) and lower to std `Char` values.
- Identifier lexing uses `[A-Za-z_][A-Za-z0-9_]*` and allows EOF-terminated identifiers (no trailing delimiter required).
- Struct declarations and struct literals accept an optional trailing comma after the last field.
- Statement-only builtins with call syntax: `prove(cond)` and `assert(cond)`.
- Runtime pointer-memory builtins: `load_u8(addr: PtrInt) -> U8`, `load_i32(addr: PtrInt) -> I32`, `load_i64(addr: PtrInt) -> I64`, `load_bool(addr: PtrInt) -> Bool`, `store_u8(addr: PtrInt, value: U8) -> Void`, `store_i32(addr: PtrInt, value: I32) -> Void`, `store_i64(addr: PtrInt, value: I64) -> Void`, and `store_bool(addr: PtrInt, value: Bool) -> Void`.
- Top-level test declarations: `test "Name" { ... }`.
- Legacy syntax `template` / `instantiate` is hard-cut and rejected with migration diagnostics.

## Semantic Rules You Must Preserve

- Match subject must resolve to an enum.
- Match must be exhaustive over enum variants.
- Duplicate match arms are invalid.
- Variant payload binders are required only for payload variants.
- `if` and `while` conditions must type-check to `Bool`.
- `prove(...)` and `assert(...)` conditions must type-check to `Bool`.
- `prove(...)` and `assert(...)` cannot be used as expressions.
- Function return paths must not mix incompatible return types.
- `main` must use one of these signatures: `fun main() -> I32`, `fun main(argc: I32, argv: I64) -> I32`, or `fun main(argc: I32, argv: PtrInt) -> I32`.
- Assignments bind variable type to expression type.
- Struct literals are zero-initialized before field stores (`calloc`) so bytewise struct equality has deterministic padding bytes.
- Struct values use by-value byte-copy semantics at assignment/call/return boundaries (implemented with clone barriers in codegen, not pointer-identity semantics).
- Struct `==` / `!=` are universal bytewise comparisons (`memcmp` over struct size), including pointer-containing structs.
- Numeric binary ops are strict and same-type only: `U8/U8`, `I32/I32`, `I64/I64`, `FP32/FP32`, `FP64/FP64` (no implicit int/float coercions).
- `U8` relational operators (`<`, `>`, `<=`, `>=`) use unsigned comparisons in codegen.
- `U8` division lowers to unsigned integer division in codegen.
- Function names `prove` and `assert` are reserved and cannot be user-defined.
- Namespace bodies accept `fun` and `extern fun` declarations; `comptime` declarations inside namespace blocks are rejected.
- `extern fun` declarations cannot be marked `comptime` and must not define a body.
- In v2 ABI, `extern fun` declarations cannot use struct parameter types or struct return types; use `PtrInt` wrappers for manual ABI bridging.
- `Void` cannot be used as a function parameter type.
- In v1, only `extern fun` may return `Void`.
- Assignment statements cannot bind variables to `Void`-typed expressions.
- `Void`-return calls are statement-only (cannot be used as expression values).
- Namespace calls are syntactic sugar for internal function names using `Namespace__function` lowering, while preserving existing enum constructor call syntax `Enum.Variant(...)`.
- Namespace call lowering also applies to generic-specialized helpers when matching mangled symbols exist (`Alias.helper(...)` -> `Alias__helper`).
- Traits are static-only in v1: method calls use `Trait.method(value, ...)` and are resolved to concrete impl symbols (`Trait__Type__method`) before backend lowering.
- Trait method signatures must take `Self` as the first parameter type in v1.
- Impl coherence is global: exactly one `impl Trait for Type` is allowed in a program.
- Impl method sets/signatures must match trait declarations exactly (arity, parameter types after `Self` substitution, return type); missing/extra methods are compile errors.
- `impl` methods cannot be `extern` or `comptime` in v1.
- Generic specialization enforces trait bounds fail-closed: missing `impl Trait for ConcreteType` required by a bound is a compile error.
- Generic expansion is ahead-of-type-checking and ahead-of-codegen: backend/proving/invariant passes still operate on concrete non-generic IR/function symbols.
- Imports are file-local-only and flat: import paths must be string literals naming `.oa` files in the same directory.
- The built-in stdlib is composed through flat imports from `crates/oac/src/std/std.oa` into split sibling files under `crates/oac/src/std/` (including `std_clib.oa` extern bindings and `std_traits.oa` trait/impl declarations), then merged into one global scope before user type-checking (including stdlib invariant declarations).
- The split stdlib includes generic `Option[T]` / `Result[T,E]` in `crates/oac/src/std/std_option_result.oa` with namespaced constructors/predicates/unwrapping helpers.
- The split stdlib includes generic `Ref[T]` and `Mut[T]` (in `crates/oac/src/std/std_ref.oa`) for pointer-wrapper value semantics (`from_ptr`, `ptr`, `is_null`, `add_bytes`), with typed read-only dereference helpers (`U8Ref.read`, `I32Ref.read`, `I64Ref.read`, `PtrIntRef.read`, `BoolRef.read`) and typed mutable helpers (`U8Mut.*`, `I32Mut.*`, `I64Mut.*`, `PtrIntMut.*`, `BoolMut.*`) that use builtin stores.
- Stdlib `HashTable` is now a bounded generic (`HashTable[K: Hash + Eq, V]`) with separate-chaining semantics while routing key hashing/equality through `Hash.hash(k)` and `Eq.equals(a, b)`.
- `String` is std-defined (in `crates/oac/src/std/std_string.oa`) as `enum String { Literal(Bytes), Heap(Bytes) }` with `Bytes { ptr: PtrInt, len: I32 }`; it is no longer a compiler primitive, and `Bytes` has an invariant requiring `len >= 0`.
- `String.make_bytes` normalizes `Bytes.len` fail-closed (`len < 0` clamps to `0`) and is used by `String.from_literal_parts` / `String.from_heap_parts`; `String.bytes` performs equivalent inline normalization through `String.normalize_len` before constructing `Bytes` so payload invariants remain provable at call sites.
- `String` namespaced helpers include structural accessors (`bytes`, `ptr`, `len`) and convenience operations (`is_empty`, `equals`, `starts_with`, `ends_with`, `char_at_or`, `slice_clamped`).
- C interop signatures are std-defined in `crates/oac/src/std/std_clib.oa` under `namespace Clib { extern fun ... }`; namespaced lookup still uses internal mangled keys (`Clib__*`), while codegen emits declared extern symbol names for linking.
- The split stdlib now uses namespaced helper APIs for JSON (`Json.*`) while JSON result enums remain top-level types (`ParseErr`, `ParseResult`, `JsonKind`).
- The split stdlib `LinkedList[T]` template (in `crates/oac/src/std/std_collections.oa`) is persistent/value-based and now includes richer namespaced helpers (`empty`, `singleton`, `cons`, `push_front`, `is_empty`, `len`, `length`, `front`, `tail`, `pop_front`, `append`, `reverse`, `take`, `drop`, `at`, `at_or`) with result enums (`FrontResult`, `TailResult`, `PopFrontResult`); `length`, `head_or`, and `tail_or` are retained as compatibility wrappers.
- `LinkedList[T]::Node` has a declaration-based struct invariant requiring positive cached length metadata (`len >= 1`); `LinkedList.make_node` normalizes negative lengths to `0` and saturates at `2147483646` before adding one so node construction preserves the invariant under fail-closed proving.
- The split stdlib also defines `AsciiChar` and `AsciiCharResult`; construction/parsing is explicit and fail-closed through `AsciiChar.from_code(...)` and `AsciiChar.from_string_at(...)` (returning `AsciiCharResult.OutOfRange` on invalid inputs). `AsciiChar` wraps `Char` and has an invariant requiring `0 <= Char.code(ch) <= 127`.
- The split stdlib also defines `Char` as an `I32` wrapper (`struct Char { code: I32 }`) with helpers `Char.from_code(...)`, `Char.code(...)`, and `Char.equals(...)`.
- The split stdlib now also defines `Null` as an empty struct (`struct Null {}`), with a namespaced constructor helper `Null.value() -> Null`.
- The split stdlib now also defines `HashTable[K: Hash + Eq, V]` as a dynamically resizing separate-chaining map in `crates/oac/src/std/std_collections.oa`; public helpers are `HashTable.new`, `HashTable.with_capacity`, `HashTable.set`, `HashTable.get`, `HashTable.remove`, `HashTable.len`, `HashTable.capacity`, `HashTable.contains_key`, and `HashTable.clear`.
- `HashTable.set` returns `SetResult { table: HashTable, inserted_new: Bool }` and `HashTable.remove` returns `RemoveResult { table: HashTable, removed: Lookup }`.
- `HashTable[K: Hash + Eq, V]` currently has no declaration-based struct invariant; the former `coherent_state` declaration was removed after fail-closed solver-unknown obligations on resize/rehash call sites.
- Struct invariants are optional per struct type and support both single and grouped declarations: `invariant [identifier]? "Human label" for (v: TypeName) { ... }` and `invariant for (v: TypeName) { [identifier]? "Human label" { ... } ... }`.
- Invariant clauses synthesize internal functions named `__struct__<TypeName>__invariant__<key>` with signature `fun ...(v: <TypeName>) -> Bool` (`<key>` is identifier-based or deterministic anonymous ordinal like `anon_0`); legacy explicit functions named `__struct__<TypeName>__invariant(v: TypeName) -> Bool` are still accepted for compatibility.
- Malformed legacy invariant functions are compile errors.
- Build-time verification checks struct invariants per `(call-site, invariant)` at return sites of user-defined function calls reachable from `main` (excluding invariant function bodies).
- Build-time verification also checks `prove(...)` obligations at reachable statement sites from `main` by synthesizing checker QBE functions that return `1` on proof-condition violation.
- Verification synthesizes each site checker from compiled QBE by instrumenting the target call with an invariant check and returning `1` on violation / `0` on success, then asks if exit code `1` is reachable (`unsat` means invariant proven, `sat` means compile failure).
- `prove(...)` checker synthesis instruments QBE marker assignments (`.oac_prove_site_*`) and rewrites checker return to `1` when the proved condition is false at the targeted site.
- Checker construction is interprocedural: the checker artifact includes entry + reachable user callees, and CHC encoding models user calls through function summary relations (`*_ret` / `*_abort`) instead of checker-time inlining.
- Checker entry preconditions now include argument-type invariants in both verification pipelines: for each checker function argument whose semantic type has struct invariants, encoding adds one invariant relation precondition per invariant (`*_ret` relation + non-zero return).
- These argument-invariant preconditions are assumptions only: the checker’s entry memory/heap state is not replaced with the invariant-call output memory/heap.
- Shared recursion-cycle analysis lives in `verification_cycles.rs` and uses SCCs over the combined verification graph with deterministic cycle witness reconstruction for fail-closed diagnostics.
- Runtime `assert(cond)` lowers to a branch that exits the process with code `242` and halts on failure.
- String literals lower to std `String.Literal` values by allocating `Bytes` + tagged union wrapper in codegen; runtime string helpers (`char_at`, `string_len`, `slice`, `print_str`) read `Bytes.ptr`/`Bytes.len` from that layout.
- Runtime `i32_to_i64` helper lowering uses signed extension (`extsw`) so values above `255` are not truncated in pointer/length conversion paths.
- Solver assumptions include `argc >= 0` when `main` uses the `(argc: I32, argv: I64)` or `(argc: I32, argv: PtrInt)` form.
- `oac test <file.oa>` is fail-fast: each `test` block is lowered to a generated zero-arg `I32` function, and a generated `main` executes tests in declaration order. A failing runtime `assert` exits immediately with code `242`.
- `oac test` requires at least one `test` declaration and rejects source files that already define `main` (because `main` is synthesized by the test runner).
- `oac build` does not lower or execute `test` declarations; test lowering is isolated to the `oac test` command path.
- Call-only recursion cycles are allowed for struct invariant and prove verification; cycles containing argument-invariant precondition edges are rejected fail-closed on the combined verification graph.
- Unsupported proving constructs at QBE level fail closed through `qbe-smt` (hard `Unsupported` encoding errors).
- Struct-invariant proof obligations are encoded by `qbe-smt` as CHC/fixedpoint Horn rules over QBE transitions and queried via reachability of a `bad` relation (`exit == 1` at halt).
- Prove obligations use the same CHC encoding/query shape (`exit == 1` reachability over synthesized checker QBE).
- Struct-invariant proof obligations are solved via the shared `qbe-smt` CHC backend runner (Z3 invocation is centralized there).
- `qbe-smt` is strict fail-closed: unsupported QBE operations are hard errors (no conservative havoc fallback).
- `qbe-smt` currently rejects floating-point obligations fail-closed (including FP32/FP64 literals/comparisons) during prove/struct-invariant checking.
- `qbe-smt` models `call $exit(code)` as a halting transition with `exit` state set from `code`.
- `qbe-smt` also models known CLib calls (`malloc`, `free`, `calloc`, `realloc`, `memcpy`, `memmove`, `memcmp`, `memset`, `strlen`, `strcmp`, `strcpy`, `strncpy`, `open`, `read`, `write`, `close`) plus variadic `printf` for builtin `print` inlined paths.
- CLib byte-memory call models use bounded precise expansion (`limit = 16`) with sound fallback branches; unknown extern call targets remain fail-closed unsupported errors.
- String-call precision now includes bounded `strlen` NUL scanning and bounded `strcmp` first-event scanning (difference/shared NUL) with tri-state results (`-1/0/1`), each with fail-open fallback to constrained unknown results when bounds are exceeded.
- `strcpy` effects are modeled as bounded copy-until-NUL (terminator included); if no NUL appears within the inline bound, encoding falls back to unconstrained memory.
- Modeled syscall return values are now constrained: `open` returns `-1` or non-negative; `close` returns `0` or `-1`; `read`/`write` return `-1` or a non-negative value not exceeding `count`.
- `qbe-smt` models `phi` by threading predecessor-block identity through CHC state and guarding predecessor-dependent merges.
- `qbe-smt` is parser-free: proving consumes direct in-memory QBE IR (`qbe::Module` via `qbe_module_to_smt` / `qbe_module_to_smt_with_assumptions`), not re-parsed QBE text.
- `qbe-smt` flattens only entry-reachable blocks; unreachable unsupported instructions do not affect encoding.
- When a struct-invariant obligation is SAT, diagnostics include a control-flow witness summary over the synthesized checker (`cfg_path` and branch decisions).
- `oac build` does not emit a general-purpose QBE SMT sidecar; SMT artifacts are produced only for struct invariant obligations under `target/oac/struct_invariants/`.
- `oac build` emits prove artifacts under `target/oac/prove/` when prove obligations exist.
- `oac build` runs a conservative non-termination classifier over QBE `main` loops and rejects builds only when non-termination is proven (current proof shape: canonical while-loop with initially true guard and identity body update on guard variable, including simple `sub(x, 0)` forms). Unproven loops are treated as unknown and allowed.

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
