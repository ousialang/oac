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
- Call-only receiver method sugar is supported for namespace helpers: `value.helper(args...)` resolves through the receiver's concrete type and rewrites to `TypeName.helper(value, args...)`.
- External function declarations are signature-only (`extern fun name(args...) -> Type`, no body) and may appear at top-level or inside namespace blocks.
- Char literals with single quotes are supported (`'x'`, escape forms like `'\n'`) and lower to std `Char` values.
- Identifier lexing uses `[A-Za-z_][A-Za-z0-9_]*` and allows EOF-terminated identifiers (no trailing delimiter required).
- Struct declarations and struct literals accept an optional trailing comma after the last field.
- Leading newlines before opening braces in braced declaration/block headers are treated as whitespace (`enum Name` newline `{`, `trait Name` newline `{`, `if cond` newline `{`, and similar forms remain valid).
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
- Ownership is move-only by default: reading a non-`Copy` binding moves it and invalidates that binding until reassigned.
- For types with a concrete `Copy` impl, read sites implicitly clone by lowering to static `Copy.copy(...)` calls; codegen passes either the value directly (legacy by-value impl signatures) or a synthesized temporary `Ref` wrapper (ref-style impl signatures).
- Deterministic destruction uses `Drop`: resolver inserts `Drop.drop(...)` calls before overwriting initialized bindings and at scope exits (reverse declaration order); moved/uninitialized bindings are not dropped.
- Struct `==` / `!=` are universal bytewise comparisons (`memcmp` over struct size), including pointer-containing structs.
- Numeric binary ops are strict and same-type only: `U8/U8`, `I32/I32`, `I64/I64`, `FP32/FP32`, `FP64/FP64` (no implicit int/float coercions).
- Fixed-width integer arithmetic uses two's-complement wrapping semantics (`I32`/`I64` overflow is not trapped); verification reasons over the same bitvector behavior as runtime rather than mathematical integers.
- Source-level integer `+`, `-`, `*`, `/` over `U8`, `I32`, `I64`, and `PtrInt` are fail-closed at compile time: every reachable runtime site and every site reachable from struct/model-invariant roots must be proven overflow/underflow-safe during `check proofs`, or compilation stops with `OAC-PROVE-001`.
- Integer-safety predicates are fixed in v1: `U8` requires `add/mul <= 255`, `sub >= 0`, `div rhs != 0`; `I32`/`I64`/`PtrInt` use signed monotonicity checks for `add/sub`, guarded `result / rhs == lhs` for `mul`, and `rhs != 0 && !(lhs == MIN && rhs == -1)` for `div`.
- `U8` relational operators (`<`, `>`, `<=`, `>=`) use unsigned comparisons in codegen.
- `U8` division lowers to unsigned integer division in codegen.
- Function names `prove` and `assert` are reserved and cannot be user-defined.
- Namespace bodies accept `fun` and `extern fun` declarations; `comptime` declarations inside namespace blocks are rejected.
- `extern fun` declarations cannot be marked `comptime` and must not define a body.
- In v2 ABI, `extern fun` declarations cannot use struct parameter types or struct return types; use `PtrInt` wrappers for manual ABI bridging.
- `Void` cannot be used as a function parameter type.
- Non-extern functions may return `Void`.
- Assignment statements cannot bind variables to `Void`-typed expressions.
- `Void`-return calls are statement-only (cannot be used as expression values).
- Namespace calls are syntactic sugar for internal function names using `Namespace__function` lowering, while preserving existing enum constructor call syntax `Enum.Variant(...)`.
- Receiver method calls are call-only sugar: `value.helper(args...)` lowers through the receiver's resolved type namespace and prepends the receiver as argument 0; bare-identifier syntax `TypeName.helper(...)` remains the existing static namespace/trait/enum surface.
- Plain field access rules are unchanged: non-variable field access is still rejected, so `(expr).field` is invalid even though `(expr).helper(...)` is accepted.
- Namespace call lowering also applies to generic-specialized helpers when matching mangled symbols exist (`Alias.helper(...)` -> `Alias__helper`).
- Project source style now prefers receiver method syntax in stdlib/runtime fixtures when that lowering is available from parameter 0 ownership (`value.helper(...)` over `TypeName.helper(value, ...)`), while keeping static syntax for constructors, non-receiver-first helpers, trait calls, and explicit namespace-vs-method equivalence coverage.
- Traits are static-only in v1: method calls use `Trait.method(value, ...)` and are resolved to concrete impl symbols (`Trait__Type__method`) before backend lowering.
- Trait method signatures must take `Self` as the first parameter type in v1.
- Special lifecycle-trait shapes are enforced exactly:
  - `trait Copy { fun copy(v: Ref[Self]) -> Self }`
  - `trait Drop { fun drop(v: Self) -> Void }`
- Impl coherence is global: exactly one `impl Trait for Type` is allowed in a program.
- Impl method sets/signatures must match trait declarations exactly (arity, parameter types after `Self` substitution, return type); missing/extra methods are compile errors.
- `impl` methods cannot be `extern` or `comptime` in v1.
- Generic specialization enforces trait bounds fail-closed: missing `impl Trait for ConcreteType` required by a bound is a compile error.
- Generic bodies may declare local specialization aliases (`specialize LocalAlias = Name[TypeArgs...]`), and generic expansion resolves those aliases recursively into concrete type/function/invariant declarations using the parent specialization substitutions.
- Generic expansion is ahead-of-type-checking and ahead-of-codegen: backend/proving/invariant passes still operate on concrete non-generic IR/function symbols.
- Imports are file-local-only and flat: import paths must be string literals naming `.oa` files in the same directory.
- The built-in stdlib is composed through flat imports from `crates/oac/src/std/std.oa` into split sibling files under `crates/oac/src/std/` (including `std_clib.oa` extern bindings and `std_traits.oa` trait/impl declarations), then merged into one global scope before user type-checking (including stdlib invariant declarations).
- `std_traits.oa` defines `Copy` and `Drop` alongside `Hash`/`Eq`; scalar types (`Bool`, `U8`, `I32`, `I64`, `FP32`, `FP64`, `Char`, `AsciiChar`) ship concrete `Copy` impls in std.
- The split stdlib includes generic `Option[T]` / `Result[T,E]` in `crates/oac/src/std/std_option_result.oa` with namespaced constructors/predicates/unwrapping helpers.
- The split stdlib includes generic `Ref[T]` and `Mut[T]` (in `crates/oac/src/std/std_ref.oa`) for pointer-wrapper value semantics (`from_ptr`, `ptr`, `is_null`, `add_bytes`), with typed read-only dereference helpers (`U8Ref.read`, `I32Ref.read`, `I64Ref.read`, `PtrIntRef.read`, `BoolRef.read`) and typed mutable helpers (`U8Mut.*`, `I32Mut.*`, `I64Mut.*`, `PtrIntMut.*`, `BoolMut.*`) that use builtin stores.
- Stdlib `HashTable` is now a bounded generic (`HashTable[K: Hash + Eq, V]`) with separate-chaining semantics while routing key hashing/equality through `Hash.hash(k)` and `Eq.equals(a, b)`.
- The split stdlib now also defines generic `HashSet[K: Hash + Eq]` (in `crates/oac/src/std/std_set.oa`) as a persistent separate-chaining set with set algebra (`union`, `intersection`, `difference`) and explicit mutation result payloads (`InsertResult`, `RemoveResult`).
- The split stdlib now also defines generic `Vec[T]` (in `crates/oac/src/std/std_vec.oa`) as a persistent vector-style container with `push`/`pop`/`get`/`set`/`reserve`/`clear` APIs and explicit result payloads (`PopResult`, `Lookup`, `SetResult`).
- `String` is std-defined (in `crates/oac/src/std/std_string.oa`) as `enum String { Literal(Bytes), Heap(Bytes) }` with `Bytes { ptr: PtrInt, len: I32 }`; it is no longer a compiler primitive, and `Bytes` has an invariant requiring `len >= 0`.
- `String.make_bytes` normalizes `Bytes.len` fail-closed (`len < 0` clamps to `0`) and is used by `String.from_literal_parts` / `String.from_heap_parts`; `String.bytes` performs equivalent inline normalization through `String.normalize_len` before constructing `Bytes` so payload invariants remain provable at call sites.
- `String` namespaced helpers include structural accessors (`bytes`, `ptr`, `len`) and convenience operations (`is_empty`, `equals`, `starts_with`, `ends_with`, `char_at_or`, `slice_clamped`).
- Stdlib now includes a small set of global model invariants (2+ args) chosen for solver stability:
  - `Char.from_code_roundtrip`: `Char.code(Char.from_code(x)) == x` for multiple inputs
  - `Char.equals_matches_code_equality`: `Char.equals(Char.from_code(x), Char.from_code(y)) == (x == y)`
  - `String.make_bytes_normalizes_len_and_keeps_ptr`: `String.make_bytes(ptr, len)` preserves `ptr` and sets `len` to `String.normalize_len(len)`
  - `String.normalize_len_is_non_negative`: `String.normalize_len(x) >= 0`
  - `Option.none must agree with presence predicates`: `Option.is_none(Option.none()) && !Option.is_some(Option.none())`
  - `Ref`/`Mut` pointer wrapper laws: `ptr(from_ptr(p)) == p`
- C interop signatures are std-defined in `crates/oac/src/std/std_clib.oa` under `namespace Clib { extern fun ... }`; namespaced lookup still uses internal mangled keys (`Clib__*`), while codegen emits declared extern symbol names for linking.
- The split stdlib now uses namespaced helper APIs for JSON (`Json.*`) and exposes both scanner-style APIs (`Json.parse_json_document_result`, `Json.json_kind`) and value-tree APIs (`Json.parse_json_document_value_result` returning `JsonValue` trees with `JsonMembers`/`JsonValues`).
- JSON booleans in `JsonValue` are modeled as `JsonValue.Bool(Bool)` (not separate `True`/`False` variants), and `Json.json_kind` classifies both `true` and `false` as `JsonKind.Bool`.
- JSON result and value carrier types are top-level stdlib declarations (`ParseErr`, `ParseResult`, `JsonKind`, `JsonValue`, `JsonValueParseResult`, `JsonDocumentValueResult`, `JsonValueLookup`, `JsonStringLookup`).
- JSON string scanning now accepts `\uXXXX` escapes (exactly four hex digits) and remains fail-closed for malformed escape sequences.
- The split stdlib now also uses namespaced file-descriptor IO helpers (`Io.*`) from `crates/oac/src/std/std_io.oa` with explicit result enums (`IoError`, `IoReadResult`, `IoWriteResult`) layered over `Clib.open/read/write/close`.
- The split stdlib `LinkedList[T]` template (in `crates/oac/src/std/std_collections.oa`) is persistent/value-based and now includes richer namespaced helpers (`empty`, `singleton`, `cons`, `push_front`, `is_empty`, `len`, `length`, `front`, `tail`, `pop_front`, `append`, `reverse`, `take`, `drop`, `at`, `at_or`) where `front`/`tail`/`at`/`pop_front` use local `Option` aliases (`FrontOption`, `TailOption`, `PopFrontOption`); `length`, `head_or`, and `tail_or` are retained as compatibility wrappers.
- `LinkedList[T]::Node` has a declaration-based struct invariant requiring positive cached length metadata (`len >= 1`); `LinkedList.make_node` normalizes negative lengths to `0` and saturates at `2147483646` before adding one so node construction preserves the invariant under fail-closed proving.
- The split stdlib also defines `AsciiChar` and `AsciiCharResult`; construction/parsing is explicit and fail-closed through `AsciiChar.from_code(...)` and `AsciiChar.from_string_at(...)` (returning `AsciiCharResult.OutOfRange` on invalid inputs). `AsciiChar` wraps `Char` and has an invariant requiring `0 <= Char.code(ch) <= 127`.
- The split stdlib also defines `Char` as an `I32` wrapper (`struct Char { code: I32 }`) with helpers `Char.from_code(...)`, `Char.code(...)`, and `Char.equals(...)`.
- The split stdlib now also defines `Null` as an empty struct (`struct Null {}`), with a namespaced constructor helper `Null.value() -> Null`.
- The split stdlib now also defines `HashTable[K: Hash + Eq, V]` as a dynamically resizing separate-chaining map in `crates/oac/src/std/std_collections.oa`; public helpers are `HashTable.new`, `HashTable.with_capacity`, `HashTable.set`, `HashTable.get`, `HashTable.remove`, `HashTable.len`, `HashTable.capacity`, `HashTable.contains_key`, and `HashTable.clear`.
- `HashTable.set` returns `SetResult { table: HashTable, inserted_new: Bool }` and `HashTable.remove` returns `RemoveResult { table: HashTable, removed: Lookup }`.
- `HashTable[K: Hash + Eq, V]` currently has no declaration-based struct invariant; the former `coherent_state` declaration was removed after fail-closed solver-unknown obligations on resize/rehash call sites.
- Hash table metadata now has explicit runtime assertion guards in `HashTable.assert_metadata(...)` (`bucket_count >= 1`, `len >= 0`, `resize_threshold >= 1`, `len <= resize_threshold`) and this helper is applied on constructor/mutation return paths (`with_capacity`, `set_no_resize`, `rehash`, `maybe_resize_before_insert` passthrough, `remove`, `clear`).
- Invariant declarations accept one or more parameters in `for (...)` for both single and grouped syntax. Empty parameter lists are rejected.
- Arity-sensitive invariant semantics:
  - unary invariants (`for (v: TypeName)`) are struct invariants;
  - multi-argument invariants (`for (a: ..., b: ..., ...)`) are model invariants.
- Unary invariant clauses synthesize internal functions named `__struct__<TypeName>__invariant__<key>` with signature `fun ...(v: <TypeName>) -> Bool` (`<key>` is identifier-based or deterministic anonymous ordinal like `anon_0`); legacy explicit functions named `__struct__<TypeName>__invariant(v: TypeName) -> Bool` are still accepted for compatibility.
- Multi-argument model-invariant clauses synthesize internal functions named `__model__invariant__<key>` and are tracked globally (identifier uniqueness is global across model invariants).
- Malformed legacy invariant functions are compile errors.
- Build-time verification checks struct invariants per `(call-site, invariant)` at return sites of user-defined function calls reachable from `main` (excluding invariant function bodies).
- Build-time verification also checks `prove(...)` obligations at reachable statement sites from `main` by synthesizing checker QBE functions that return `1` on proof-condition violation.
- Build-time verification also checks source-level integer arithmetic at reachable marker sites: ordinary roots are `main` plus reachable helper callees, and additional roots are every struct-invariant function plus every model-invariant function.
- Build-time verification checks model invariants globally (independent of `main` reachability): one obligation per declaration.
- Verification synthesizes each site checker from compiled QBE by instrumenting the target call with an invariant check and returning `1` on violation / `0` on success, then asks if exit code `1` is reachable (`unsat` means invariant proven, `sat` means compile failure).
- `prove(...)` checker synthesis instruments QBE marker assignments (`.oac_prove_site_*`), prunes the cloned caller CFG to blocks that can still reach the targeted site before checker-module closure, and rewrites checker return to `1` when the proved condition is false at the targeted site.
- Integer-safety checker synthesis instruments QBE marker assignments emitted by codegen (`.oac_integer_site_<type>__<op>__<id>__{lhs,rhs,out}`), clones the marker’s caller as checker `main`, prunes CFG branches that cannot reach the marker, and rewrites checker return to `1` when the operator’s safety predicate is false at that site.
- Model-invariant checker synthesis rewrites invariant returns to checker `bad` (`ret == 0`) and queries reachability of `exit == 1`.
- Model invariants are resolve-validated as a strict pure subset over transitive user calls: reject `prove(...)`, `assert(...)`, extern calls, pointer load/store builtins, and side-effect builtins (`print`, `print_str`).
- Checker construction is interprocedural: the checker artifact includes entry + reachable user callees, and CHC encoding models user calls through function summary relations (`*_ret` / `*_abort`) instead of checker-time inlining.
- Checker reachable-callee discovery now traverses only entry-reachable CFG blocks per QBE function (and stops scanning a block after terminators), so dead instrumentation blocks do not contribute spurious call targets/argument-invariant assumptions.
- Struct-invariant checker synthesis also prunes the cloned caller CFG to blocks that can still reach the targeted call site before checker-module closure, so post-site branches do not contribute extra callees to the obligation.
- Before CHC encoding, checker entry functions rewrite only the compiler-generated assert-fail pattern (`call $exit(w 242)` immediately followed by `hlt`) into safe `ret 0`; helper callees keep terminal assert exits so callers do not continue past impossible states, and other `exit(...)` paths remain aborts.
- Checker entry preconditions now include argument-type invariants in prove/struct-invariant/model-invariant pipelines: for each checker function argument whose semantic type has struct invariants, encoding adds one invariant relation precondition per invariant (`*_ret` relation + non-zero return).
- Checker entry preconditions also include integer range assumptions where available: semantic `U8` parameters become `[0,255]` assumptions in `qbe-smt`, so checker modules reason about byte ranges without requiring separate user-written invariants.
- These argument-invariant preconditions are assumptions only: the checker’s entry memory/heap state is not replaced with the invariant-call output memory/heap.
- Shared recursion-cycle analysis lives in `verification_cycles.rs` and uses SCCs over the combined verification graph with deterministic cycle witness reconstruction for fail-closed diagnostics.
- Runtime `assert(cond)` lowers to a branch that exits the process with code `242` and halts on failure.
- Comptime `I32` arithmetic is checked instead of panicking-through-Rust: `+/-/*` overflow and `/` divide-by-zero or `MIN / -1` produce deterministic comptime diagnostics.
- String literals lower to std `String.Literal` values by allocating `Bytes` + tagged union wrapper in codegen; runtime string helpers (`char_at`, `string_len`, `slice`, `print_str`) read `Bytes.ptr`/`Bytes.len` from that layout.
- Runtime `i32_to_i64` helper lowering uses signed extension (`extsw`) so values above `255` are not truncated in pointer/length conversion paths.
- Solver assumptions include `argc >= 0` when `main` uses the `(argc: I32, argv: I64)` or `(argc: I32, argv: PtrInt)` form.
- `oac test <file.oa>` is fail-fast: each `test` block is lowered to a generated zero-arg `I32` function, and a generated `main` executes tests in declaration order. A failing runtime `assert` exits immediately with code `242`.
- `oac test` requires at least one `test` declaration and rejects source files that already define `main` (because `main` is synthesized by the test runner).
- `oac build` does not lower or execute `test` declarations; test lowering is isolated to the `oac test` command path.
- Call-only recursion cycles are allowed for struct-invariant/prove/model-invariant verification; cycles containing argument-invariant precondition edges are rejected fail-closed on the combined verification graph.
- Unsupported proving constructs at QBE level fail closed through `qbe-smt` (hard `Unsupported` encoding errors).
- Struct-invariant proof obligations are encoded by `qbe-smt` as CHC/fixedpoint Horn rules over QBE transitions and queried via reachability of a `bad` relation (`exit == 1` at halt).
- Prove and model-invariant obligations use the same CHC encoding/query shape (`exit == 1` reachability over synthesized checker QBE).
- Prove/struct-invariant/model-invariant obligations are solved via the shared `qbe-smt` CHC backend runner (Z3 invocation is centralized there).
- Verification outcome classes are `{sat, unsat, unknown}` per obligation; `sat`/`unsat` interpretation is unchanged (`sat` fail, `unsat` pass), and `unknown` remains fail-closed.
- Outcome-migration policy for unknown mitigation is strict: only baseline `unknown` obligations may change outcome; baseline `sat`/`unsat` obligations must remain unchanged.
- Default solver retry behavior is `10s` then `30s`; candidate profile may add a third attempt for large obligations still `unknown`, controlled by `OAC_Z3_LARGE_OBLIGATION_BYTES` and `OAC_Z3_TIMEOUT_LARGE_OBLIGATION_SECS`.
- `qbe-smt` is strict fail-closed: unsupported QBE operations are hard errors (no conservative havoc fallback).
- `qbe-smt` supports FP32/FP64 obligations during prove/struct-invariant/model-invariant checking for the emitted subset (FP32/FP64 args/results, `copy`, `add/sub/mul/div`, `cmp` `eq/ne/lt/le/gt/ge/o/uo`, `phi`, `exts`/`truncd`, `stosi`/`stoui`/`dtosi`/`dtoui`, `swtof`/`uwtof`/`sltof`/`ultof`, and FP32/FP64 `loads`/`stores`) using IEEE floating-point semantics (`RNE` for arithmetic/int->FP, `RTZ` for FP->int and `truncd`).
- Float-conversion edge cases in proving follow solver IEEE-SMT semantics and may differ from CPU-specific runtime behavior for NaN/out-of-range float-to-int conversions.
- `qbe-smt` remains fail-closed for unsupported operations and invalid conversion assignment-type combinations.
- `qbe-smt` models `call $exit(code)` as a halting transition with `exit` state set from `code`.
- `qbe-smt` also models known CLib calls (`malloc`, `free`, `calloc`, `realloc`, `memcpy`, `memmove`, `memcmp`, `memset`, `strlen`, `strcmp`, `strcpy`, `strncpy`, `open`, `read`, `write`, `close`) plus variadic `printf` for builtin `print` inlined paths.
- CLib byte-memory call models use bounded precise expansion (`limit = 16`) with sound fallback branches; unknown extern call targets remain fail-closed unsupported errors.
- String-call precision now includes bounded `strlen` NUL scanning and bounded `strcmp` first-event scanning (difference/shared NUL) with tri-state results (`-1/0/1`), each with fail-open fallback to constrained unknown results when bounds are exceeded.
- `strcpy` effects are modeled as bounded copy-until-NUL (terminator included); if no NUL appears within the inline bound, encoding falls back to unconstrained memory.
- Modeled syscall return values are now constrained: `open` returns `-1` or non-negative; `close` returns `0` or `-1`; `read`/`write` return `-1` or a non-negative value not exceeding `count`.
- `qbe-smt` models `phi` by threading predecessor-block identity through CHC state only for functions whose reachable blocks contain `phi`; functions without reachable `phi` omit `pred` from their PC relations entirely.
- `qbe-smt` is parser-free: proving consumes direct in-memory QBE IR (`qbe::Module` via `qbe_module_to_smt` / `qbe_module_to_smt_with_assumptions`), not re-parsed QBE text.
- `qbe-smt` flattens only entry-reachable blocks; unreachable unsupported instructions do not affect encoding.
- When a struct-invariant obligation is SAT, diagnostics include a control-flow witness summary over the synthesized checker (`cfg_path` and branch decisions).
- `oac build` does not emit a general-purpose QBE SMT sidecar; SMT artifacts are produced under `target/oac/prove/`, `target/oac/struct_invariants/`, and `target/oac/model_invariants/` when obligations exist.
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
