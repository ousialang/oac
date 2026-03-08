# Compiler Pipeline

## End-to-End Build Flow

Defined in `crates/oac/src/main.rs` (`compile` function):

1. Read source file.
2. Tokenize with `tokenizer::tokenize`.
3. Parse with `parser::parse`.
4. Resolve flat imports (`import "file.oa"`) from the same directory via `flat_imports` and merge declarations into one AST scope.
   - CLI `build`/`test`/`bench-prove` share this front-end staging path through `main.rs::parse_source_to_ast_with_artifacts` and `main.rs::compile_source_with_artifacts` to keep tokenize/parse/import/comptime behavior and diagnostics aligned.
5. Execute comptime applies with `comptime::execute_comptime_applies`.
   - The evaluator sees the already-flat-merged user/imported AST plus a preloaded stdlib comptime context from `crates/oac/src/std/std.oa`, so user `comptime apply` can call both imported user helpers and stdlib comptime helpers before `resolve()`.
6. Resolve/type-check with `ir::resolve`.
   - After the initial function-body type check, resolve normalizes receiver method syntax (`value.helper(...)`) into ordinary calls (`TypeName__helper(value, ...)`) or enum-constructor postfix forms before ownership rewriting, purity checks, call indexing, and codegen.
   - The same normalization pass also rewrites non-builtin infix operators into ordinary calls to resolved operator-trait impls (`Addition`, `Subtraction`, `Multiplication`, `Division`, `Equality`, `Comparison`), while keeping compiler-owned primitive scalar operators as builtin `BinOp` nodes.
6. Lower to QBE with `qbe_backend::compile`.
7. Prepare function-precondition + prove + integer-safety + struct-invariant checker artifacts, group ordinary-root obligations into repo-local summary candidates, and consult proof-cache policy from `VerificationConfig` / `--proof-cache`.
   - Function-precondition, prove, integer-safety, and struct-invariant site checkers first prune the cloned caller CFG to blocks that can still reach the targeted site before reachable-callee closure is computed.
   - Assembled checker entry functions rewrite only compiler-generated assert-fail exits (`call $exit(w 242)` + `hlt`) to safe `ret 0` before CHC encoding; helper callees keep terminal assert exits so callers do not continue past impossible states, and other exits remain aborts.
8. Verify function-precondition obligations with `function_preconditions::verify_prepared_function_preconditions` (SMT-based, fail-closed, same ordinary-function summary trust boundary as `prove(...)`, covering reachable user-defined call sites from `main`, generated precondition helpers, struct-invariant helpers, and model-invariant roots).
9. Verify `prove(...)` obligations with `prove::verify_prepared_prove_obligations` (SMT-based, fail-closed, trust mode skips solver only when the combined ordinary-function summary matches a cached `unsat` entry).
10. Verify source-level integer arithmetic obligations with `integer_safety::verify_prepared_integer_safety_obligations` (SMT-based, fail-closed, same ordinary-function summary trust boundary as `prove(...)`, covering reachable integer `+/-/*//` sites from `main` plus all struct/model-invariant roots and generated precondition helpers).
11. Verify struct invariants with `struct_invariants::verify_prepared_struct_invariant_obligations` (SMT-based, fail-closed, same ordinary-function summary trust boundary as precondition/prove/int-safety checking); after all ordinary-root obligations succeed, new `unsat` summaries are persisted for uncached ordinary roots when cache writes are enabled.
12. Verify model invariants with `model_invariants::verify_model_invariants_with_qbe_with_config` (SMT-based, fail-closed, global per-declaration checking, consumes in-memory QBE module, and uses one summary candidate per model-invariant checker root).
13. Run best-effort loop non-termination classification on in-memory QBE `main` (`qbe::Function`) via `qbe_smt::classify_simple_loops`; if a loop is proven non-terminating, fail build before runtime backend toolchain calls.
14. Select runtime backend via CLI flags (`--backend qbe|llvm`, default `qbe`) and emit backend artifacts through `codegen_runtime`:
    - QBE runtime backend: emit `target/oac/ir.qbe`, run `qbe`, emit `target/oac/assembly.s`.
    - LLVM runtime backend: emit `target/oac/ir.ll`, run `clang -x ir -c`, emit `target/oac/object.o`.
15. Invoke C linker/compiler driver attempts to link executable (`target/oac/app`) from backend linker input (`assembly.s` for QBE, `object.o` for LLVM): default `cc` (plus `--target=<triple>` when requested/derived), then fallbacks (`clang --target=<triple>`, target-prefixed `*-gcc` for known QBE arches, plain `cc`). Respect `OAC_CC` (single explicit command), `CC` (preferred first attempt), `OAC_CC_TARGET`, and `OAC_CC_FLAGS` overrides, and fail compilation if all attempts fail.
16. Map stage failures into shared compiler diagnostics (`crates/oac/src/diagnostics.rs`) and render Ariadne reports for CLI users.
17. `oac build` emits compact staged progress rows to `stderr` with program-facing labels (`prepare source`, `check program`, `check proofs`, `check data rules`, `check global rules`, `check loops`, `generate backend`, `link executable`) plus command header/summary; `--quiet` suppresses those rows and `--no-color` disables ANSI styling for both progress rows and diagnostics.

Artifacts emitted during build:
- `target/oac/tokens.json`
- `target/oac/ast.json`
- `target/oac/ir.json`
- `target/oac/ir.qbe`
- `target/oac/ir.ll` (LLVM runtime backend)
- `target/oac/prove/site_*.qbe` (generated checker programs, when prove obligations exist)
- `target/oac/prove/site_*.smt2` (when prove obligations exist)
- `target/oac/preconditions/site_*.qbe` (generated checker programs, when function-precondition obligations exist)
- `target/oac/preconditions/site_*.smt2` (when function-precondition obligations exist)
- `target/oac/integer_safety/site_*.qbe` (generated checker programs, when integer-safety obligations exist)
- `target/oac/integer_safety/site_*.smt2` (when integer-safety obligations exist)
- `target/oac/struct_invariants/site_*.qbe` (generated checker programs, when obligations exist)
- `target/oac/struct_invariants/site_*.smt2` (when invariant obligations exist)
- `target/oac/model_invariants/site_*.qbe` (generated checker programs, when model-invariant obligations exist)
- `target/oac/model_invariants/site_*.smt2` (when model-invariant obligations exist)
- `target/oac/verification_cache/{ordinary_function,model_invariant_function}/.../*.json` (repo-local content-hash-keyed `unsat` proof summaries when cache writes are enabled)
- `target/oac/assembly.s`
- `target/oac/object.o` (LLVM runtime backend)
- `target/oac/app`

## End-to-End Test Flow

Defined in `crates/oac/src/main.rs` (`run_tests` function):

1. Read source file.
2. Tokenize with `tokenizer::tokenize`.
3. Parse with `parser::parse`.
4. Resolve flat imports via `flat_imports` and execute comptime applies.
5. Lower top-level `test "..." { ... }` declarations via `test_framework::lower_tests_to_program` into generated test functions plus a generated `main`.
6. Resolve/type-check with `ir::resolve`.
7. Lower to QBE, run prove/struct-invariant/model-invariant checks, run non-termination classification, emit runtime backend artifacts (`qbe` or `llvm`), and link executable (same backend path as `oac build`).
8. Execute `target/oac/test/app` and treat non-zero exit status as test failure.
9. Map failures into shared compiler diagnostics and render Ariadne reports for CLI users.
10. `oac test` emits the same compile-stage progress UI to `stderr`, plus `collect tests` and `run tests` stages; `--quiet` suppresses harness/progress rows while still forwarding runtime program stdout/stderr, and `--no-color` disables ANSI styling for both progress rows and diagnostics.

Artifacts emitted during test runs:
- `target/oac/test/tokens.json`
- `target/oac/test/ast.json`
- `target/oac/test/ir.json`
- `target/oac/test/ir.qbe`
- `target/oac/test/ir.ll` (LLVM runtime backend)
- `target/oac/test/assembly.s`
- `target/oac/test/object.o` (LLVM runtime backend)
- `target/oac/test/app`
- proof debug artifacts under `target/oac/test/preconditions/`, `target/oac/test/prove/`, `target/oac/test/struct_invariants/`, and `target/oac/test/model_invariants/` when obligations exist
- shared repo-local proof summaries under `target/oac/verification_cache/` when `--proof-cache` is not `off`

## End-to-End Bench Flow

Defined in `crates/oac/src/bench_prove.rs` (`run` / `run_with_runner`):

1. Select fixture corpus (`full` or `quick`) and iteration count.
2. For each fixture+iteration, compile through the same front-end+backend path as `oac build` into isolated targets under `target/oac/bench/runs/<fixture>/iter_<n>/`.
3. Record elapsed wall time per iteration and collect checker artifact metrics (`prove/*.smt2` plus `preconditions/*.smt2` in proof-stage totals, and `struct_invariants/*.smt2` plus `model_invariants/*.smt2` aggregated for invariant stats).
4. Use median elapsed time per fixture as the reported value.
5. Compare fixture medians against committed baseline (`crates/oac/bench/prove_baseline.json`) with regression policy `delta_ms >= 200 && delta_pct >= 20.0`.
6. Emit JSON report (`target/oac/bench/prove/latest.json` by default) plus compact console table.
7. Optional `--update-baseline` rewrites baseline JSON deterministically in canonical fixture order.

Notes:
- Timing regressions are report-only in v1 (command still exits success when outcomes match expectations).
- Unexpected fixture outcomes (unexpected success/failure or wrong diagnostic code) fail the command.
- Full suite fixture set includes prove, function-precondition, struct-invariant, template-hash-table, and model-invariant pass/fail checks; quick suite remains the first four fixtures for fast local iteration.

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
- Generic definitions and specializations (`generic Name[T]`, `specialize Alias = Name[ConcreteType]`), including local `specialize` declarations inside generic bodies.
- Trait declarations and concrete impl blocks (`trait Name { ... }`, `impl Name for Type { ... }`)
- Enum payload variants use `Variant: Type` declarations, while unit variants stay bare.
- Flat import declarations (`import "file.oa"`) for same-directory file inclusion.
- Top-level test declarations (`test "Name" { ... }`).
- Top-level namespaces (`namespace Name { ... }`) support `fun` and `extern fun`; declarations are flattened to mangled internal function keys (`Name__fn`).
- External declarations (`extern fun name(...) -> Type`) are signature-only AST nodes and may appear at top-level or inside namespace blocks.
- Optional function `pre { ... }` blocks are parsed after the return type and before the body on ordinary `fun` definitions; clauses are multiline Bool expressions and the block must contain at least one clause.
- Statements: assign, return, expression, `prove(...)`, `assert(...)`, while, if/else, match
- Expressions: literals, vars, calls, method calls, postfix calls, unary/binary ops, field access, struct values, match-expr (`receiver.fn(args)` parses as a method call; resolve preserves `Name.fn(args)` as static namespace/trait/enum syntax and rewrites value receivers to ordinary calls)
- Char literals are parsed from single quotes (for example `'x'`, `'\n'`) and lowered to a namespaced constructor call (`Char.from_code(<i32>)`).
- Legacy `template` / `instantiate` are hard-cut parser errors with migration hints to `generic` / `specialize`.

Operator precedence is explicitly encoded in parser.

## Semantic Resolution (`ir.rs`)

`resolve(ast)` performs:
- stdlib loading from `crates/oac/src/std/std.oa` (which imports split `std/std_*.oa` modules including `std/std_comptime.oa`, `std/std_clib.oa`, `std/std_io.oa`, `std/std_string.oa`, `std/std_ref.oa`, `std/std_option_result.oa`, `std/std_set.oa`, `std/std_vec.oa`, and `std/std_traits.oa`) using the same flat import resolver, including stdlib invariant declarations.
- deterministic comptime evaluation, including checked `I32` arithmetic in `comptime.rs` (`+/-/*` overflow and `/` divide-by-zero or `MIN / -1` now produce deterministic comptime errors instead of Rust panics)
- comptime semantic reflection builtins over `Type`, now covering both struct metadata (`is_struct`, `as_struct_opt`, `struct_field_count`, `struct_field_at`, `field_name`, `field_type`) and enum metadata (`is_enum`, `as_enum_opt`, `enum_variant_count`, `enum_variant_at`, `variant_name`, `variant_payload_type_opt`) together with existing semantic helpers (`type_name`, `resolve_type`, `expr_meta_opt`, `definition_location_opt`, `is_some`, `unwrap`, `concat`)
- comptime `DeclSet` emission builtins for derived declarations, now including incremental enum construction (`declset_new`, `declset_add_empty_enum`, `declset_add_enum_tag_variant`, `declset_add_enum_payload_variant`) alongside existing derived-struct/invariant emitters
- stdlib comptime helpers are visible during user apply execution because `execute_comptime_applies` preloads stdlib comptime functions/types into its evaluation world without mutating the user AST ahead of `resolve`
- trait metadata collection (signature registry, impl coherence checks, and synthesized concrete impl methods)
- binary-operator resolution that first keeps compiler-owned primitive scalar behavior builtin, then falls back to resolved operator-trait impls for std/user types, with struct/tag-only-enum equality fallback and tagged-payload-enum equality rejection unless `Equality` is implemented
- generic expansion (`specialize`) into concrete type/function/invariant declarations before normal type-checking/codegen stages, including recursive expansion of local generic-body specializations after parent type substitutions are applied.
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
- Function `pre { ... }` clauses are lowered by resolve into synthesized helper functions `__pre__<function_name>__clause_<ordinal>` with the same parameter list as the owning function, and `ResolvedProgram.function_preconditions` tracks the owning function -> helper mapping for later verification/entry assumptions.
- user-defined functions named `prove` or `assert` are rejected (reserved builtin names)
- namespace function calls (`Name.fn(args)`) are type-checked as regular function calls using mangled names (`Name__fn`) when such a function exists; otherwise postfix call semantics continue to serve enum payload constructors
- receiver method calls (`value.fn(args)`) are resolved through the receiver's concrete type (`TypeName__fn(value, args...)`) and normalized into ordinary `Call(...)` nodes before ownership/codegen
- namespace call lowering is also used for generic-specialized helpers (`Alias.fn(args)` resolving to generated `Alias__fn` symbols)
- trait calls are v1 namespaced calls (`Trait.method(value, ...)`) that type-check against trait signatures and resolve to concrete impl function names (`Trait__Type__method`)
- user/std infix operator lowering shares the same trait-resolution path as explicit trait calls; comparison impls normalize to `Comparison.compare(lhs, rhs)` plus a builtin compare-to-zero step
- compiler-reserved primitive operator trait/type pairs (`Addition`/`Subtraction`/`Multiplication`/`Division`/`Comparison` on numeric scalars, `Equality` on numeric scalars plus `Bool`) reject user/std overrides during impl collection
- trait coherence is enforced globally: duplicate `impl Trait for Type` is rejected, and missing impls for generic bounds are rejected at specialization time
- special lifecycle-trait signatures are enforced: `Copy.copy(Ref[Self]) -> Self` and `Drop.drop(Self) -> Void`
- ownership analysis/rewriting runs during resolve for user runtime functions:
  - move-only default for non-`Copy` locals (use-after-move diagnostics)
  - implicit-copy eligibility for types with concrete `Copy` impls
  - inserted `Drop.drop(...)` statements at reassignment overwrite points and lexical scope exits
- built-in `U8`/`FP32`/`FP64` exist alongside integer primitives; unsuffixed decimal literals type-check as `FP32`, and `f64`-suffixed decimal literals type-check as `FP64`
- arithmetic/comparison on numerics requires matching widths/types (`U8/U8`, `I32/I32`, `I64/I64`, `FP32/FP32`, `FP64/FP64`), with no implicit int/float coercions
- `U8` comparisons/codegen are unsigned (`ult/ule/ugt/uge`), and `U8` division lowers to unsigned division (`udiv`)
- stdlib split modules intentionally expose namespaced helper APIs for JSON (`Json.*`), now including both scanner/validator helpers (`json_kind`, `parse_json_document_result`) and value-tree parsing helpers (`parse_json_document_value_result`, `object_get`, `array_get`)
- JSON structured values now represent booleans as `JsonValue.Bool: Bool` (instead of separate `True`/`False` variants), and kind classification uses `JsonKind.Bool`.
- stdlib split modules also include `AsciiChar`/`AsciiCharResult` helpers in `crates/oac/src/std/std_ascii.oa`, loaded through `crates/oac/src/std/std.oa` like other std modules
- stdlib split modules also include `Char` helper API in `crates/oac/src/std/std_char.oa`, loaded through `crates/oac/src/std/std.oa` like other std modules
- stdlib split modules now also include `Null` as an empty struct in `crates/oac/src/std/std_null.oa` (with `Null.value()` helper), loaded through `crates/oac/src/std/std.oa` like other std modules
- stdlib split modules now also include `Bytes` + `String` in `crates/oac/src/std/std_string.oa`; `String` is std-defined as a tagged enum (`Literal: Bytes`, `Heap: Bytes`) and is no longer a resolver primitive
- `String` std helper surface includes structural accessors plus utility helpers (`String.equals`, `String.starts_with`, `String.ends_with`, `String.char_at_or`, `String.slice_clamped`)
- stdlib split modules now also include generic `Option[T]` / `Result[T,E]` in `crates/oac/src/std/std_option_result.oa`
- stdlib split modules now also include generic `Ref[T]` / `Mut[T]` in `crates/oac/src/std/std_ref.oa` with typed read helpers (`U8Ref.read`, `I32Ref.read`, `I64Ref.read`, `PtrIntRef.read`, `BoolRef.read`) and mutable read/write helpers (`U8Mut.*`, `I32Mut.*`, `I64Mut.*`, `PtrIntMut.*`, `BoolMut.*`)
- stdlib split modules now also include generic `HashSet[K: Hash + Equality]` in `crates/oac/src/std/std_set.oa` with persistent set-algebra helpers (`union`, `intersection`, `difference`) and insertion/removal result payloads (`InsertResult`, `RemoveResult`)
- stdlib split modules now also include generic `Vec[T]` in `crates/oac/src/std/std_vec.oa` with persistent vector-style helpers (`push`, `pop`, `get`, `set`, `reserve`, `clear`) and explicit result enums/structs
- C interop signatures are no longer compiler-injected from JSON; stdlib exposes them via `namespace Clib { extern fun ... }` in `crates/oac/src/std/std_clib.oa` (resolver keys are still mangled as `Clib__*` for namespaced-call lookup)
- stdlib split modules now also include `namespace Io` wrappers in `crates/oac/src/std/std_io.oa` over `Clib.open/read/write/close` with explicit result enums (`IoError`, `IoReadResult`, `IoWriteResult`)
- resolver builtins include numeric aliases `Int` -> `I32` and `PtrInt` -> `I64`
- resolver builtins also include `Void` for procedure-like extern signatures
- resolver builtins also include pointer-memory helpers `load_u8(addr: PtrInt) -> U8`, `load_i32(addr: PtrInt) -> I32`, `load_i64(addr: PtrInt) -> I64`, `load_bool(addr: PtrInt) -> Bool`, `store_u8(addr: PtrInt, value: U8) -> Void`, `store_i32(addr: PtrInt, value: I32) -> Void`, `store_i64(addr: PtrInt, value: I64) -> Void`, and `store_bool(addr: PtrInt, value: Bool) -> Void`
- `extern fun` declarations are signature-only (`extern` cannot be `comptime` and extern functions must not have bodies)
- v2 ABI restriction: `extern fun` signatures cannot use struct parameter or return types; use manual `PtrInt` wrappers at C ABI boundaries when struct-like payloads are needed
- `Void` is restricted in v1: function parameters cannot be `Void`, but both extern and non-extern functions may return `Void`
- declaration-based stdlib invariants (for example `AsciiChar` range checks over wrapped `Char.code`) are synthesized and registered during resolve like user-declared invariants
- consistent return types inside a function
- `main` must be either `fun main() -> I32`, `fun main(argc: I32, argv: I64) -> I32`, or `fun main(argc: I32, argv: PtrInt) -> I32`
- semantic reflection/emission builtins remain comptime-only: runtime functions cannot call either the `DeclSet` emitters or any of the struct/enum/type metadata helpers
- invariant declarations support one or more parameters in `for (...)` for both single and grouped syntax; empty parameter lists are parser errors.
- arity-sensitive invariant semantics are enforced in resolve:
  - unary (`for (v: StructType)`) invariants remain struct invariants and synthesize `__struct__<TypeName>__invariant__<key>`
  - multi-argument (`for (a: ..., b: ..., ...)`) invariants become model invariants and synthesize `__model__invariant__<key>`
- unary invariants keep legacy compatibility for explicit `__struct__<TypeName>__invariant(v: TypeName) -> Bool` functions.
- model invariants are resolve-validated as a strict pure subset over their transitive user-call graph (reject `prove`, `assert`, extern calls, pointer load/store builtins, and side-effect builtins `print`/`print_str`).
- `invariant_metadata.rs` centralizes struct-invariant metadata discovery and argument-invariant assumption construction, reused by prove, struct-invariant, and model-invariant verification entrypoints.
- `verification_cycles.rs` centralizes reachable user-call graph discovery plus SCC-based recursion-cycle policy checks reused by prove, struct-invariants, and model invariants.
- `prove(...)` sites reachable from `main` are verified by checker QBE synthesis: the site condition is marked in QBE, checker returns `1` when the proof condition is false at the site, and proving asks reachability of exit code `1` (`unsat` = proven, `sat` = compile failure)
- reachable user-call return sites for struct-typed values are verified per `(call-site, invariant)` with generated checker QBE programs where return code `1` means violation; proving asks reachability of exit code `1` (`unsat` = success)
- model invariants are verified globally (independent of `main` reachability): one checker obligation per declaration, where checker return is rewritten to `1` when invariant result is `0`.
- checker generation is QBE-native and interprocedural: site instrumentation happens on compiled caller QBE, checker artifacts include a checker entry plus reachable user callees, and CHC encoding models user calls through function-summary relations (no checker-time call inlining)
- checker encoding adds argument preconditions for invariant-bearing parameter types in all verification pipelines: if a checker function argument’s semantic type has one or more struct invariants, encoding assumes each invariant relation returns non-zero at function entry (assumption-only; entry memory/heap state is not overwritten from invariant-call outputs)
- call-only recursion cycles are allowed during struct-invariant/prove/model-invariant verification; only cycles that include argument-invariant precondition edges are rejected fail-closed on the combined verification graph

## Backend (`qbe_backend.rs`)

- Generates QBE module/functions/data.
- Includes builtins and interop helpers (for example integer ops, print, string utilities) plus user/std-declared extern call targets.
- Extern calls emit symbol names from signature metadata; namespace externs (for example `Clib.malloc`) therefore call raw declared extern symbols (for example `malloc`) while keeping namespaced lookup keys internal.
- Struct literals allocate zero-initialized storage via `calloc` before field stores, so padding bytes are deterministic for bytewise equality.
- Struct assignment/call/return no longer inject unconditional clone barriers.
- Value reads lower through static `Copy.copy(...)` calls only when the resolved concrete type implements `Copy`; codegen passes either the value directly (legacy by-value impl signatures) or a synthesized temporary `Ref` wrapper (ref-style impl signatures).
- Resolver-inserted `Drop.drop(...)` statements lower as ordinary `Void` call statements in codegen.
- Struct `==` / `!=` lower through `memcmp(lhs, rhs, size)` and compare the result with zero.
- Handles expression lowering and control-flow generation.
- Trait calls are lowered with static dispatch only (resolved concrete impl symbols), with no runtime dictionaries or vtables.
- Lowers `Void`-return calls only as statement calls; `Void` calls used as expression values are rejected.
- Lowers pointer-memory builtins to QBE loads/stores: `load_u8` -> `loadub`, `load_i32` -> `loadw`, `load_i64` -> `loadl`, `load_bool` -> `loadw` + compare-to-zero, `store_u8` -> `storeb`, `store_i32`/`store_bool` -> `storew`, and `store_i64` -> `storel`.
- Lowers string literals to std-owned `String.Literal(Bytes{ptr,len})` heap objects (compiler allocates `Bytes` payload and tagged-union `String` wrapper).
- String helper builtins (`char_at`, `string_len`, `slice`, `print_str`) operate over std `String`/`Bytes` layout rather than raw C-string pointers.
- Maps `FP32` to QBE `s` (`Type::Single`) and `FP64` to QBE `d` (`Type::Double`), emitting ordered float comparisons (`clt*/cle*/cgt*/cge*`) for `< <= > >=`.
- Maps `U8` to QBE word temporaries with unsigned compare/div lowering for `U8` arithmetic relations.
- Emits lightweight integer-site markers for source-level integer `+`, `-`, `*`, `/` expressions (`.oac_integer_site_<semantic_type>__<op>__<site_id>` plus `lhs`/`rhs`/`out` copies) so proof-stage integer checkers can recover operands/results without marking compiler-internal pointer math or offset arithmetic.
- Produces snapshots in tests for codegen and runtime behavior.

## Runtime Backend Dispatch (`codegen_runtime.rs` + `llvm_backend.rs`)

- Verification remains QBE-only regardless of runtime backend.
- Runtime backend selection is explicit on `oac build` / `oac test`:
  - `--backend qbe` (default), optional `--qbe-arch <arch>`
  - `--backend llvm` (rejects `--qbe-arch`)
  - `--target <triple>` applies to LLVM IR compilation/linking and linker attempt target resolution.
- LLVM runtime lowering emits textual LLVM IR directly from `ir::ResolvedProgram` (`llvm_backend::compile`) and does not use a production `compile_with_qbe` runtime path.
- Shared runtime value/tagged-union layout invariants used by both backends live in `runtime_layout.rs`.
- In LLVM runtime lowering, `prove(...)` is verification-only and emits no runtime behavior.

## SMT Adjacent Paths

- `verification.rs` is the shared in-crate verification entrypoint; it runs ordinary-root prove obligations first, then ordinary-root integer-safety obligations, then struct invariants, then model invariants.
- `qbe-smt` is used by prove, struct-invariant, and model-invariant verification to encode checker QBE modules (checker entry + reachable user callees) into CHC/fixedpoint (Horn) constraints.
- `integer_safety.rs` reuses the same checker-module closure helpers as `prove.rs`: it collects marker sites reachable from `main` plus struct/model-invariant roots, clones the site’s caller into checker `main`, prunes CFG branches that cannot reach the target marker, injects a `ret bad` predicate after the marker, and groups resulting obligations into ordinary/model summary candidates for cache reuse.
- `prove.rs` and `struct_invariants.rs` now use the same shared target-reachability pruning helper as `integer_safety.rs`, so cloned checker entries are trimmed to target-reaching blocks before `direct_user_callees(...)` computes reachable checker-module closure.
- `qbe-smt` also owns CHC solver execution (`solve_chc_script`), so invariant/prove verification shares one encode+solve backend path.
- `oac` routes prove/struct-invariant/model-invariant solver calls through `crates/oac/src/verification_solver.rs`, which preserves baseline two-step retries (`10s`, `30s`) and can add a candidate-only third attempt for large obligations that remain `unknown`.
- `main.rs` also uses `qbe-smt` loop classification on generated in-memory `main` QBE as an early non-termination guard.
- `qbe-smt` is parser-free: it consumes in-memory QBE IR directly as modules (`qbe::Module` via `qbe_module_to_smt` / `qbe_module_to_smt_with_assumptions`). Internals are split by concern across `crates/qbe-smt/src/lib.rs` (API + tests), `crates/qbe-smt/src/encode.rs` (Horn encoding), `crates/qbe-smt/src/encode_extern_models.rs` (extern-call model/arity catalog), and `crates/qbe-smt/src/classify.rs` (loop classification).
- `qbe-smt` models a broad integer + memory QBE subset plus an FP32/FP64 proving subset:
  - integer ALU/comparison ops (`add/sub/mul/div/rem`, unsigned variants, bitwise/shift ops)
  - FP32/FP64 ALU/comparison ops (`add/sub/mul/div`, `eq/ne/lt/le/gt/ge/o/uo`) with IEEE semantics (`RNE`)
  - FP conversion ops: `exts` (FP32 -> FP64, `RNE`), `truncd` (FP64 -> FP32, `RTZ`), `stosi/stoui/dtosi/dtoui` (FP -> int, `RTZ`), and `swtof/uwtof/sltof/ultof` (int -> FP, `RNE`)
  - `phi` merging via predecessor-tracking state in CHC (`pred`), emitted only for functions whose reachable blocks actually contain `phi`
  - `call` modeling for `malloc`, `free`, `calloc`, `realloc`, `memcpy`, `memmove`, `memcmp`, `memset`, `strlen`, `strcmp`, `strcpy`, `strncpy`, `open`, `read`, `write`, `close`, `exit(code)`, and variadic `printf` (for builtin `print` lowering)
  - `load*`/`store*` byte-addressed memory operations (including FP32 `loads`/`stores`)
  - `alloc4/alloc8/alloc16` heap-pointer modeling
  - control flow via Horn transition rules (`jnz`, `jmp`, `ret`, halt relation)
- Register state is encoded as an SMT array and threaded through relation arguments.
- Relation state threads predecessor-block identity only for `phi`-bearing functions, so branch-edge semantics stay explicit where needed without widening every PC relation in the module.
- Property surface is fixed: query whether halt with `exit == 1` is reachable (`(query bad)`).
- Unsupported constructs are fail-closed hard errors (no havoc fallback path).
- For modeled CLib memory operations, encoding uses bounded precise expansion (`limit = 16`) plus sound fallback branches (for example, unconstrained `mem_next` when bounds are exceeded).
- Bounded helper expressions in `encode.rs` are assembled with linearized SMT `let` chains (instead of repeated nested expression duplication) to reduce obligation size growth while preserving precise/fallback semantics.
- Bounded string-call details: `strlen` scans for NUL up to the inline limit and otherwise falls back to constrained unknown non-negative length; `strcmp` performs bounded first-event scan (`difference` or shared NUL) with tri-state results (`-1/0/1`) and otherwise falls back to unconstrained return.
- `strcpy` memory effects are modeled as bounded byte copy until first NUL (including terminator); if no NUL is found within the inline limit, memory falls back to unconstrained `mem_next`.
- Syscall-like modeled return constraints are explicit: `open` -> `-1 | >=0`, `close` -> `0 | -1`, `read`/`write` -> `-1 | (0 <= ret <= count)`.
- FP32/FP64 obligations are supported in checker encoding for the emitted subset (FP32/FP64 args/results, `copy`, `add/sub/mul/div`, `cmp` `eq/ne/lt/le/gt/ge/o/uo`, `phi`, `exts`/`truncd`, `stosi`/`stoui`/`dtosi`/`dtoui`, `swtof`/`uwtof`/`sltof`/`ultof`, and FP32/FP64 `loads`/`stores`), and force `(set-logic ALL)` in the emitted SMT script.
- Conversion edge cases follow solver IEEE-SMT semantics and may differ from CPU-specific runtime behavior for NaN/out-of-range float-to-int conversions.
- Invalid conversion assignment-type pairings remain fail-closed in checker encoding (`Unsupported` errors).
- Encoding/validation is reachable-code-aware: only blocks reachable from function entry are flattened into Horn rules, so unreachable unsupported code does not block proving.
- Main-argument-aware assumption remains available: when enabled and main has `argc`, encoding asserts `argc >= 0`.
- Module-level argument assumptions are also available: `oac` passes both per-function invariant-bearing argument assumptions and integer range assumptions, and `qbe-smt` validates these references fail-closed (function exists/encoded, argument index in range, invariant target unary, range bounds/order valid). Current integer range use is checker-entry `[0,255]` assumptions for semantic `U8` parameters.
- Struct-invariant SAT failures include a compact checker CFG witness (block path + branch directions); for `main(argc, argv)` obligations, `oac` also extracts a concrete `argc` witness via additional CHC range queries.
- Loop classification is intentionally conservative: currently proves only a narrow canonical while-loop shape where the guard is initially true on entry and the body preserves the guard variable (`x' = x`), otherwise result is unknown and build proceeds.

## LSP Path

- `main.rs` also exposes `test` subcommand (`oac test <file.oa>`) for lowered test-declaration execution.
- `main.rs` also exposes `fmt` subcommand (`oac fmt <file.oa>`) for in-place source formatting via `crates/oac/src/formatter.rs`.
- `build`/`test` backend flags now follow: `oac build <file.oa> --backend <qbe|llvm> [--qbe-arch <arch>] [--target <triple>] [--quiet] [--no-color]` and `oac test <file.oa> --backend <qbe|llvm> [--qbe-arch <arch>] [--target <triple>] [--quiet] [--no-color]`.
- `main.rs` also exposes `lsp` subcommand (`oac lsp`).
- `main.rs` also exposes `bench-prove` subcommand (`oac bench-prove --suite <full|quick> --iterations <N> [--baseline <path>] [--output <path>] [--update-baseline] [--strict-outcome-gate] [--proof-cache trust|strict|off]`).
- `--strict-outcome-gate` runs baseline/candidate verification-outcome captures over the selected fixture corpus and fails on forbidden transitions (`sat/unsat` drift or obligation-key set drift), writing artifacts to `target/oac/verification_outcomes/`.
- `--proof-cache` defaults to `strict` for `bench-prove`, and benchmark-run cache policy is read-only so quick/full suite timings remain live-solve measurements even when cache reads are enabled.
- `lsp.rs` runs JSON-RPC over stdio, handles `initialize`/`shutdown`/`exit`, text document open/change/save/close notifications, and requests for definition/hover/document symbols/references/completion.
- LSP import crawling for project-symbol indexing now reuses `flat_imports::validate_same_dir_oa_import(...)` so editor-side import acceptance matches compiler import semantics.
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
