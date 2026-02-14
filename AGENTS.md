# AGENTS: Ousia Contributor Intelligence

This file is the entrypoint for LLM contributors. It is a table of contents for high-value project context in `agents/`.

## Non-Optional Maintenance Rule

If code, commands, architecture, semantics, tests, or workflows change, you must update this file and affected files under `agents/` in the same change set.

Do this autonomously. Do not defer it to “later docs cleanup”.

## How To Use This Pack

1. Read `agents/01-repo-map.md` for structure and boundaries.
2. Read `agents/02-compiler-pipeline.md` before touching parser/IR/codegen.
3. Read `agents/03-language-semantics.md` before changing language behavior.
4. Read `agents/04-testing-ci.md` before refactors, bugfixes, or snapshots.
5. Read `agents/05-engineering-playbook.md` before implementing non-trivial changes.

## Index

- `agents/01-repo-map.md`: repository map, ownership zones, and source-of-truth files.
- `agents/02-compiler-pipeline.md`: front-end to backend flow (`tokenizer` -> `parser` -> `ir` -> `qbe` -> asm -> binary).
- `agents/03-language-semantics.md`: language model and invariants implemented today.
- `agents/04-testing-ci.md`: how to run tests, snapshot behavior, CI expectations, and debugging flow.
- `agents/05-engineering-playbook.md`: practical implementation rules for safe compiler evolution.

## Scope Note

This repository currently contains both the Ousia compiler workspace (`crates/*`) and vendored/reference material under `tools/selfie/`. Prefer touching compiler code only unless explicitly requested.

## Current Syntax Notes

- Templates use square brackets for type parameters and instantiation arguments: `template Option[T] { ... }`, `instantiate OptionI32 = Option[I32]`.
