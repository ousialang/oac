use std::collections::HashSet;
use std::ffi::OsStr;
use std::path::{Component, Path, PathBuf};

use anyhow::Context;

use crate::{parser, tokenizer};

pub fn parse_and_resolve_file(source_path: &Path) -> anyhow::Result<parser::Ast> {
    let source = std::fs::read_to_string(source_path)
        .with_context(|| format!("failed to read source {}", source_path.display()))?;
    let tokens = tokenizer::tokenize(source)
        .with_context(|| format!("failed to tokenize source {}", source_path.display()))?;
    let root_ast = parser::parse(tokens)
        .with_context(|| format!("failed to parse source {}", source_path.display()))?;
    resolve_ast(root_ast, source_path)
}

pub fn resolve_ast(root_ast: parser::Ast, source_path: &Path) -> anyhow::Result<parser::Ast> {
    let mut visited = HashSet::new();
    let mut loading = vec![];
    resolve_ast_inner(root_ast, source_path, &mut visited, &mut loading)
}

fn resolve_ast_inner(
    parsed_ast: parser::Ast,
    source_path: &Path,
    visited: &mut HashSet<PathBuf>,
    loading: &mut Vec<PathBuf>,
) -> anyhow::Result<parser::Ast> {
    let canonical_source = source_path
        .canonicalize()
        .with_context(|| format!("failed to canonicalize {}", source_path.display()))?;

    if visited.contains(&canonical_source) {
        return Ok(parser::Ast::default());
    }

    if let Some(cycle_start) = loading.iter().position(|p| p == &canonical_source) {
        let mut cycle = loading[cycle_start..]
            .iter()
            .map(|p| p.display().to_string())
            .collect::<Vec<_>>();
        cycle.push(canonical_source.display().to_string());
        return Err(anyhow::anyhow!(
            "circular import detected: {}",
            cycle.join(" -> ")
        ));
    }

    loading.push(canonical_source.clone());

    let source_dir = canonical_source
        .parent()
        .ok_or_else(|| anyhow::anyhow!("failed to determine parent directory for import"))?;

    let mut merged = parser::Ast::default();
    for import in &parsed_ast.imports {
        let import_path = resolve_import_path(source_dir, &import.path)?;
        let import_source = std::fs::read_to_string(&import_path)
            .with_context(|| format!("failed to read import {}", import_path.display()))?;
        let import_tokens = tokenizer::tokenize(import_source)
            .with_context(|| format!("failed to tokenize import {}", import_path.display()))?;
        let import_ast = parser::parse(import_tokens)
            .with_context(|| format!("failed to parse import {}", import_path.display()))?;
        let resolved_import_ast = resolve_ast_inner(import_ast, &import_path, visited, loading)?;
        merge_flat_ast(&mut merged, resolved_import_ast);
    }

    merged.type_definitions.extend(parsed_ast.type_definitions);
    merged
        .top_level_functions
        .extend(parsed_ast.top_level_functions);
    merged
        .trait_declarations
        .extend(parsed_ast.trait_declarations);
    merged
        .impl_declarations
        .extend(parsed_ast.impl_declarations);
    merged.tests.extend(parsed_ast.tests);
    merged.invariants.extend(parsed_ast.invariants);
    merged
        .generic_definitions
        .extend(parsed_ast.generic_definitions);
    merged
        .generic_specializations
        .extend(parsed_ast.generic_specializations);
    merged.comptime_applies.extend(parsed_ast.comptime_applies);

    loading.pop();
    visited.insert(canonical_source);

    Ok(merged)
}

fn resolve_import_path(source_dir: &Path, import_path: &str) -> anyhow::Result<PathBuf> {
    let import = Path::new(import_path);
    anyhow::ensure!(
        !import.is_absolute(),
        "import path must be relative to the current directory: {}",
        import_path
    );

    let components = import.components().collect::<Vec<_>>();
    anyhow::ensure!(
        components.len() == 1 && matches!(components[0], Component::Normal(_)),
        "import path must refer to a file in the same directory: {}",
        import_path
    );

    anyhow::ensure!(
        import.extension() == Some(OsStr::new("oa")),
        "import path must end with .oa: {}",
        import_path
    );

    let path = source_dir.join(import);
    anyhow::ensure!(path.exists(), "import file not found: {}", path.display());

    Ok(path)
}

fn merge_flat_ast(dst: &mut parser::Ast, mut src: parser::Ast) {
    dst.type_definitions.append(&mut src.type_definitions);
    dst.top_level_functions.append(&mut src.top_level_functions);
    dst.trait_declarations.append(&mut src.trait_declarations);
    dst.impl_declarations.append(&mut src.impl_declarations);
    dst.tests.append(&mut src.tests);
    dst.invariants.append(&mut src.invariants);
    dst.generic_definitions.append(&mut src.generic_definitions);
    dst.generic_specializations
        .append(&mut src.generic_specializations);
    dst.comptime_applies.append(&mut src.comptime_applies);
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::{parse_and_resolve_file, resolve_ast};
    use crate::parser;
    use crate::tokenizer;

    #[test]
    fn resolve_flat_imports_merges_same_directory_files() {
        let tmp = tempfile::tempdir().expect("create tempdir");
        let helper_path = tmp.path().join("helper.oa");
        let main_path = tmp.path().join("main.oa");

        fs::write(
            &helper_path,
            r#"
fun helper() -> I32 {
	return 7
}

test "helper test" {
	assert(true)
}
"#,
        )
        .expect("write helper");

        fs::write(
            &main_path,
            r#"
import "helper.oa"

fun main() -> I32 {
	print(helper())
	return 0
}
"#,
        )
        .expect("write main");

        let main_source = fs::read_to_string(&main_path).expect("read main");
        let main_tokens = tokenizer::tokenize(main_source).expect("tokenize main");
        let main_ast = parser::parse(main_tokens).expect("parse main");

        let merged = resolve_ast(main_ast, &main_path).expect("resolve imports");
        assert!(merged.imports.is_empty());
        assert!(
            merged
                .top_level_functions
                .iter()
                .any(|f| f.name == "helper"),
            "missing imported helper function"
        );
        assert!(
            merged.top_level_functions.iter().any(|f| f.name == "main"),
            "missing root main function"
        );
        assert_eq!(merged.tests.len(), 1);
        assert_eq!(merged.tests[0].name, "helper test");
    }

    #[test]
    fn resolve_flat_imports_merges_invariant_declarations() {
        let tmp = tempfile::tempdir().expect("create tempdir");
        let helper_path = tmp.path().join("helper.oa");
        let main_path = tmp.path().join("main.oa");

        fs::write(
            &helper_path,
            r#"
struct Counter {
	value: I32,
}

invariant "counter value must be non-negative" for (v: Counter) {
	return v.value >= 0
}
"#,
        )
        .expect("write helper");

        fs::write(
            &main_path,
            r#"
import "helper.oa"

fun main() -> I32 {
	return 0
}
"#,
        )
        .expect("write main");

        let merged = parse_and_resolve_file(&main_path).expect("resolve imports");
        assert_eq!(merged.invariants.len(), 1);
        assert_eq!(
            merged.invariants[0].display_name,
            "counter value must be non-negative"
        );
        assert_eq!(merged.invariants[0].parameter.ty, "Counter");
    }

    #[test]
    fn resolve_flat_imports_rejects_parent_traversal() {
        let tmp = tempfile::tempdir().expect("create tempdir");
        let main_path = tmp.path().join("main.oa");
        fs::write(&main_path, "import \"../outside.oa\"\n").expect("write main");

        let main_source = fs::read_to_string(&main_path).expect("read main");
        let main_tokens = tokenizer::tokenize(main_source).expect("tokenize main");
        let main_ast = parser::parse(main_tokens).expect("parse main");

        let err = resolve_ast(main_ast, &main_path).expect_err("import should fail");
        assert!(
            err.to_string()
                .contains("import path must refer to a file in the same directory"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn resolve_flat_imports_detects_cycles() {
        let tmp = tempfile::tempdir().expect("create tempdir");
        let a_path = tmp.path().join("a.oa");
        let b_path = tmp.path().join("b.oa");

        fs::write(&a_path, "import \"b.oa\"\n").expect("write a");
        fs::write(&b_path, "import \"a.oa\"\n").expect("write b");

        let err = parse_and_resolve_file(&a_path).expect_err("cycle should fail");
        assert!(
            err.to_string().contains("circular import detected"),
            "unexpected cycle error: {err}"
        );
    }
}
