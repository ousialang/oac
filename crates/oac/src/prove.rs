use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::path::Path;

use anyhow::Context;

use crate::invariant_metadata::{
    build_function_arg_invariant_assumptions, build_function_arg_invariant_assumptions_for_names,
    build_function_arg_invariant_assumptions_with_name_overrides,
    discover_struct_invariant_bindings, InvariantBinding,
};
use crate::ir::ResolvedProgram;
use crate::qbe_backend::PROVE_MARKER_PREFIX;
use crate::verification_cycles::{
    reachable_user_functions, reject_recursion_cycles_with_arg_invariants,
};

const Z3_TIMEOUT_SECONDS: u64 = 10;

#[derive(Clone, Debug)]
struct ProveSite {
    id: String,
    caller: String,
    marker_temp: String,
}

pub fn verify_prove_obligations_with_qbe(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
) -> anyhow::Result<()> {
    let invariant_by_struct = discover_struct_invariant_bindings(program)?;
    let reachable = reachable_user_functions(program, "main")?;

    let function_map = qbe_module
        .functions
        .iter()
        .map(|function| (function.name.clone(), function.clone()))
        .collect::<HashMap<_, _>>();

    let sites = collect_prove_sites(&function_map, &reachable)?;
    if sites.is_empty() {
        return Ok(());
    }

    let reachable_names = reachable.iter().cloned().collect::<BTreeSet<_>>();
    let arg_invariant_assumptions = build_function_arg_invariant_assumptions_for_names(
        program,
        &reachable_names,
        &invariant_by_struct,
    )?;
    reject_recursion_cycles_with_arg_invariants(
        program,
        "main",
        &reachable,
        &arg_invariant_assumptions,
        "prove verification",
    )?;
    solve_prove_sites(
        program,
        &invariant_by_struct,
        &function_map,
        &sites,
        target_dir,
    )
}

fn collect_prove_sites(
    function_map: &HashMap<String, qbe::Function>,
    reachable: &HashSet<String>,
) -> anyhow::Result<Vec<ProveSite>> {
    let mut functions = reachable.iter().cloned().collect::<Vec<_>>();
    functions.sort();

    let mut sites = Vec::new();
    for function_name in functions {
        let function = function_map
            .get(&function_name)
            .ok_or_else(|| anyhow::anyhow!("missing QBE function {}", function_name))?;

        for (block_index, block) in function.blocks.iter().enumerate() {
            for (item_index, item) in block.items.iter().enumerate() {
                let qbe::BlockItem::Statement(qbe::Statement::Assign(
                    qbe::Value::Temporary(dest),
                    _,
                    qbe::Instr::Copy(_),
                )) = item
                else {
                    continue;
                };

                if !dest.starts_with(PROVE_MARKER_PREFIX) {
                    continue;
                }

                sites.push(ProveSite {
                    id: format!("{}#{}#{}", function_name, block_index, item_index),
                    caller: function_name.clone(),
                    marker_temp: dest.clone(),
                });
            }
        }
    }

    sites.sort_by(|a, b| a.id.cmp(&b.id));
    Ok(sites)
}

fn solve_prove_sites(
    program: &ResolvedProgram,
    invariant_by_struct: &HashMap<String, Vec<InvariantBinding>>,
    function_map: &HashMap<String, qbe::Function>,
    sites: &[ProveSite],
    target_dir: &Path,
) -> anyhow::Result<()> {
    let verification_dir = target_dir.join("prove");
    std::fs::create_dir_all(&verification_dir).with_context(|| {
        format!(
            "failed to create prove verification directory {}",
            verification_dir.display()
        )
    })?;

    let mut failures = Vec::new();
    for site in sites {
        let (checker_module, checker_function, assumptions) =
            build_site_checker_module(program, invariant_by_struct, function_map, site)?;
        let checker_qbe = checker_module.to_string();
        let site_stem = format!("site_{}", sanitize_ident(&site.id));
        let qbe_filename = format!("{}.qbe", site_stem);
        let smt_filename = format!("{}.smt2", site_stem);

        let qbe_path = verification_dir.join(&qbe_filename);
        std::fs::write(&qbe_path, &checker_qbe).with_context(|| {
            format!(
                "failed to write prove checker QBE program {}",
                qbe_path.display()
            )
        })?;

        let smt = qbe_smt::qbe_module_to_smt_with_assumptions(
            &checker_module,
            "main",
            &qbe_smt::EncodeOptions {
                assume_main_argc_non_negative: should_assume_main_argc_non_negative(
                    site,
                    &checker_function,
                ),
                first_arg_i32_range: None,
            },
            &assumptions,
        )
        .map_err(|err| {
            anyhow::anyhow!(
                "failed to encode prove checker QBE for {}: {}\n{}",
                site.id,
                err,
                err.render_report_plain("prove-checker")
            )
        })?;

        let smt_path = verification_dir.join(&smt_filename);
        std::fs::write(&smt_path, &smt).with_context(|| {
            format!(
                "failed to write prove SMT obligation {}",
                smt_path.display()
            )
        })?;

        match qbe_smt::solve_chc_script_with_diagnostics(&smt, Z3_TIMEOUT_SECONDS) {
            Ok(run) if run.result == qbe_smt::SolverResult::Unsat => {}
            Ok(run) if run.result == qbe_smt::SolverResult::Sat => {
                let solver_excerpt = summarize_solver_output(&run.stdout, &run.stderr)
                    .map(|excerpt| format!(", solver_excerpt={excerpt}"))
                    .unwrap_or_default();
                let mut failure = format!(
                    "{} (caller={}, qbe_artifact={}, smt_artifact={}",
                    site.id, site.caller, qbe_filename, smt_filename
                );
                failure.push_str(&solver_excerpt);
                failure.push(')');
                failures.push(failure);
            }
            Ok(_run) => {
                return Err(anyhow::anyhow!(
                    "solver returned unknown for prove obligation {}",
                    site.id
                ));
            }
            Err(err) => {
                return Err(anyhow::anyhow!(
                    "failed to solve prove obligation {}: {}\n{}",
                    site.id,
                    err,
                    err.render_report_plain("prove-obligation")
                ))
            }
        }
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(anyhow::anyhow!(
            "prove verification failed (SAT counterexamples found):\n{}",
            failures.join("\n")
        ))
    }
}

fn build_site_checker_module(
    program: &ResolvedProgram,
    invariant_by_struct: &HashMap<String, Vec<InvariantBinding>>,
    function_map: &HashMap<String, qbe::Function>,
    site: &ProveSite,
) -> anyhow::Result<(qbe::Module, qbe::Function, qbe_smt::ModuleAssumptions)> {
    let caller = function_map
        .get(&site.caller)
        .ok_or_else(|| anyhow::anyhow!("missing QBE function for caller {}", site.caller))?;
    let mut checker = caller.clone();
    checker.name = "main".to_string();
    checker.linkage = qbe::Linkage::private();
    checker.return_ty = Some(qbe::Type::Word);

    rewrite_returns_to_zero(&mut checker);
    inject_site_check_and_return(&mut checker, site)?;

    let mut checker_to_program_name = HashMap::new();
    if site.caller != "main" {
        checker_to_program_name.insert("main".to_string(), site.caller.clone());
    }

    let (module, assumptions) = checker_module_with_reachable_callees(
        program,
        invariant_by_struct,
        function_map,
        &checker,
        &checker_to_program_name,
    )?;
    Ok((module, checker, assumptions))
}

fn checker_module_with_reachable_callees(
    program: &ResolvedProgram,
    invariant_by_struct: &HashMap<String, Vec<InvariantBinding>>,
    function_map: &HashMap<String, qbe::Function>,
    checker: &qbe::Function,
    checker_to_program_name: &HashMap<String, String>,
) -> anyhow::Result<(qbe::Module, qbe_smt::ModuleAssumptions)> {
    let mut additional_roots = BTreeSet::<String>::new();
    loop {
        let mut module = qbe::Module::default();
        module.functions.push(checker.clone());

        let mut visited = HashSet::<String>::new();
        let mut queue = VecDeque::<String>::new();
        for callee in direct_user_callees(checker, function_map) {
            queue.push_back(callee);
        }
        for root in &additional_roots {
            if root != &checker.name {
                queue.push_back(root.clone());
            }
        }

        while let Some(callee_name) = queue.pop_front() {
            if !visited.insert(callee_name.clone()) {
                continue;
            }
            let callee = function_map.get(&callee_name).ok_or_else(|| {
                anyhow::anyhow!("missing QBE function for callee {}", callee_name)
            })?;
            module.functions.push(callee.clone());
            for nested in direct_user_callees(callee, function_map) {
                if !visited.contains(&nested) {
                    queue.push_back(nested);
                }
            }
        }

        let assumptions = if checker_to_program_name.is_empty() {
            build_function_arg_invariant_assumptions(
                program,
                &module.functions,
                invariant_by_struct,
            )?
        } else {
            build_function_arg_invariant_assumptions_with_name_overrides(
                program,
                &module.functions,
                invariant_by_struct,
                checker_to_program_name,
            )?
        };
        let required_invariant_functions = assumptions
            .iter()
            .map(|assumption| assumption.invariant_function_name.clone())
            .collect::<BTreeSet<_>>();

        let mut next_roots = additional_roots.clone();
        next_roots.extend(required_invariant_functions);
        if next_roots == additional_roots {
            return Ok((
                module,
                qbe_smt::ModuleAssumptions {
                    arg_invariant_assumptions: assumptions,
                },
            ));
        }
        additional_roots = next_roots;
    }
}

fn direct_user_callees(
    function: &qbe::Function,
    function_map: &HashMap<String, qbe::Function>,
) -> BTreeSet<String> {
    let mut callees = BTreeSet::new();
    for block in &function.blocks {
        for item in &block.items {
            let qbe::BlockItem::Statement(statement) = item else {
                continue;
            };
            let maybe_name = match statement {
                qbe::Statement::Assign(_, _, qbe::Instr::Call(name, _, _))
                | qbe::Statement::Volatile(qbe::Instr::Call(name, _, _)) => Some(name),
                _ => None,
            };
            if let Some(name) = maybe_name {
                if function_map.contains_key(name) {
                    callees.insert(name.clone());
                }
            }
        }
    }
    callees
}

fn rewrite_returns_to_zero(function: &mut qbe::Function) {
    for block in &mut function.blocks {
        for item in &mut block.items {
            let qbe::BlockItem::Statement(qbe::Statement::Volatile(instr)) = item else {
                continue;
            };
            if matches!(instr, qbe::Instr::Ret(_)) {
                *instr = qbe::Instr::Ret(Some(qbe::Value::Const(0)));
            }
        }
    }
}

fn inject_site_check_and_return(
    function: &mut qbe::Function,
    site: &ProveSite,
) -> anyhow::Result<()> {
    let mut found = false;
    let bad_temp = format!("{}_bad", site.marker_temp);

    for block in &mut function.blocks {
        for item_index in 0..block.items.len() {
            let qbe::BlockItem::Statement(qbe::Statement::Assign(
                qbe::Value::Temporary(dest),
                _,
                qbe::Instr::Copy(_),
            )) = &block.items[item_index]
            else {
                continue;
            };
            if dest != &site.marker_temp {
                continue;
            }

            let mut new_items = block.items[..=item_index].to_vec();
            new_items.push(qbe::BlockItem::Statement(qbe::Statement::Assign(
                qbe::Value::Temporary(bad_temp.clone()),
                qbe::Type::Word,
                qbe::Instr::Cmp(
                    qbe::Type::Word,
                    qbe::Cmp::Eq,
                    qbe::Value::Temporary(site.marker_temp.clone()),
                    qbe::Value::Const(0),
                ),
            )));
            new_items.push(qbe::BlockItem::Statement(qbe::Statement::Volatile(
                qbe::Instr::Ret(Some(qbe::Value::Temporary(bad_temp.clone()))),
            )));
            block.items = new_items;
            found = true;
            break;
        }
        if found {
            break;
        }
    }

    if found {
        Ok(())
    } else {
        Err(anyhow::anyhow!(
            "failed to locate prove marker {} for site {}",
            site.marker_temp,
            site.id
        ))
    }
}

fn sanitize_ident(input: &str) -> String {
    let mut out = String::new();
    for (i, ch) in input.chars().enumerate() {
        let keep = ch.is_ascii_alphanumeric() || ch == '_';
        if keep {
            if i == 0 && ch.is_ascii_digit() {
                out.push('_');
            }
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() {
        "_sym".to_string()
    } else {
        out
    }
}

fn should_assume_main_argc_non_negative(site: &ProveSite, checker: &qbe::Function) -> bool {
    if site.caller != "main" {
        return false;
    }
    if checker.arguments.len() != 2 {
        return false;
    }
    matches!(checker.arguments[0].0, qbe::Type::Word)
        && matches!(checker.arguments[1].0, qbe::Type::Long)
}

fn summarize_solver_output(stdout: &str, stderr: &str) -> Option<String> {
    let mut snippets = stdout
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .skip(1)
        .take(2)
        .map(|line| line.to_string())
        .collect::<Vec<_>>();

    if snippets.is_empty() {
        snippets = stderr
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
            .take(1)
            .map(|line| line.to_string())
            .collect::<Vec<_>>();
    }

    if snippets.is_empty() {
        None
    } else {
        Some(snippets.join(" | "))
    }
}

#[cfg(test)]
mod tests {
    use crate::verification_cycles::{
        reachable_user_functions, reject_recursion_cycles_with_arg_invariants,
    };
    use crate::{ir, parser, qbe_backend, tokenizer};

    use super::verify_prove_obligations_with_qbe;

    fn resolve_program(source: &str) -> ir::ResolvedProgram {
        let tokens = tokenizer::tokenize(source.to_string()).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        ir::resolve(ast).expect("resolve source")
    }

    #[test]
    fn no_prove_sites_is_noop() {
        let source = r#"
fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let program = resolve_program(&source);
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        verify_prove_obligations_with_qbe(&program, &qbe_module, tempdir.path())
            .expect("no prove obligations should pass");
    }

    #[test]
    fn prove_sites_can_use_argument_invariant_preconditions() {
        let source = r#"
struct Foo {
	x: I32,
}

invariant "x non-negative" for (v: Foo) {
	return v.x >= 0
}

fun helper(v: Foo) -> I32 {
	prove(v.x >= 0)
	return 0
}

fun main() -> I32 {
	f = Foo struct { x: sub(0, 1), }
	return helper(f)
}
"#;

        let program = resolve_program(source);
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        verify_prove_obligations_with_qbe(&program, &qbe_module, tempdir.path())
            .expect("argument-invariant preconditions should satisfy helper prove obligations");
    }

    #[test]
    fn prove_sites_use_all_argument_invariant_preconditions_for_multi_invariant_types() {
        let source = r#"
struct Counter {
	value: I32,
	max: I32,
}

invariant value_non_negative "value non-negative" for (v: Counter) {
	return v.value >= 0
}

invariant max_non_negative "max non-negative" for (v: Counter) {
	return v.max >= 0
}

fun helper(v: Counter) -> I32 {
	prove(v.value >= 0)
	prove(v.max >= 0)
	return 0
}

fun main() -> I32 {
	c = Counter struct { value: sub(0, 1), max: sub(0, 2), }
	return helper(c)
}
"#;

        let program = resolve_program(source);
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        verify_prove_obligations_with_qbe(&program, &qbe_module, tempdir.path())
            .expect("all invariant preconditions should be applied to prove-site parameters");
    }

    #[test]
    fn rejects_cycles_introduced_by_argument_invariant_edges() {
        let source = r#"
struct Foo {
	x: I32,
}

invariant "foo invariant" for (v: Foo) {
	w = helper(v)
	return w == w
}

fun helper(v: Foo) -> I32 {
	prove(v.x >= 0)
	return v.x
}

fun main() -> I32 {
	f = Foo struct { x: 1, }
	return helper(f)
}
"#;

        let program = resolve_program(source);
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        let err = verify_prove_obligations_with_qbe(&program, &qbe_module, tempdir.path())
            .expect_err("combined call graph cycles must fail closed");
        assert!(err
            .to_string()
            .contains("includes arg-invariant precondition edges"));
    }

    #[test]
    fn allows_call_only_recursion_in_verified_paths() {
        let source = r#"
fun a(n: I32) -> I32 {
	if n <= 0 {
		return 0
	}
	return b(n - 1)
}

fun b(n: I32) -> I32 {
	if n <= 0 {
		return 0
	}
	return a(n - 1)
}

fun main() -> I32 {
	return a(2)
}
"#;

        let program = resolve_program(source);
        let reachable =
            reachable_user_functions(&program, "main").expect("collect reachable functions");
        reject_recursion_cycles_with_arg_invariants(
            &program,
            "main",
            &reachable,
            &[],
            "prove verification",
        )
        .expect("call-only recursion should be allowed");
    }

    #[test]
    fn rejects_mixed_cycles_with_argument_invariant_edges() {
        let source = r#"
fun a(n: I32) -> I32 {
	if n <= 0 {
		return id(n)
	}
	return b(n - 1)
}

fun b(n: I32) -> I32 {
	if n <= 0 {
		return n
	}
	return a(n - 1)
}

fun id(v: I32) -> I32 {
	prove(v == v)
	return v
}

fun main() -> I32 {
	return id(2)
}
"#;

        let program = resolve_program(source);
        let reachable =
            reachable_user_functions(&program, "main").expect("collect reachable functions");
        let assumptions = vec![qbe_smt::FunctionArgInvariantAssumption {
            function_name: "id".to_string(),
            arg_index: 0,
            invariant_function_name: "a".to_string(),
        }];
        let err = reject_recursion_cycles_with_arg_invariants(
            &program,
            "main",
            &reachable,
            &assumptions,
            "prove verification",
        )
        .expect_err("mixed call+arg cycle should fail closed");
        assert!(err
            .to_string()
            .contains("includes arg-invariant precondition edges"));
    }
}
