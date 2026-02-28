use std::collections::{HashMap, HashSet};
use std::path::Path;

use crate::ir::ResolvedProgram;
use crate::qbe_backend::PROVE_MARKER_PREFIX;

pub(crate) const PROVE_BATCH_CONFIG: crate::verification::ObligationBatchConfig<'static> =
    crate::verification::ObligationBatchConfig {
        verification_subdir: "prove",
        create_dir_error_prefix: "failed to create prove verification directory",
        write_qbe_error_prefix: "failed to write prove checker QBE program",
        write_smt_error_prefix: "failed to write prove SMT obligation",
        encode_error_prefix: "failed to encode prove checker QBE for",
        encode_report_name: "prove-checker",
        unknown_error_prefix: "solver returned unknown for prove obligation",
        solve_error_prefix: "failed to solve prove obligation",
        solve_report_name: "prove-obligation",
        sat_failure_header: "prove verification failed (SAT counterexamples found):",
    };

#[derive(Clone, Debug)]
pub(crate) struct ProveSite {
    pub(crate) id: String,
    pub(crate) caller: String,
    pub(crate) marker_temp: String,
}

#[allow(dead_code)]
pub fn verify_prove_obligations_with_qbe(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
) -> anyhow::Result<()> {
    let context = crate::verification::build_verification_context(program, qbe_module)?;
    let sites = collect_prove_sites(&context.function_map, &context.reachable)?;
    if sites.is_empty() {
        return Ok(());
    }

    crate::verification::reject_recursion_cycles(
        program,
        "main",
        &context.reachable,
        "prove verification",
    )?;
    crate::verification::run_obligation_batch(
        &context.function_map,
        &sites,
        target_dir,
        &PROVE_BATCH_CONFIG,
        |site| site.id.as_str(),
        build_site_checker_function,
        should_assume_main_argc_non_negative,
        format_sat_failure,
    )
}

pub(crate) fn collect_prove_sites(
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

pub(crate) fn format_sat_failure(
    site: &ProveSite,
    _checker: &qbe::Function,
    qbe_filename: &str,
    smt_filename: &str,
    run: &qbe_smt::SolverRun,
) -> String {
    let solver_excerpt = crate::verification::summarize_solver_output(&run.stdout, &run.stderr)
        .map(|excerpt| format!(", solver_excerpt={excerpt}"))
        .unwrap_or_default();
    let mut failure = format!(
        "{} (caller={}, qbe_artifact={}, smt_artifact={}",
        site.id, site.caller, qbe_filename, smt_filename
    );
    failure.push_str(&solver_excerpt);
    failure.push(')');
    failure
}

pub(crate) fn build_site_checker_function(
    function_map: &HashMap<String, qbe::Function>,
    site: &ProveSite,
) -> anyhow::Result<qbe::Function> {
    let caller = function_map
        .get(&site.caller)
        .ok_or_else(|| anyhow::anyhow!("missing QBE function for caller {}", site.caller))?;
    let mut checker = caller.clone();
    checker.name = "main".to_string();
    checker.linkage = qbe::Linkage::private();
    checker.return_ty = Some(qbe::Type::Word);

    rewrite_returns_to_zero(&mut checker);
    inject_site_check_and_return(&mut checker, site)?;
    crate::struct_invariants::inline_reachable_user_calls(&mut checker, function_map)?;

    Ok(checker)
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

pub(crate) fn should_assume_main_argc_non_negative(
    site: &ProveSite,
    checker: &qbe::Function,
) -> bool {
    if site.caller != "main" {
        return false;
    }
    if checker.arguments.len() != 2 {
        return false;
    }
    matches!(checker.arguments[0].0, qbe::Type::Word)
        && matches!(checker.arguments[1].0, qbe::Type::Long)
}

#[cfg(test)]
mod tests {
    use crate::{ir, parser, qbe_backend, tokenizer};

    use super::verify_prove_obligations_with_qbe;

    #[test]
    fn no_prove_sites_is_noop() {
        let source = r#"
fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let tokens = tokenizer::tokenize(source).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let program = ir::resolve(ast).expect("resolve source");
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        verify_prove_obligations_with_qbe(&program, &qbe_module, tempdir.path())
            .expect("no prove obligations should pass");
    }
}
