use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::Path;

use anyhow::Context;

use crate::invariant_metadata::{
    build_function_arg_invariant_assumptions_for_names, discover_struct_invariant_bindings,
    InvariantBinding,
};
use crate::ir::ResolvedProgram;
use crate::qbe_backend::INTEGER_SAFETY_MARKER_PREFIX;
use crate::verification_cache::{
    VerificationCacheMode, VerificationCacheWritePolicy, VerificationConfig,
    VerificationSummaryCandidate, VerificationSummaryInput, VerificationSummaryKind,
};
use crate::verification_checker::{
    checker_module_with_reachable_callees, rewrite_returns_to_zero, sanitize_ident,
    should_assume_main_argc_non_negative, summarize_solver_output,
};
use crate::verification_cycles::{
    reachable_user_functions, reject_recursion_cycles_with_arg_invariants,
};
use crate::verification_outcomes::{
    record_outcome, VerificationKind, VerificationOutcome, VerificationOutcomeRecord,
};
use crate::verification_profile::VerificationProfile;
use crate::verification_solver::{format_attempts, solve_chc_with_policy};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum CheckedIntegerType {
    U8,
    I32,
    I64,
    PtrInt,
}

impl CheckedIntegerType {
    fn marker_label(self) -> &'static str {
        match self {
            Self::U8 => "u8",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::PtrInt => "ptrint",
        }
    }

    fn diagnostic_label(self) -> &'static str {
        match self {
            Self::U8 => "U8",
            Self::I32 => "I32",
            Self::I64 => "I64",
            Self::PtrInt => "PtrInt",
        }
    }

    fn qbe_type(self) -> qbe::Type {
        match self {
            Self::U8 | Self::I32 => qbe::Type::Word,
            Self::I64 | Self::PtrInt => qbe::Type::Long,
        }
    }

    fn min_const(self) -> Option<u64> {
        match self {
            Self::U8 => None,
            Self::I32 => Some(i32::MIN as u32 as u64),
            Self::I64 | Self::PtrInt => Some(i64::MIN as u64),
        }
    }

    fn neg_one_const(self) -> Option<u64> {
        match self {
            Self::U8 => None,
            Self::I32 => Some(u32::MAX as u64),
            Self::I64 | Self::PtrInt => Some(u64::MAX),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum CheckedIntegerOp {
    Add,
    Sub,
    Mul,
    Div,
}

impl CheckedIntegerOp {
    fn marker_label(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::Sub => "sub",
            Self::Mul => "mul",
            Self::Div => "div",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct VerificationRoot {
    function_name: String,
    summary_kind: VerificationSummaryKind,
}

#[derive(Clone, Debug)]
struct IntegerSafetySite {
    id: String,
    root_name: String,
    summary_kind: VerificationSummaryKind,
    caller: String,
    integer_type: CheckedIntegerType,
    op: CheckedIntegerOp,
    lhs_marker: String,
    rhs_marker: String,
    out_marker: String,
}

#[derive(Clone, Debug)]
pub(crate) struct PreparedIntegerSafetySite {
    site: IntegerSafetySite,
    qbe_filename: String,
    smt_filename: String,
    smt: String,
}

impl PreparedIntegerSafetySite {
    pub(crate) fn root_name(&self) -> &str {
        &self.site.root_name
    }

    pub(crate) fn summary_kind(&self) -> VerificationSummaryKind {
        self.site.summary_kind
    }

    pub(crate) fn summary_input(&self) -> VerificationSummaryInput {
        VerificationSummaryInput {
            kind: VerificationKind::Prove,
            local_id: self.site.id.clone(),
            smt: self.smt.clone(),
        }
    }
}

#[allow(dead_code)]
pub(crate) fn verify_integer_safety_obligations_with_qbe(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
) -> anyhow::Result<()> {
    verify_integer_safety_obligations_with_qbe_with_profile(
        program,
        qbe_module,
        target_dir,
        VerificationProfile::default(),
    )
}

#[allow(dead_code)]
pub(crate) fn verify_integer_safety_obligations_with_qbe_with_profile(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
    profile: VerificationProfile,
) -> anyhow::Result<()> {
    verify_integer_safety_obligations_with_qbe_with_config(
        program,
        qbe_module,
        target_dir,
        VerificationConfig::new(
            profile,
            VerificationCacheMode::Off,
            target_dir.join("verification_cache"),
            VerificationCacheWritePolicy::PersistUnsat,
        ),
    )
}

pub(crate) fn verify_integer_safety_obligations_with_qbe_with_config(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
    config: VerificationConfig,
) -> anyhow::Result<()> {
    let prepared =
        prepare_integer_safety_obligations_with_config(program, qbe_module, target_dir, &config)?;
    verify_prepared_integer_safety_obligations(&prepared, &config, &HashSet::new())
}

pub(crate) fn prepare_integer_safety_obligations_with_config(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
    _config: &VerificationConfig,
) -> anyhow::Result<Vec<PreparedIntegerSafetySite>> {
    let invariant_by_struct = discover_struct_invariant_bindings(program)?;
    let roots = collect_verification_roots(program, &invariant_by_struct);
    if roots.is_empty() {
        return Ok(Vec::new());
    }

    let function_map = qbe_module
        .functions
        .iter()
        .map(|function| (function.name.clone(), function.clone()))
        .collect::<HashMap<_, _>>();

    let verification_dir = target_dir.join("integer_safety");
    std::fs::create_dir_all(&verification_dir).with_context(|| {
        format!(
            "failed to create integer safety verification directory {}",
            verification_dir.display()
        )
    })?;

    let mut prepared = Vec::new();
    for root in roots {
        let reachable = reachable_user_functions(program, &root.function_name)?;
        let sites = collect_integer_sites(&function_map, &reachable, &root)?;
        if sites.is_empty() {
            continue;
        }

        let reachable_names = reachable.iter().cloned().collect::<BTreeSet<_>>();
        let arg_invariant_assumptions = build_function_arg_invariant_assumptions_for_names(
            program,
            &reachable_names,
            &invariant_by_struct,
        )?;
        reject_recursion_cycles_with_arg_invariants(
            program,
            &root.function_name,
            &reachable,
            &arg_invariant_assumptions,
            "integer safety verification",
        )?;

        for site in sites {
            let (checker_module, checker_function, assumptions) =
                build_site_checker_module(program, &invariant_by_struct, &function_map, &site)?;
            let checker_qbe = checker_module.to_string();
            let site_stem = format!("site_{}", sanitize_ident(&site.id));
            let qbe_filename = format!("{}.qbe", site_stem);
            let smt_filename = format!("{}.smt2", site_stem);

            let qbe_path = verification_dir.join(&qbe_filename);
            std::fs::write(&qbe_path, &checker_qbe).with_context(|| {
                format!(
                    "failed to write integer safety checker QBE program {}",
                    qbe_path.display()
                )
            })?;

            let smt = qbe_smt::qbe_module_to_smt_with_assumptions(
                &checker_module,
                "main",
                &qbe_smt::EncodeOptions {
                    assume_main_argc_non_negative: should_assume_main_argc_non_negative(
                        &site.root_name,
                        &checker_function,
                    ),
                    first_arg_i32_range: None,
                },
                &assumptions,
            )
            .map_err(|err| {
                anyhow::anyhow!(
                    "failed to encode integer safety checker QBE for {}: {}\n{}",
                    site.id,
                    err,
                    err.render_report_plain("integer-safety-checker")
                )
            })?;

            let smt_path = verification_dir.join(&smt_filename);
            std::fs::write(&smt_path, &smt).with_context(|| {
                format!(
                    "failed to write integer safety SMT obligation {}",
                    smt_path.display()
                )
            })?;

            prepared.push(PreparedIntegerSafetySite {
                site,
                qbe_filename,
                smt_filename,
                smt,
            });
        }
    }

    prepared.sort_by(|lhs, rhs| lhs.site.id.cmp(&rhs.site.id));
    Ok(prepared)
}

pub(crate) fn verify_prepared_integer_safety_obligations(
    prepared_sites: &[PreparedIntegerSafetySite],
    config: &VerificationConfig,
    cached_ordinary_roots: &HashSet<String>,
) -> anyhow::Result<()> {
    let model_summaries = build_model_summary_candidates(prepared_sites);
    let mut matched_model_summaries = HashSet::<String>::new();

    if config.cache_reads_enabled() {
        for (root_name, summary) in &model_summaries {
            if summary.matches_persisted_unsat(&config.cache_root)? {
                matched_model_summaries.insert(root_name.clone());
            }
        }
    }

    let mut sat_failures = Vec::new();
    let mut model_roots_with_non_unsat = HashSet::<String>::new();

    for prepared in prepared_sites {
        let trust_skip = match prepared.summary_kind() {
            VerificationSummaryKind::OrdinaryFunction => {
                config.cache_trust_enabled() && cached_ordinary_roots.contains(prepared.root_name())
            }
            VerificationSummaryKind::ModelInvariantFunction => {
                config.cache_trust_enabled()
                    && matched_model_summaries.contains(prepared.root_name())
            }
        };
        if trust_skip {
            record_outcome(VerificationOutcomeRecord {
                kind: VerificationKind::Prove,
                obligation_id: prepared.site.id.clone(),
                caller: prepared.site.caller.clone(),
                callee: None,
                invariant_key: None,
                outcome: VerificationOutcome::Unsat,
                fixture: None,
            });
            continue;
        }

        let strict_cache_mismatch = config.cache_mode == VerificationCacheMode::Strict
            && match prepared.summary_kind() {
                VerificationSummaryKind::OrdinaryFunction => {
                    cached_ordinary_roots.contains(prepared.root_name())
                }
                VerificationSummaryKind::ModelInvariantFunction => {
                    matched_model_summaries.contains(prepared.root_name())
                }
            };

        match solve_chc_with_policy(&prepared.smt, config.profile) {
            Ok(run) if run.final_run.result == qbe_smt::SolverResult::Unsat => {
                record_outcome(VerificationOutcomeRecord {
                    kind: VerificationKind::Prove,
                    obligation_id: prepared.site.id.clone(),
                    caller: prepared.site.caller.clone(),
                    callee: None,
                    invariant_key: None,
                    outcome: verification_outcome_from_solver_result(run.final_run.result),
                    fixture: None,
                });
            }
            Ok(run) if run.final_run.result == qbe_smt::SolverResult::Sat => {
                record_outcome(VerificationOutcomeRecord {
                    kind: VerificationKind::Prove,
                    obligation_id: prepared.site.id.clone(),
                    caller: prepared.site.caller.clone(),
                    callee: None,
                    invariant_key: None,
                    outcome: verification_outcome_from_solver_result(run.final_run.result),
                    fixture: None,
                });
                if prepared.summary_kind() == VerificationSummaryKind::ModelInvariantFunction {
                    model_roots_with_non_unsat.insert(prepared.root_name().to_string());
                }
                let solver_excerpt =
                    summarize_solver_output(&run.final_run.stdout, &run.final_run.stderr)
                        .map(|excerpt| format!(", solver_excerpt={excerpt}"))
                        .unwrap_or_default();
                let cache_excerpt = if strict_cache_mismatch {
                    ", cached_summary_revalidation=mismatch"
                } else {
                    ""
                };
                sat_failures.push(format!(
                    "{} (root={}, caller={}, op={}, semantic_type={}, qbe_artifact={}, smt_artifact={}{}{})",
                    prepared.site.id,
                    prepared.site.root_name,
                    prepared.site.caller,
                    prepared.site.op.marker_label(),
                    prepared.site.integer_type.diagnostic_label(),
                    prepared.qbe_filename,
                    prepared.smt_filename,
                    cache_excerpt,
                    solver_excerpt
                ));
            }
            Ok(run) => {
                record_outcome(VerificationOutcomeRecord {
                    kind: VerificationKind::Prove,
                    obligation_id: prepared.site.id.clone(),
                    caller: prepared.site.caller.clone(),
                    callee: None,
                    invariant_key: None,
                    outcome: verification_outcome_from_solver_result(run.final_run.result),
                    fixture: None,
                });
                if prepared.summary_kind() == VerificationSummaryKind::ModelInvariantFunction {
                    model_roots_with_non_unsat.insert(prepared.root_name().to_string());
                }
                let solver_excerpt =
                    summarize_solver_output(&run.final_run.stdout, &run.final_run.stderr)
                        .map(|excerpt| format!(", solver_excerpt={excerpt}"))
                        .unwrap_or_default();
                let attempts = format_attempts(&run.attempts);
                let cache_excerpt = if strict_cache_mismatch {
                    ", cached_summary_revalidation=mismatch"
                } else {
                    ""
                };
                return Err(anyhow::anyhow!(
                    "solver returned unknown for integer safety obligation {} (root={}, caller={}, op={}, semantic_type={}, qbe_artifact={}, smt_artifact={}, attempts={}{}{}). verification is fail-closed until this obligation is proven unsat",
                    prepared.site.id,
                    prepared.site.root_name,
                    prepared.site.caller,
                    prepared.site.op.marker_label(),
                    prepared.site.integer_type.diagnostic_label(),
                    prepared.qbe_filename,
                    prepared.smt_filename,
                    attempts,
                    cache_excerpt,
                    solver_excerpt
                ));
            }
            Err(err) => {
                return Err(anyhow::anyhow!(
                    "failed to solve integer safety obligation {}: {}\n{}",
                    prepared.site.id,
                    err,
                    err.render_report_plain("integer-safety-obligation")
                ))
            }
        }
    }

    if config.cache_writes_enabled() {
        for (root_name, summary) in &model_summaries {
            if matched_model_summaries.contains(root_name)
                || model_roots_with_non_unsat.contains(root_name)
            {
                continue;
            }
            summary.persist_unsat(&config.cache_root)?;
        }
    }

    if sat_failures.is_empty() {
        Ok(())
    } else {
        Err(anyhow::anyhow!(
            "integer safety verification failed (SAT counterexamples found):\n{}",
            sat_failures.join("\n")
        ))
    }
}

fn build_model_summary_candidates(
    prepared_sites: &[PreparedIntegerSafetySite],
) -> BTreeMap<String, VerificationSummaryCandidate> {
    let mut inputs_by_root = BTreeMap::<String, Vec<VerificationSummaryInput>>::new();
    for prepared in prepared_sites {
        if prepared.summary_kind() != VerificationSummaryKind::ModelInvariantFunction {
            continue;
        }
        inputs_by_root
            .entry(prepared.root_name().to_string())
            .or_default()
            .push(prepared.summary_input());
    }

    inputs_by_root
        .into_iter()
        .map(|(root_name, inputs)| {
            (
                root_name.clone(),
                VerificationSummaryCandidate::from_inputs(
                    &root_name,
                    VerificationSummaryKind::ModelInvariantFunction,
                    &inputs,
                ),
            )
        })
        .collect()
}

fn verification_outcome_from_solver_result(result: qbe_smt::SolverResult) -> VerificationOutcome {
    match result {
        qbe_smt::SolverResult::Sat => VerificationOutcome::Sat,
        qbe_smt::SolverResult::Unsat => VerificationOutcome::Unsat,
        qbe_smt::SolverResult::Unknown => VerificationOutcome::Unknown,
    }
}

fn collect_verification_roots(
    program: &ResolvedProgram,
    invariant_by_struct: &HashMap<String, Vec<InvariantBinding>>,
) -> Vec<VerificationRoot> {
    let mut roots = BTreeSet::<VerificationRoot>::new();
    if program.function_definitions.contains_key("main") {
        roots.insert(VerificationRoot {
            function_name: "main".to_string(),
            summary_kind: VerificationSummaryKind::OrdinaryFunction,
        });
    }
    for function_name in invariant_by_struct.values().flat_map(|bindings| {
        bindings
            .iter()
            .map(|binding| binding.function_name.to_string())
    }) {
        roots.insert(VerificationRoot {
            function_name,
            summary_kind: VerificationSummaryKind::OrdinaryFunction,
        });
    }
    for invariant in &program.model_invariants {
        roots.insert(VerificationRoot {
            function_name: invariant.function_name.clone(),
            summary_kind: VerificationSummaryKind::ModelInvariantFunction,
        });
    }
    roots.into_iter().collect()
}

fn collect_integer_sites(
    function_map: &HashMap<String, qbe::Function>,
    reachable: &HashSet<String>,
    root: &VerificationRoot,
) -> anyhow::Result<Vec<IntegerSafetySite>> {
    let mut functions = reachable.iter().cloned().collect::<Vec<_>>();
    functions.sort();

    let mut sites = Vec::new();
    for function_name in functions {
        let function = function_map
            .get(&function_name)
            .ok_or_else(|| anyhow::anyhow!("missing QBE function {}", function_name))?;
        let partials = collect_function_integer_markers(function)?;
        for partial in partials.into_values() {
            let lhs_marker = partial
                .lhs_marker
                .ok_or_else(|| anyhow::anyhow!("missing lhs marker for {}", partial.base))?;
            let rhs_marker = partial
                .rhs_marker
                .ok_or_else(|| anyhow::anyhow!("missing rhs marker for {}", partial.base))?;
            let out_marker = partial
                .out_marker
                .ok_or_else(|| anyhow::anyhow!("missing out marker for {}", partial.base))?;
            sites.push(IntegerSafetySite {
                id: format!(
                    "{}#{}#{}#{}",
                    root.function_name,
                    function_name,
                    partial.integer_type.marker_label(),
                    partial.base
                ),
                root_name: root.function_name.clone(),
                summary_kind: root.summary_kind,
                caller: function_name.clone(),
                integer_type: partial.integer_type,
                op: partial.op,
                lhs_marker,
                rhs_marker,
                out_marker,
            });
        }
    }

    sites.sort_by(|lhs, rhs| lhs.id.cmp(&rhs.id));
    Ok(sites)
}

#[derive(Clone, Debug)]
struct PartialIntegerSite {
    base: String,
    integer_type: CheckedIntegerType,
    op: CheckedIntegerOp,
    lhs_marker: Option<String>,
    rhs_marker: Option<String>,
    out_marker: Option<String>,
}

fn collect_function_integer_markers(
    function: &qbe::Function,
) -> anyhow::Result<BTreeMap<String, PartialIntegerSite>> {
    let mut sites = BTreeMap::<String, PartialIntegerSite>::new();
    for block in &function.blocks {
        for item in &block.items {
            let qbe::BlockItem::Statement(qbe::Statement::Assign(
                qbe::Value::Temporary(dest),
                _,
                qbe::Instr::Copy(_),
            )) = item
            else {
                continue;
            };
            let Some((base, integer_type, op, suffix)) = parse_marker(dest) else {
                continue;
            };
            let partial = sites
                .entry(base.clone())
                .or_insert_with(|| PartialIntegerSite {
                    base,
                    integer_type,
                    op,
                    lhs_marker: None,
                    rhs_marker: None,
                    out_marker: None,
                });
            if partial.integer_type != integer_type || partial.op != op {
                return Err(anyhow::anyhow!(
                    "conflicting integer safety marker group {} in function {}",
                    partial.base,
                    function.name
                ));
            }
            match suffix {
                "lhs" => partial.lhs_marker = Some(dest.clone()),
                "rhs" => partial.rhs_marker = Some(dest.clone()),
                "out" => partial.out_marker = Some(dest.clone()),
                other => {
                    return Err(anyhow::anyhow!(
                        "unsupported integer safety marker suffix {} in {}",
                        other,
                        function.name
                    ));
                }
            }
        }
    }
    Ok(sites)
}

fn parse_marker(dest: &str) -> Option<(String, CheckedIntegerType, CheckedIntegerOp, &str)> {
    let rest = dest.strip_prefix(INTEGER_SAFETY_MARKER_PREFIX)?;
    let (core, suffix) = rest.rsplit_once("__")?;
    let mut parts = core.split("__");
    let type_label = parts.next()?;
    let op_label = parts.next()?;
    let site_label = parts.next()?;
    if parts.next().is_some() {
        return None;
    }

    let integer_type = match type_label {
        "u8" => CheckedIntegerType::U8,
        "i32" => CheckedIntegerType::I32,
        "i64" => CheckedIntegerType::I64,
        "ptrint" => CheckedIntegerType::PtrInt,
        _ => return None,
    };
    let op = match op_label {
        "add" => CheckedIntegerOp::Add,
        "sub" => CheckedIntegerOp::Sub,
        "mul" => CheckedIntegerOp::Mul,
        "div" => CheckedIntegerOp::Div,
        _ => return None,
    };

    Some((
        format!("{INTEGER_SAFETY_MARKER_PREFIX}{type_label}__{op_label}__{site_label}"),
        integer_type,
        op,
        suffix,
    ))
}

fn build_site_checker_module(
    program: &ResolvedProgram,
    invariant_by_struct: &HashMap<String, Vec<InvariantBinding>>,
    function_map: &HashMap<String, qbe::Function>,
    site: &IntegerSafetySite,
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

fn inject_site_check_and_return(
    function: &mut qbe::Function,
    site: &IntegerSafetySite,
) -> anyhow::Result<()> {
    let mut used_temps = collect_temps_in_function(function);
    let mut target = None;
    for (block_index, block) in function.blocks.iter().enumerate() {
        for item_index in 0..block.items.len() {
            let qbe::BlockItem::Statement(qbe::Statement::Assign(
                qbe::Value::Temporary(dest),
                _,
                qbe::Instr::Copy(_),
            )) = &block.items[item_index]
            else {
                continue;
            };
            if dest != &site.out_marker {
                continue;
            }
            target = Some((block_index, item_index));
            break;
        }
        if target.is_some() {
            break;
        }
    }

    let Some((target_block_index, target_item_index)) = target else {
        return Err(anyhow::anyhow!(
            "failed to locate integer safety marker {} for site {}",
            site.out_marker,
            site.id
        ));
    };

    prune_function_to_target(function, target_block_index);

    let block = &mut function.blocks[target_block_index];
    let mut new_items = block.items[..=target_item_index].to_vec();
    let bad_temp = emit_bad_predicate(&mut new_items, &mut used_temps, site)?;
    new_items.push(qbe::BlockItem::Statement(qbe::Statement::Volatile(
        qbe::Instr::Ret(Some(qbe::Value::Temporary(bad_temp))),
    )));
    block.items = new_items;
    Ok(())
}

fn prune_function_to_target(function: &mut qbe::Function, target_block_index: usize) {
    let keep = blocks_that_can_reach_target(function, target_block_index);
    let mut used_labels = collect_labels_in_function(function);
    let mut prune_label = None::<String>;

    for block_index in 0..function.blocks.len() {
        if !keep.contains(&block_index) || block_index == target_block_index {
            continue;
        }

        let successors = block_successors(function, block_index);
        let fallthrough = block_index + 1;
        let terminator_index = find_terminator_index(&function.blocks[block_index]);

        match terminator_index {
            Some(term_index) => {
                let block = &mut function.blocks[block_index];
                let qbe::BlockItem::Statement(qbe::Statement::Volatile(instr)) =
                    &mut block.items[term_index]
                else {
                    continue;
                };
                match instr {
                    qbe::Instr::Jmp(_label) => {
                        let keep_jump = successors
                            .first()
                            .copied()
                            .map(|successor| keep.contains(&successor))
                            .unwrap_or(false);
                        if !keep_jump {
                            *instr = qbe::Instr::Ret(Some(qbe::Value::Const(0)));
                        }
                    }
                    qbe::Instr::Jnz(_, then_label, else_label) => {
                        let then_kept = successors
                            .first()
                            .copied()
                            .map(|successor| keep.contains(&successor))
                            .unwrap_or(false);
                        let else_kept = successors
                            .get(1)
                            .copied()
                            .map(|successor| keep.contains(&successor))
                            .unwrap_or(false);
                        match (then_kept, else_kept) {
                            (true, true) => {}
                            (false, false) => {
                                *instr = qbe::Instr::Ret(Some(qbe::Value::Const(0)));
                            }
                            (true, false) => {
                                let label = prune_label.get_or_insert_with(|| {
                                    fresh_unique_label("integer_prune", &mut used_labels)
                                });
                                *else_label = label.clone();
                            }
                            (false, true) => {
                                let label = prune_label.get_or_insert_with(|| {
                                    fresh_unique_label("integer_prune", &mut used_labels)
                                });
                                *then_label = label.clone();
                            }
                        }
                    }
                    qbe::Instr::Ret(_) | qbe::Instr::Hlt => {}
                    _ => {}
                }
            }
            None => {
                let block_count = function.blocks.len();
                let block = &mut function.blocks[block_index];
                let falls_to_target = successors
                    .first()
                    .copied()
                    .map(|successor| keep.contains(&successor))
                    .unwrap_or(false);
                if fallthrough >= block_count || !falls_to_target {
                    block
                        .items
                        .push(qbe::BlockItem::Statement(qbe::Statement::Volatile(
                            qbe::Instr::Ret(Some(qbe::Value::Const(0))),
                        )));
                }
            }
        }
    }

    if let Some(label) = prune_label {
        function.blocks.push(qbe::Block {
            label,
            items: vec![qbe::BlockItem::Statement(qbe::Statement::Volatile(
                qbe::Instr::Ret(Some(qbe::Value::Const(0))),
            ))],
        });
    }
}

fn blocks_that_can_reach_target(
    function: &qbe::Function,
    target_block_index: usize,
) -> HashSet<usize> {
    let mut predecessors = vec![Vec::<usize>::new(); function.blocks.len()];
    for block_index in 0..function.blocks.len() {
        for successor in block_successors(function, block_index) {
            predecessors[successor].push(block_index);
        }
    }

    let mut keep = HashSet::<usize>::new();
    let mut queue = vec![target_block_index];
    while let Some(block_index) = queue.pop() {
        if !keep.insert(block_index) {
            continue;
        }
        queue.extend(predecessors[block_index].iter().copied());
    }
    keep
}

fn block_successors(function: &qbe::Function, block_index: usize) -> Vec<usize> {
    let mut label_to_index = HashMap::<String, usize>::new();
    for (index, block) in function.blocks.iter().enumerate() {
        label_to_index.insert(block.label.clone(), index);
    }

    if let Some(term_index) = find_terminator_index(&function.blocks[block_index]) {
        let qbe::BlockItem::Statement(qbe::Statement::Volatile(instr)) =
            &function.blocks[block_index].items[term_index]
        else {
            return Vec::new();
        };
        match instr {
            qbe::Instr::Jmp(label) => label_to_index.get(label).copied().into_iter().collect(),
            qbe::Instr::Jnz(_, then_label, else_label) => {
                let mut out = Vec::new();
                if let Some(index) = label_to_index.get(then_label) {
                    out.push(*index);
                }
                if let Some(index) = label_to_index.get(else_label) {
                    out.push(*index);
                }
                out
            }
            qbe::Instr::Ret(_) | qbe::Instr::Hlt => Vec::new(),
            _ => Vec::new(),
        }
    } else if block_index + 1 < function.blocks.len() {
        vec![block_index + 1]
    } else {
        Vec::new()
    }
}

fn find_terminator_index(block: &qbe::Block) -> Option<usize> {
    block.items.iter().rposition(|item| {
        matches!(
            item,
            qbe::BlockItem::Statement(qbe::Statement::Volatile(
                qbe::Instr::Ret(_)
                    | qbe::Instr::Jmp(_)
                    | qbe::Instr::Jnz(_, _, _)
                    | qbe::Instr::Hlt
            ))
        )
    })
}

fn collect_labels_in_function(function: &qbe::Function) -> HashSet<String> {
    function
        .blocks
        .iter()
        .map(|block| block.label.clone())
        .collect()
}

fn fresh_unique_label(base: &str, used: &mut HashSet<String>) -> String {
    if !used.contains(base) {
        used.insert(base.to_string());
        return base.to_string();
    }
    let mut index = 0usize;
    loop {
        let candidate = format!("{}_{}", base, index);
        if !used.contains(&candidate) {
            used.insert(candidate.clone());
            return candidate;
        }
        index += 1;
    }
}

fn emit_bad_predicate(
    items: &mut Vec<qbe::BlockItem>,
    used_temps: &mut HashSet<String>,
    site: &IntegerSafetySite,
) -> anyhow::Result<String> {
    let safe_temp = match site.integer_type {
        CheckedIntegerType::U8 => emit_u8_safe_predicate(items, used_temps, site),
        CheckedIntegerType::I32 | CheckedIntegerType::I64 | CheckedIntegerType::PtrInt => {
            emit_signed_safe_predicate(items, used_temps, site)?
        }
    };
    Ok(emit_bool_not(items, used_temps, &safe_temp))
}

fn emit_u8_safe_predicate(
    items: &mut Vec<qbe::BlockItem>,
    used_temps: &mut HashSet<String>,
    site: &IntegerSafetySite,
) -> String {
    match site.op {
        CheckedIntegerOp::Add | CheckedIntegerOp::Mul => emit_cmp(
            items,
            used_temps,
            "u8_safe",
            qbe::Type::Word,
            qbe::Cmp::Ule,
            qbe::Value::Temporary(site.out_marker.clone()),
            qbe::Value::Const(255),
        ),
        CheckedIntegerOp::Sub => emit_cmp(
            items,
            used_temps,
            "u8_safe",
            qbe::Type::Word,
            qbe::Cmp::Sge,
            qbe::Value::Temporary(site.out_marker.clone()),
            qbe::Value::Const(0),
        ),
        CheckedIntegerOp::Div => emit_cmp(
            items,
            used_temps,
            "u8_safe",
            qbe::Type::Word,
            qbe::Cmp::Ne,
            qbe::Value::Temporary(site.rhs_marker.clone()),
            qbe::Value::Const(0),
        ),
    }
}

fn emit_signed_safe_predicate(
    items: &mut Vec<qbe::BlockItem>,
    used_temps: &mut HashSet<String>,
    site: &IntegerSafetySite,
) -> anyhow::Result<String> {
    let ty = site.integer_type.qbe_type();
    match site.op {
        CheckedIntegerOp::Add => {
            let rhs_non_negative = emit_cmp(
                items,
                used_temps,
                "rhs_non_negative",
                ty.clone(),
                qbe::Cmp::Sge,
                qbe::Value::Temporary(site.rhs_marker.clone()),
                qbe::Value::Const(0),
            );
            let rhs_negative = emit_cmp(
                items,
                used_temps,
                "rhs_negative",
                ty.clone(),
                qbe::Cmp::Slt,
                qbe::Value::Temporary(site.rhs_marker.clone()),
                qbe::Value::Const(0),
            );
            let result_ge_lhs = emit_cmp(
                items,
                used_temps,
                "result_ge_lhs",
                ty.clone(),
                qbe::Cmp::Sge,
                qbe::Value::Temporary(site.out_marker.clone()),
                qbe::Value::Temporary(site.lhs_marker.clone()),
            );
            let result_lt_lhs = emit_cmp(
                items,
                used_temps,
                "result_lt_lhs",
                ty.clone(),
                qbe::Cmp::Slt,
                qbe::Value::Temporary(site.out_marker.clone()),
                qbe::Value::Temporary(site.lhs_marker.clone()),
            );
            let non_negative_case = emit_bool_or(items, used_temps, &rhs_negative, &result_ge_lhs);
            let negative_case = emit_bool_or(items, used_temps, &rhs_non_negative, &result_lt_lhs);
            Ok(emit_bool_and(
                items,
                used_temps,
                &non_negative_case,
                &negative_case,
            ))
        }
        CheckedIntegerOp::Sub => {
            let rhs_non_negative = emit_cmp(
                items,
                used_temps,
                "rhs_non_negative",
                ty.clone(),
                qbe::Cmp::Sge,
                qbe::Value::Temporary(site.rhs_marker.clone()),
                qbe::Value::Const(0),
            );
            let rhs_negative = emit_cmp(
                items,
                used_temps,
                "rhs_negative",
                ty.clone(),
                qbe::Cmp::Slt,
                qbe::Value::Temporary(site.rhs_marker.clone()),
                qbe::Value::Const(0),
            );
            let result_le_lhs = emit_cmp(
                items,
                used_temps,
                "result_le_lhs",
                ty.clone(),
                qbe::Cmp::Sle,
                qbe::Value::Temporary(site.out_marker.clone()),
                qbe::Value::Temporary(site.lhs_marker.clone()),
            );
            let result_gt_lhs = emit_cmp(
                items,
                used_temps,
                "result_gt_lhs",
                ty.clone(),
                qbe::Cmp::Sgt,
                qbe::Value::Temporary(site.out_marker.clone()),
                qbe::Value::Temporary(site.lhs_marker.clone()),
            );
            let non_negative_case = emit_bool_or(items, used_temps, &rhs_negative, &result_le_lhs);
            let negative_case = emit_bool_or(items, used_temps, &rhs_non_negative, &result_gt_lhs);
            Ok(emit_bool_and(
                items,
                used_temps,
                &non_negative_case,
                &negative_case,
            ))
        }
        CheckedIntegerOp::Mul => emit_signed_mul_safe_predicate(items, used_temps, site),
        CheckedIntegerOp::Div => Ok(emit_signed_div_safe_predicate(items, used_temps, site)?),
    }
}

fn emit_signed_mul_safe_predicate(
    items: &mut Vec<qbe::BlockItem>,
    used_temps: &mut HashSet<String>,
    site: &IntegerSafetySite,
) -> anyhow::Result<String> {
    let ty = site.integer_type.qbe_type();
    let neg_one = site
        .integer_type
        .neg_one_const()
        .ok_or_else(|| anyhow::anyhow!("missing neg-one constant for {}", site.id))?;
    let min_value = site
        .integer_type
        .min_const()
        .ok_or_else(|| anyhow::anyhow!("missing min constant for {}", site.id))?;

    let lhs_zero = emit_cmp(
        items,
        used_temps,
        "lhs_zero",
        ty.clone(),
        qbe::Cmp::Eq,
        qbe::Value::Temporary(site.lhs_marker.clone()),
        qbe::Value::Const(0),
    );
    let rhs_zero = emit_cmp(
        items,
        used_temps,
        "rhs_zero",
        ty.clone(),
        qbe::Cmp::Eq,
        qbe::Value::Temporary(site.rhs_marker.clone()),
        qbe::Value::Const(0),
    );
    let lhs_neg_one = emit_cmp(
        items,
        used_temps,
        "lhs_neg_one",
        ty.clone(),
        qbe::Cmp::Eq,
        qbe::Value::Temporary(site.lhs_marker.clone()),
        qbe::Value::Const(neg_one),
    );
    let rhs_neg_one = emit_cmp(
        items,
        used_temps,
        "rhs_neg_one",
        ty.clone(),
        qbe::Cmp::Eq,
        qbe::Value::Temporary(site.rhs_marker.clone()),
        qbe::Value::Const(neg_one),
    );
    let lhs_is_min = emit_cmp(
        items,
        used_temps,
        "lhs_is_min",
        ty.clone(),
        qbe::Cmp::Eq,
        qbe::Value::Temporary(site.lhs_marker.clone()),
        qbe::Value::Const(min_value),
    );
    let rhs_is_min = emit_cmp(
        items,
        used_temps,
        "rhs_is_min",
        ty.clone(),
        qbe::Cmp::Eq,
        qbe::Value::Temporary(site.rhs_marker.clone()),
        qbe::Value::Const(min_value),
    );
    let rhs_not_min = emit_bool_not(items, used_temps, &rhs_is_min);
    let lhs_not_min = emit_bool_not(items, used_temps, &lhs_is_min);
    let lhs_neg_one_case = emit_bool_and(items, used_temps, &lhs_neg_one, &rhs_not_min);
    let rhs_neg_one_case = emit_bool_and(items, used_temps, &rhs_neg_one, &lhs_not_min);

    let rhs_non_zero = emit_cmp(
        items,
        used_temps,
        "rhs_non_zero",
        ty.clone(),
        qbe::Cmp::Ne,
        qbe::Value::Temporary(site.rhs_marker.clone()),
        qbe::Value::Const(0),
    );
    let min_div_overflow = emit_bool_and(items, used_temps, &lhs_is_min, &rhs_neg_one);
    let div_allowed = emit_bool_not(items, used_temps, &min_div_overflow);
    let div_guard = emit_bool_and(items, used_temps, &rhs_non_zero, &div_allowed);

    let div_temp = fresh_unique_temp("mul_div", used_temps);
    items.push(qbe::BlockItem::Statement(qbe::Statement::Assign(
        qbe::Value::Temporary(div_temp.clone()),
        ty.clone(),
        qbe::Instr::Div(
            qbe::Value::Temporary(site.out_marker.clone()),
            qbe::Value::Temporary(site.rhs_marker.clone()),
        ),
    )));
    let div_matches = emit_cmp(
        items,
        used_temps,
        "div_matches",
        ty,
        qbe::Cmp::Eq,
        qbe::Value::Temporary(div_temp),
        qbe::Value::Temporary(site.lhs_marker.clone()),
    );
    let guarded_div_case = emit_bool_and(items, used_temps, &div_guard, &div_matches);

    let zero_case = emit_bool_or(items, used_temps, &lhs_zero, &rhs_zero);
    let neg_one_case = emit_bool_or(items, used_temps, &lhs_neg_one_case, &rhs_neg_one_case);
    let zero_or_neg_one_case = emit_bool_or(items, used_temps, &zero_case, &neg_one_case);
    Ok(emit_bool_or(
        items,
        used_temps,
        &zero_or_neg_one_case,
        &guarded_div_case,
    ))
}

fn emit_signed_div_safe_predicate(
    items: &mut Vec<qbe::BlockItem>,
    used_temps: &mut HashSet<String>,
    site: &IntegerSafetySite,
) -> anyhow::Result<String> {
    let ty = site.integer_type.qbe_type();
    let neg_one = site
        .integer_type
        .neg_one_const()
        .ok_or_else(|| anyhow::anyhow!("missing neg-one constant for {}", site.id))?;
    let min_value = site
        .integer_type
        .min_const()
        .ok_or_else(|| anyhow::anyhow!("missing min constant for {}", site.id))?;

    let rhs_non_zero = emit_cmp(
        items,
        used_temps,
        "rhs_non_zero",
        ty.clone(),
        qbe::Cmp::Ne,
        qbe::Value::Temporary(site.rhs_marker.clone()),
        qbe::Value::Const(0),
    );
    let lhs_is_min = emit_cmp(
        items,
        used_temps,
        "lhs_is_min",
        ty.clone(),
        qbe::Cmp::Eq,
        qbe::Value::Temporary(site.lhs_marker.clone()),
        qbe::Value::Const(min_value),
    );
    let rhs_is_neg_one = emit_cmp(
        items,
        used_temps,
        "rhs_is_neg_one",
        ty,
        qbe::Cmp::Eq,
        qbe::Value::Temporary(site.rhs_marker.clone()),
        qbe::Value::Const(neg_one),
    );
    let overflow_case = emit_bool_and(items, used_temps, &lhs_is_min, &rhs_is_neg_one);
    let overflow_safe = emit_bool_not(items, used_temps, &overflow_case);
    Ok(emit_bool_and(
        items,
        used_temps,
        &rhs_non_zero,
        &overflow_safe,
    ))
}

fn emit_cmp(
    items: &mut Vec<qbe::BlockItem>,
    used_temps: &mut HashSet<String>,
    base: &str,
    ty: qbe::Type,
    cmp: qbe::Cmp,
    lhs: qbe::Value,
    rhs: qbe::Value,
) -> String {
    let temp = fresh_unique_temp(base, used_temps);
    items.push(qbe::BlockItem::Statement(qbe::Statement::Assign(
        qbe::Value::Temporary(temp.clone()),
        qbe::Type::Word,
        qbe::Instr::Cmp(ty, cmp, lhs, rhs),
    )));
    temp
}

fn emit_bool_not(
    items: &mut Vec<qbe::BlockItem>,
    used_temps: &mut HashSet<String>,
    input: &str,
) -> String {
    emit_cmp(
        items,
        used_temps,
        "bool_not",
        qbe::Type::Word,
        qbe::Cmp::Eq,
        qbe::Value::Temporary(input.to_string()),
        qbe::Value::Const(0),
    )
}

fn emit_bool_and(
    items: &mut Vec<qbe::BlockItem>,
    used_temps: &mut HashSet<String>,
    lhs: &str,
    rhs: &str,
) -> String {
    let temp = fresh_unique_temp("bool_and", used_temps);
    items.push(qbe::BlockItem::Statement(qbe::Statement::Assign(
        qbe::Value::Temporary(temp.clone()),
        qbe::Type::Word,
        qbe::Instr::And(
            qbe::Value::Temporary(lhs.to_string()),
            qbe::Value::Temporary(rhs.to_string()),
        ),
    )));
    temp
}

fn emit_bool_or(
    items: &mut Vec<qbe::BlockItem>,
    used_temps: &mut HashSet<String>,
    lhs: &str,
    rhs: &str,
) -> String {
    let temp = fresh_unique_temp("bool_or", used_temps);
    items.push(qbe::BlockItem::Statement(qbe::Statement::Assign(
        qbe::Value::Temporary(temp.clone()),
        qbe::Type::Word,
        qbe::Instr::Or(
            qbe::Value::Temporary(lhs.to_string()),
            qbe::Value::Temporary(rhs.to_string()),
        ),
    )));
    temp
}

fn collect_temps_in_function(function: &qbe::Function) -> HashSet<String> {
    let mut out = HashSet::new();
    for (_, value) in &function.arguments {
        collect_temp_from_value(value, &mut out);
    }
    for block in &function.blocks {
        for item in &block.items {
            if let qbe::BlockItem::Statement(statement) = item {
                collect_temps_from_statement(statement, &mut out);
            }
        }
    }
    out
}

fn collect_temps_from_statement(statement: &qbe::Statement, out: &mut HashSet<String>) {
    match statement {
        qbe::Statement::Assign(dest, _, instr) => {
            collect_temp_from_value(dest, out);
            collect_temps_from_instr(instr, out);
        }
        qbe::Statement::Volatile(instr) => {
            collect_temps_from_instr(instr, out);
        }
    }
}

fn collect_temps_from_instr(instr: &qbe::Instr, out: &mut HashSet<String>) {
    use qbe::Instr;

    match instr {
        Instr::Add(lhs, rhs)
        | Instr::Sub(lhs, rhs)
        | Instr::Mul(lhs, rhs)
        | Instr::Div(lhs, rhs)
        | Instr::Rem(lhs, rhs)
        | Instr::And(lhs, rhs)
        | Instr::Or(lhs, rhs)
        | Instr::Udiv(lhs, rhs)
        | Instr::Urem(lhs, rhs)
        | Instr::Sar(lhs, rhs)
        | Instr::Shr(lhs, rhs)
        | Instr::Shl(lhs, rhs) => {
            collect_temp_from_value(lhs, out);
            collect_temp_from_value(rhs, out);
        }
        Instr::Cmp(_, _, lhs, rhs) => {
            collect_temp_from_value(lhs, out);
            collect_temp_from_value(rhs, out);
        }
        Instr::Copy(value)
        | Instr::Cast(value)
        | Instr::Extsw(value)
        | Instr::Extuw(value)
        | Instr::Extsh(value)
        | Instr::Extuh(value)
        | Instr::Extsb(value)
        | Instr::Extub(value)
        | Instr::Exts(value)
        | Instr::Truncd(value)
        | Instr::Stosi(value)
        | Instr::Stoui(value)
        | Instr::Dtosi(value)
        | Instr::Dtoui(value)
        | Instr::Swtof(value)
        | Instr::Uwtof(value)
        | Instr::Sltof(value)
        | Instr::Ultof(value)
        | Instr::Vastart(value) => {
            collect_temp_from_value(value, out);
        }
        Instr::Ret(value) => {
            if let Some(value) = value {
                collect_temp_from_value(value, out);
            }
        }
        Instr::Jnz(value, _, _) => {
            collect_temp_from_value(value, out);
        }
        Instr::Call(_, args, _) => {
            for (_, value) in args {
                collect_temp_from_value(value, out);
            }
        }
        Instr::Store(_, destination, value) => {
            collect_temp_from_value(destination, out);
            collect_temp_from_value(value, out);
        }
        Instr::Load(_, source) => {
            collect_temp_from_value(source, out);
        }
        Instr::Blit(source, destination, _) => {
            collect_temp_from_value(source, out);
            collect_temp_from_value(destination, out);
        }
        Instr::Vaarg(_, value) => {
            collect_temp_from_value(value, out);
        }
        Instr::Phi(_, left, _, right) => {
            collect_temp_from_value(left, out);
            collect_temp_from_value(right, out);
        }
        Instr::Jmp(_)
        | Instr::Alloc4(_)
        | Instr::Alloc8(_)
        | Instr::Alloc16(_)
        | Instr::DbgFile(_)
        | Instr::DbgLoc(_, _)
        | Instr::Hlt => {}
    }
}

fn collect_temp_from_value(value: &qbe::Value, out: &mut HashSet<String>) {
    if let qbe::Value::Temporary(name) = value {
        out.insert(name.clone());
    }
}

fn fresh_unique_temp(base: &str, used: &mut HashSet<String>) -> String {
    if !used.contains(base) {
        used.insert(base.to_string());
        return base.to_string();
    }
    let mut index = 0usize;
    loop {
        let candidate = format!("{}_{}", base, index);
        if !used.contains(&candidate) {
            used.insert(candidate.clone());
            return candidate;
        }
        index += 1;
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::prepare_integer_safety_obligations_with_config;
    use crate::verification_cache::{
        VerificationCacheMode, VerificationCacheWritePolicy, VerificationConfig,
    };
    use crate::verification_profile::VerificationProfile;
    use crate::{ir, parser, qbe_backend, tokenizer};

    fn resolve_program(source: &str) -> ir::ResolvedProgram {
        let tokens = tokenizer::tokenize(source.to_string()).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        ir::resolve(ast).expect("resolve source")
    }

    fn config(root: &std::path::Path) -> VerificationConfig {
        VerificationConfig::new(
            VerificationProfile::Candidate,
            VerificationCacheMode::Off,
            root.join("verification_cache"),
            VerificationCacheWritePolicy::PersistUnsat,
        )
    }

    #[test]
    fn prepare_collects_reachable_integer_sites() {
        let mut program = resolve_program(
            r#"
fun helper(v: I32) -> I32 {
	return v + 1
}

fun main() -> I32 {
	return helper(41)
}
"#,
        );
        program.model_invariants.clear();
        program.struct_invariants.clear();
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");

        let prepared = prepare_integer_safety_obligations_with_config(
            &program,
            &qbe_module,
            tempdir.path(),
            &config(tempdir.path()),
        )
        .expect("prepare integer safety obligations");

        assert_eq!(prepared.len(), 1);
        assert_eq!(prepared[0].root_name(), "main");
        assert_eq!(prepared[0].site.caller, "helper");
        assert_eq!(
            prepared[0].summary_kind(),
            crate::verification_cache::VerificationSummaryKind::OrdinaryFunction
        );
    }

    #[test]
    fn checker_injection_returns_bad_predicate() {
        let mut program = resolve_program(
            r#"
fun main() -> I32 {
	x = 1 + 2
	return x
}
"#,
        );
        program.model_invariants.clear();
        program.struct_invariants.clear();
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");

        let prepared = prepare_integer_safety_obligations_with_config(
            &program,
            &qbe_module,
            tempdir.path(),
            &config(tempdir.path()),
        )
        .expect("prepare integer safety obligations");

        let qbe_path = tempdir
            .path()
            .join("integer_safety")
            .join(&prepared[0].qbe_filename);
        let qbe_text = fs::read_to_string(&qbe_path).expect("read checker qbe");
        assert!(qbe_text.contains("ret %"));
        assert!(!qbe_text.contains("call $exit"));
    }
}
