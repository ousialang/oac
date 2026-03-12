use std::collections::{BTreeMap, HashSet};
use std::path::Path;

use crate::ir::ResolvedProgram;
use crate::verification_cache::{
    VerificationConfig, VerificationSummaryCandidate, VerificationSummaryInput,
    VerificationSummaryKind,
};

#[derive(Debug)]
pub enum VerificationError {
    Precondition(anyhow::Error),
    Prove(anyhow::Error),
    StructInvariant(anyhow::Error),
    ModelInvariant(anyhow::Error),
}

pub(crate) struct OrdinaryVerificationSession {
    prepared_preconditions: Vec<crate::function_preconditions::PreparedFunctionPreconditionSite>,
    prepared_prove: Vec<crate::prove::PreparedProveSite>,
    prepared_integer: Vec<crate::integer_safety::PreparedIntegerSafetySite>,
    prepared_struct: Vec<crate::struct_invariants::PreparedStructInvariantSite>,
    cached_roots: HashSet<String>,
    uncached_summaries: Vec<VerificationSummaryCandidate>,
}

impl OrdinaryVerificationSession {
    fn prepare(
        program: &ResolvedProgram,
        qbe_module: &qbe::Module,
        target_dir: &Path,
        config: &VerificationConfig,
    ) -> Result<Self, VerificationError> {
        let prepared_preconditions =
            crate::function_preconditions::prepare_function_preconditions_with_config(
                program, qbe_module, target_dir, config,
            )
            .map_err(VerificationError::Precondition)?;
        let prepared_prove = crate::prove::prepare_prove_obligations_with_config(
            program, qbe_module, target_dir, config,
        )
        .map_err(VerificationError::Prove)?;
        let prepared_integer =
            crate::integer_safety::prepare_integer_safety_obligations_with_config(
                program, qbe_module, target_dir, config,
            )
            .map_err(VerificationError::Prove)?;
        let prepared_struct =
            crate::struct_invariants::prepare_struct_invariant_obligations_with_config(
                program, qbe_module, target_dir, config,
            )
            .map_err(VerificationError::StructInvariant)?;

        let mut inputs_by_root = BTreeMap::<String, Vec<VerificationSummaryInput>>::new();
        for prepared in &prepared_preconditions {
            if prepared.summary_kind() != VerificationSummaryKind::OrdinaryFunction {
                continue;
            }
            inputs_by_root
                .entry(prepared.root_name().to_string())
                .or_default()
                .push(prepared.summary_input());
        }
        for prepared in &prepared_prove {
            inputs_by_root
                .entry(prepared.caller().to_string())
                .or_default()
                .push(prepared.summary_input());
        }
        for prepared in &prepared_integer {
            if prepared.summary_kind() != VerificationSummaryKind::OrdinaryFunction {
                continue;
            }
            inputs_by_root
                .entry(prepared.root_name().to_string())
                .or_default()
                .push(prepared.summary_input());
        }
        for prepared in &prepared_struct {
            inputs_by_root
                .entry(prepared.caller().to_string())
                .or_default()
                .push(prepared.summary_input());
        }

        let mut cached_roots = HashSet::new();
        let mut uncached_summaries = Vec::new();
        for (root_name, inputs) in inputs_by_root {
            let candidate = VerificationSummaryCandidate::from_inputs(
                &root_name,
                VerificationSummaryKind::OrdinaryFunction,
                &inputs,
            );
            let cache_match = if config.cache_reads_enabled() {
                candidate
                    .matches_persisted_unsat(&config.cache_root)
                    .map_err(VerificationError::StructInvariant)?
            } else {
                false
            };
            if cache_match {
                cached_roots.insert(root_name);
            } else {
                uncached_summaries.push(candidate);
            }
        }

        Ok(Self {
            prepared_preconditions,
            prepared_prove,
            prepared_integer,
            prepared_struct,
            cached_roots,
            uncached_summaries,
        })
    }

    pub(crate) fn verify_prove_stage(
        &self,
        config: &VerificationConfig,
    ) -> Result<(), VerificationError> {
        crate::function_preconditions::verify_prepared_function_preconditions(
            &self.prepared_preconditions,
            config,
            &self.cached_roots,
        )
        .map_err(VerificationError::Precondition)?;
        crate::prove::verify_prepared_prove_obligations(
            &self.prepared_prove,
            config,
            &self.cached_roots,
        )
        .map_err(VerificationError::Prove)?;
        crate::integer_safety::verify_prepared_integer_safety_obligations(
            &self.prepared_integer,
            config,
            &self.cached_roots,
        )
        .map_err(VerificationError::Prove)
    }

    pub(crate) fn verify_struct_stage(
        &self,
        config: &VerificationConfig,
    ) -> Result<(), VerificationError> {
        crate::struct_invariants::verify_prepared_struct_invariant_obligations(
            &self.prepared_struct,
            config,
            &self.cached_roots,
        )
        .map_err(VerificationError::StructInvariant)?;

        if config.cache_writes_enabled() {
            for summary in &self.uncached_summaries {
                summary
                    .persist_unsat(&config.cache_root)
                    .map_err(VerificationError::StructInvariant)?;
            }
        }

        Ok(())
    }
}

pub(crate) fn prepare_ordinary_verification_session(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
    config: &VerificationConfig,
) -> Result<OrdinaryVerificationSession, VerificationError> {
    OrdinaryVerificationSession::prepare(program, qbe_module, target_dir, config)
}

pub(crate) fn verify_model_stage(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
    config: &VerificationConfig,
) -> Result<(), VerificationError> {
    crate::model_invariants::verify_model_invariants_with_qbe_with_config(
        program,
        qbe_module,
        target_dir,
        config.clone(),
    )
    .map_err(VerificationError::ModelInvariant)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::prepare_ordinary_verification_session;
    use crate::verification_cache::{
        VerificationCacheMode, VerificationCacheWritePolicy, VerificationConfig,
        VerificationSummaryFile,
    };
    use crate::verification_profile::VerificationProfile;
    use crate::verification_solver::test_support;
    use crate::{ir, parser, qbe_backend, tokenizer};

    fn resolve_program(source: &str) -> ir::ResolvedProgram {
        let tokens = tokenizer::tokenize(source.to_string()).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        ir::resolve(ast).expect("resolve source")
    }

    fn run(result: qbe_smt::SolverResult, stdout: &str, stderr: &str) -> qbe_smt::SolverRun {
        qbe_smt::SolverRun {
            result,
            stdout: stdout.to_string(),
            stderr: stderr.to_string(),
        }
    }

    fn ordinary_root_source() -> &'static str {
        r#"
struct Counter {
	value: I32,
}

invariant positive_value "counter value must be non-negative" for (v: Counter) {
	return v.value >= 0
}

fun make_counter() -> Counter {
	return Counter struct { value: 7, }
}

fun main() -> I32 {
	counter = make_counter()
	prove(counter.value >= 0)
	return 0
}
"#
    }

    fn config(root: &std::path::Path, mode: VerificationCacheMode) -> VerificationConfig {
        VerificationConfig::new(
            VerificationProfile::Candidate,
            mode,
            root.join("verification_cache"),
            VerificationCacheWritePolicy::PersistUnsat,
        )
    }

    fn ordinary_cache_entry_count(cache_root: &std::path::Path) -> usize {
        let dir = cache_root.join("ordinary_function").join("main");
        if !dir.exists() {
            return 0;
        }
        fs::read_dir(dir)
            .expect("read ordinary function cache dir")
            .filter_map(|entry| entry.ok().map(|entry| entry.path()))
            .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("json"))
            .count()
    }

    fn load_ordinary_summary(cache_root: &std::path::Path) -> VerificationSummaryFile {
        let dir = cache_root.join("ordinary_function").join("main");
        let path = fs::read_dir(&dir)
            .expect("read ordinary function cache dir")
            .filter_map(|entry| entry.ok().map(|entry| entry.path()))
            .find(|path| path.extension().and_then(|ext| ext.to_str()) == Some("json"))
            .expect("ordinary summary cache entry");
        let raw = fs::read_to_string(&path).expect("read ordinary summary cache file");
        serde_json::from_str(&raw).expect("parse ordinary summary cache file")
    }

    #[test]
    fn ordinary_summary_cache_trust_hit_skips_solver() {
        let mut program = resolve_program(ordinary_root_source());
        program.model_invariants.clear();
        program
            .struct_invariants
            .retain(|name, _| name == "Counter");
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        let config = config(tempdir.path(), VerificationCacheMode::Trust);

        let first_session =
            prepare_ordinary_verification_session(&program, &qbe_module, tempdir.path(), &config)
                .expect("prepare first session");
        let first_stage_solver_runs = first_session.prepared_preconditions.len()
            + first_session.prepared_prove.len()
            + first_session.prepared_integer.len()
            + first_session.prepared_struct.len();
        test_support::with_mock_solver_runs(
            std::iter::repeat_with(|| Ok(run(qbe_smt::SolverResult::Unsat, "unsat", "")))
                .take(first_stage_solver_runs)
                .collect(),
            || {
                first_session
                    .verify_prove_stage(&config)
                    .expect("prove stage should succeed");
                first_session
                    .verify_struct_stage(&config)
                    .expect("struct stage should succeed");
                assert_eq!(
                    test_support::observed_timeouts().len(),
                    first_stage_solver_runs
                );
            },
        );
        assert_eq!(ordinary_cache_entry_count(&config.cache_root), 1);

        let second_session =
            prepare_ordinary_verification_session(&program, &qbe_module, tempdir.path(), &config)
                .expect("prepare cached session");
        test_support::with_mock_solver_runs(vec![], || {
            second_session
                .verify_prove_stage(&config)
                .expect("prove stage should trust cached summary");
            second_session
                .verify_struct_stage(&config)
                .expect("struct stage should trust cached summary");
            assert!(
                test_support::observed_timeouts().is_empty(),
                "cached trust mode should skip solver invocations"
            );
        });
    }

    #[test]
    fn ordinary_summary_cache_strict_mismatch_fails_closed() {
        let mut program = resolve_program(ordinary_root_source());
        program.model_invariants.clear();
        program
            .struct_invariants
            .retain(|name, _| name == "Counter");
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        let trust_config = config(tempdir.path(), VerificationCacheMode::Trust);

        let warm_session = prepare_ordinary_verification_session(
            &program,
            &qbe_module,
            tempdir.path(),
            &trust_config,
        )
        .expect("prepare warm session");
        let warm_stage_solver_runs = warm_session.prepared_preconditions.len()
            + warm_session.prepared_prove.len()
            + warm_session.prepared_integer.len()
            + warm_session.prepared_struct.len();
        test_support::with_mock_solver_runs(
            std::iter::repeat_with(|| Ok(run(qbe_smt::SolverResult::Unsat, "unsat", "")))
                .take(warm_stage_solver_runs)
                .collect(),
            || {
                warm_session
                    .verify_prove_stage(&trust_config)
                    .expect("prove stage should succeed");
                warm_session
                    .verify_struct_stage(&trust_config)
                    .expect("struct stage should succeed");
            },
        );

        let strict_config = config(tempdir.path(), VerificationCacheMode::Strict);
        let strict_session = prepare_ordinary_verification_session(
            &program,
            &qbe_module,
            tempdir.path(),
            &strict_config,
        )
        .expect("prepare strict session");
        let strict_prove_stage_solver_runs = strict_session.prepared_preconditions.len()
            + strict_session.prepared_prove.len()
            + strict_session.prepared_integer.len();
        test_support::with_mock_solver_runs(
            std::iter::repeat_with(|| Ok(run(qbe_smt::SolverResult::Sat, "sat", "")))
                .take(strict_prove_stage_solver_runs.max(1))
                .collect(),
            || {
                let err = strict_session
                    .verify_prove_stage(&strict_config)
                    .expect_err("strict revalidation mismatch must fail");
                assert!(
                    match err {
                        super::VerificationError::Prove(err) => err
                            .to_string()
                            .contains("cached_summary_revalidation=mismatch"),
                        _ => false,
                    },
                    "strict mismatch should be reported in the prove-stage error"
                );
            },
        );
    }

    #[test]
    fn ordinary_summary_cache_never_persists_non_unsat_results() {
        let mut program = resolve_program(ordinary_root_source());
        program.model_invariants.clear();
        program
            .struct_invariants
            .retain(|name, _| name == "Counter");
        let qbe_module = qbe_backend::compile(program.clone());
        let outcomes = [qbe_smt::SolverResult::Sat, qbe_smt::SolverResult::Unknown];

        for outcome in outcomes {
            let tempdir = tempfile::tempdir().expect("tempdir");
            let config = config(tempdir.path(), VerificationCacheMode::Trust);
            let session = prepare_ordinary_verification_session(
                &program,
                &qbe_module,
                tempdir.path(),
                &config,
            )
            .expect("prepare session");
            let mocked = match outcome {
                qbe_smt::SolverResult::Sat => vec![Ok(run(qbe_smt::SolverResult::Sat, "sat", ""))],
                qbe_smt::SolverResult::Unknown => vec![
                    Ok(run(
                        qbe_smt::SolverResult::Unknown,
                        "unknown\n(reason-unknown timeout)",
                        "",
                    )),
                    Ok(run(
                        qbe_smt::SolverResult::Unknown,
                        "unknown\n(reason-unknown timeout)",
                        "",
                    )),
                    Ok(run(
                        qbe_smt::SolverResult::Unknown,
                        "unknown\n(reason-unknown timeout)",
                        "",
                    )),
                ],
                qbe_smt::SolverResult::Unsat => unreachable!("only non-unsat cases are tested"),
            };
            test_support::with_mock_solver_runs(mocked, || {
                let _ = session.verify_prove_stage(&config);
            });
            assert_eq!(
                ordinary_cache_entry_count(&config.cache_root),
                0,
                "non-unsat prove results must not populate the ordinary summary cache"
            );
        }
    }

    #[test]
    fn ordinary_summary_includes_integer_obligations() {
        let mut program = resolve_program(
            r#"
fun main() -> I32 {
	x = 1 + 2
	prove(x == 3)
	return x
}
"#,
        );
        program.model_invariants.clear();
        program.struct_invariants.clear();
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        let config = config(tempdir.path(), VerificationCacheMode::Trust);
        let session =
            prepare_ordinary_verification_session(&program, &qbe_module, tempdir.path(), &config)
                .expect("prepare session");

        test_support::with_mock_solver_runs(
            vec![
                Ok(run(qbe_smt::SolverResult::Unsat, "unsat", "")),
                Ok(run(qbe_smt::SolverResult::Unsat, "unsat", "")),
                Ok(run(qbe_smt::SolverResult::Unsat, "unsat", "")),
            ],
            || {
                session
                    .verify_prove_stage(&config)
                    .expect("prove stage should succeed");
                session
                    .verify_struct_stage(&config)
                    .expect("struct stage should persist the summary");
            },
        );

        let summary = load_ordinary_summary(&config.cache_root);
        assert_eq!(summary.obligations.len(), 2);
        assert!(summary
            .obligations
            .iter()
            .any(|obligation| obligation.local_id.contains(".oac_integer_site_i32__add__")));
        assert!(summary.obligations.iter().any(|obligation| matches!(
            obligation.kind,
            crate::verification_outcomes::VerificationKind::Prove
        ) && !obligation
            .local_id
            .contains(".oac_integer_site_")));
    }
}
