use std::collections::{BTreeMap, HashSet};
use std::path::Path;

use crate::ir::ResolvedProgram;
use crate::verification_cache::{
    VerificationConfig, VerificationSummaryCandidate, VerificationSummaryInput,
    VerificationSummaryKind,
};

#[derive(Debug)]
pub enum VerificationError {
    Prove(anyhow::Error),
    StructInvariant(anyhow::Error),
    ModelInvariant(anyhow::Error),
}

pub(crate) struct OrdinaryVerificationSession {
    prepared_prove: Vec<crate::prove::PreparedProveSite>,
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
        let prepared_prove = crate::prove::prepare_prove_obligations_with_config(
            program, qbe_module, target_dir, config,
        )
        .map_err(VerificationError::Prove)?;
        let prepared_struct =
            crate::struct_invariants::prepare_struct_invariant_obligations_with_config(
                program, qbe_module, target_dir, config,
            )
            .map_err(VerificationError::StructInvariant)?;

        let mut inputs_by_root = BTreeMap::<String, Vec<VerificationSummaryInput>>::new();
        for prepared in &prepared_prove {
            inputs_by_root
                .entry(prepared.caller().to_string())
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
            prepared_prove,
            prepared_struct,
            cached_roots,
            uncached_summaries,
        })
    }

    pub(crate) fn verify_prove_stage(
        &self,
        config: &VerificationConfig,
    ) -> Result<(), VerificationError> {
        crate::prove::verify_prepared_prove_obligations(
            &self.prepared_prove,
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

    #[test]
    fn ordinary_summary_cache_trust_hit_skips_solver() {
        let program = resolve_program(ordinary_root_source());
        let qbe_module = qbe_backend::compile(program.clone());
        let tempdir = tempfile::tempdir().expect("tempdir");
        let config = config(tempdir.path(), VerificationCacheMode::Trust);

        let first_session =
            prepare_ordinary_verification_session(&program, &qbe_module, tempdir.path(), &config)
                .expect("prepare first session");
        test_support::with_mock_solver_runs(
            vec![
                Ok(run(qbe_smt::SolverResult::Unsat, "unsat", "")),
                Ok(run(qbe_smt::SolverResult::Unsat, "unsat", "")),
            ],
            || {
                first_session
                    .verify_prove_stage(&config)
                    .expect("prove stage should succeed");
                first_session
                    .verify_struct_stage(&config)
                    .expect("struct stage should succeed");
                assert_eq!(test_support::observed_timeouts().len(), 2);
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
        let program = resolve_program(ordinary_root_source());
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
        test_support::with_mock_solver_runs(
            vec![
                Ok(run(qbe_smt::SolverResult::Unsat, "unsat", "")),
                Ok(run(qbe_smt::SolverResult::Unsat, "unsat", "")),
            ],
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
        test_support::with_mock_solver_runs(
            vec![Ok(run(qbe_smt::SolverResult::Sat, "sat", ""))],
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
        let program = resolve_program(ordinary_root_source());
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
}
