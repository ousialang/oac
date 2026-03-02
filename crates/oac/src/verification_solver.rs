use crate::verification_profile::VerificationProfile;

const Z3_TIMEOUT_SECONDS: u64 = 10;
const Z3_TIMEOUT_RETRY_SECONDS: u64 = 30;
const DEFAULT_LARGE_OBLIGATION_BYTES: usize = 8_000_000;
const DEFAULT_LARGE_TIMEOUT_SECONDS: u64 = 90;

pub(crate) const ENV_Z3_LARGE_OBLIGATION_BYTES: &str = "OAC_Z3_LARGE_OBLIGATION_BYTES";
pub(crate) const ENV_Z3_TIMEOUT_LARGE_OBLIGATION_SECS: &str =
    "OAC_Z3_TIMEOUT_LARGE_OBLIGATION_SECS";

#[derive(Clone, Copy, Debug)]
struct SolverPolicy {
    large_obligation_bytes: usize,
    large_timeout_seconds: u64,
}

#[derive(Clone, Debug)]
pub(crate) struct SolverAttempt {
    pub timeout_seconds: u64,
    pub result: qbe_smt::SolverResult,
    pub reason: Option<String>,
}

#[derive(Clone, Debug)]
pub(crate) struct SolverRunWithAttempts {
    pub final_run: qbe_smt::SolverRun,
    pub attempts: Vec<SolverAttempt>,
}

pub(crate) fn solve_chc_with_policy(
    smt: &str,
    profile: VerificationProfile,
) -> Result<SolverRunWithAttempts, qbe_smt::QbeSmtError> {
    solve_chc_with_policy_for_bytes(smt, smt.len(), profile)
}

pub(crate) fn solve_chc_with_policy_for_bytes(
    smt: &str,
    smt_bytes: usize,
    profile: VerificationProfile,
) -> Result<SolverRunWithAttempts, qbe_smt::QbeSmtError> {
    let policy = SolverPolicy::from_env();
    solve_chc_with_policy_for_bytes_and_runner(smt_bytes, profile, policy, |timeout_seconds| {
        run_solver_attempt(smt, timeout_seconds)
    })
}

fn solve_chc_with_policy_for_bytes_and_runner(
    smt_bytes: usize,
    profile: VerificationProfile,
    policy: SolverPolicy,
    mut run_attempt: impl FnMut(u64) -> Result<qbe_smt::SolverRun, qbe_smt::QbeSmtError>,
) -> Result<SolverRunWithAttempts, qbe_smt::QbeSmtError> {
    let mut attempts = Vec::new();

    let first = run_attempt(Z3_TIMEOUT_SECONDS)?;
    attempts.push(SolverAttempt {
        timeout_seconds: Z3_TIMEOUT_SECONDS,
        result: first.result,
        reason: reason_from_solver_run(&first),
    });
    if first.result != qbe_smt::SolverResult::Unknown {
        return Ok(SolverRunWithAttempts {
            final_run: first,
            attempts,
        });
    }

    let retry = run_attempt(Z3_TIMEOUT_RETRY_SECONDS)?;
    attempts.push(SolverAttempt {
        timeout_seconds: Z3_TIMEOUT_RETRY_SECONDS,
        result: retry.result,
        reason: reason_from_solver_run(&retry),
    });
    if retry.result != qbe_smt::SolverResult::Unknown {
        return Ok(SolverRunWithAttempts {
            final_run: retry,
            attempts,
        });
    }

    let Some(large_timeout) = policy.large_attempt_timeout(profile, smt_bytes) else {
        return Ok(SolverRunWithAttempts {
            final_run: retry,
            attempts,
        });
    };

    let large_retry = run_attempt(large_timeout)?;
    attempts.push(SolverAttempt {
        timeout_seconds: large_timeout,
        result: large_retry.result,
        reason: reason_from_solver_run(&large_retry),
    });
    Ok(SolverRunWithAttempts {
        final_run: large_retry,
        attempts,
    })
}

fn run_solver_attempt(
    smt: &str,
    timeout_seconds: u64,
) -> Result<qbe_smt::SolverRun, qbe_smt::QbeSmtError> {
    #[cfg(test)]
    if let Some(mocked) = test_support::next_mock_solver_result(timeout_seconds) {
        return mocked;
    }

    qbe_smt::solve_chc_script_with_diagnostics(smt, timeout_seconds)
}

impl SolverPolicy {
    fn from_env() -> Self {
        Self {
            large_obligation_bytes: read_usize_env(
                ENV_Z3_LARGE_OBLIGATION_BYTES,
                DEFAULT_LARGE_OBLIGATION_BYTES,
            ),
            large_timeout_seconds: read_u64_env(
                ENV_Z3_TIMEOUT_LARGE_OBLIGATION_SECS,
                DEFAULT_LARGE_TIMEOUT_SECONDS,
            ),
        }
    }

    fn large_attempt_timeout(self, profile: VerificationProfile, smt_bytes: usize) -> Option<u64> {
        if profile == VerificationProfile::Baseline {
            return None;
        }
        if smt_bytes < self.large_obligation_bytes {
            return None;
        }
        if self.large_timeout_seconds <= Z3_TIMEOUT_RETRY_SECONDS {
            return None;
        }
        Some(self.large_timeout_seconds)
    }
}

pub(crate) fn format_attempts(attempts: &[SolverAttempt]) -> String {
    if attempts.is_empty() {
        return "[]".to_string();
    }

    let items = attempts
        .iter()
        .map(|attempt| {
            let status = match attempt.result {
                qbe_smt::SolverResult::Sat => "sat",
                qbe_smt::SolverResult::Unsat => "unsat",
                qbe_smt::SolverResult::Unknown => "unknown",
            };
            if let Some(reason) = &attempt.reason {
                format!("{}s:{}({})", attempt.timeout_seconds, status, reason)
            } else {
                format!("{}s:{}", attempt.timeout_seconds, status)
            }
        })
        .collect::<Vec<_>>();

    format!("[{}]", items.join(", "))
}

fn reason_from_solver_run(run: &qbe_smt::SolverRun) -> Option<String> {
    run.stdout
        .lines()
        .chain(run.stderr.lines())
        .map(str::trim)
        .find_map(|line| {
            if line.is_empty() {
                return None;
            }
            if line.starts_with("(reason-unknown") {
                return Some(line.to_string());
            }
            if line.eq_ignore_ascii_case("timeout") {
                return Some("timeout".to_string());
            }
            None
        })
}

fn read_u64_env(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|value| value.parse::<u64>().ok())
        .unwrap_or(default)
}

fn read_usize_env(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(default)
}

#[cfg(test)]
pub(crate) mod test_support {
    use std::cell::RefCell;
    use std::collections::VecDeque;

    thread_local! {
        static MOCK_RUNS: RefCell<Option<VecDeque<Result<qbe_smt::SolverRun, qbe_smt::QbeSmtError>>>> = const { RefCell::new(None) };
        static OBSERVED_TIMEOUTS: RefCell<Vec<u64>> = const { RefCell::new(Vec::new()) };
    }

    pub(crate) fn with_mock_solver_runs<T>(
        runs: Vec<Result<qbe_smt::SolverRun, qbe_smt::QbeSmtError>>,
        action: impl FnOnce() -> T,
    ) -> T {
        MOCK_RUNS.with(|cell| {
            *cell.borrow_mut() = Some(VecDeque::from(runs));
        });
        OBSERVED_TIMEOUTS.with(|cell| cell.borrow_mut().clear());

        let output = action();

        MOCK_RUNS.with(|cell| {
            *cell.borrow_mut() = None;
        });

        output
    }

    pub(crate) fn observed_timeouts() -> Vec<u64> {
        OBSERVED_TIMEOUTS.with(|cell| cell.borrow().clone())
    }

    pub(crate) fn next_mock_solver_result(
        timeout_seconds: u64,
    ) -> Option<Result<qbe_smt::SolverRun, qbe_smt::QbeSmtError>> {
        OBSERVED_TIMEOUTS.with(|cell| cell.borrow_mut().push(timeout_seconds));
        MOCK_RUNS.with(|cell| {
            let mut borrow = cell.borrow_mut();
            let queue = borrow.as_mut()?;
            Some(queue.pop_front().unwrap_or_else(|| {
                panic!("missing mocked solver run for timeout {}s", timeout_seconds)
            }))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{
        format_attempts, solve_chc_with_policy_for_bytes_and_runner, SolverPolicy,
        Z3_TIMEOUT_RETRY_SECONDS, Z3_TIMEOUT_SECONDS,
    };
    use crate::verification_profile::VerificationProfile;

    fn run(result: qbe_smt::SolverResult, stdout: &str, stderr: &str) -> qbe_smt::SolverRun {
        qbe_smt::SolverRun {
            result,
            stdout: stdout.to_string(),
            stderr: stderr.to_string(),
        }
    }

    #[test]
    fn baseline_profile_stays_two_attempts_even_for_large_unknown() {
        let mut calls = Vec::new();
        let output = solve_chc_with_policy_for_bytes_and_runner(
            1_000_000_000,
            VerificationProfile::Baseline,
            SolverPolicy {
                large_obligation_bytes: 1,
                large_timeout_seconds: 120,
            },
            |timeout| {
                calls.push(timeout);
                Ok(run(
                    qbe_smt::SolverResult::Unknown,
                    "unknown\n(reason-unknown timeout)",
                    "",
                ))
            },
        )
        .expect("solve");

        assert_eq!(calls, vec![Z3_TIMEOUT_SECONDS, Z3_TIMEOUT_RETRY_SECONDS]);
        assert_eq!(output.attempts.len(), 2);
    }

    #[test]
    fn candidate_profile_uses_third_attempt_only_for_large_obligation() {
        let mut calls = Vec::new();
        let output = solve_chc_with_policy_for_bytes_and_runner(
            1024,
            VerificationProfile::Candidate,
            SolverPolicy {
                large_obligation_bytes: 512,
                large_timeout_seconds: 90,
            },
            |timeout| {
                calls.push(timeout);
                if timeout == 90 {
                    return Ok(run(qbe_smt::SolverResult::Unsat, "unsat", ""));
                }
                Ok(run(qbe_smt::SolverResult::Unknown, "unknown", ""))
            },
        )
        .expect("solve");

        assert_eq!(calls, vec![10, 30, 90]);
        assert_eq!(output.final_run.result, qbe_smt::SolverResult::Unsat);
        assert_eq!(output.attempts.len(), 3);
    }

    #[test]
    fn third_attempt_is_skipped_when_large_timeout_is_not_stronger() {
        let mut calls = Vec::new();
        let output = solve_chc_with_policy_for_bytes_and_runner(
            1024,
            VerificationProfile::Candidate,
            SolverPolicy {
                large_obligation_bytes: 1,
                large_timeout_seconds: Z3_TIMEOUT_RETRY_SECONDS,
            },
            |timeout| {
                calls.push(timeout);
                Ok(run(qbe_smt::SolverResult::Unknown, "unknown", ""))
            },
        )
        .expect("solve");

        assert_eq!(calls, vec![10, 30]);
        assert_eq!(output.final_run.result, qbe_smt::SolverResult::Unknown);
        assert_eq!(output.attempts.len(), 2);
    }

    #[test]
    fn attempt_format_includes_reason_when_available() {
        let output = solve_chc_with_policy_for_bytes_and_runner(
            1024,
            VerificationProfile::Candidate,
            SolverPolicy {
                large_obligation_bytes: 512,
                large_timeout_seconds: 90,
            },
            |timeout| {
                if timeout == 10 {
                    return Ok(run(
                        qbe_smt::SolverResult::Unknown,
                        "unknown\n(reason-unknown timeout)",
                        "",
                    ));
                }
                if timeout == 30 {
                    return Ok(run(qbe_smt::SolverResult::Unknown, "unknown", "timeout"));
                }
                Ok(run(qbe_smt::SolverResult::Sat, "sat", ""))
            },
        )
        .expect("solve");

        let formatted = format_attempts(&output.attempts);
        assert!(formatted.contains("10s:unknown((reason-unknown timeout))"));
        assert!(formatted.contains("30s:unknown(timeout)"));
        assert!(formatted.contains("90s:sat"));
    }
}
