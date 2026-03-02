use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::{Mutex, OnceLock};

use serde::{Deserialize, Serialize};

use crate::verification_profile::VerificationProfile;

const OUTCOME_SCHEMA_VERSION: u32 = 1;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum VerificationKind {
    Prove,
    StructInvariant,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum VerificationOutcome {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
pub(crate) struct VerificationOutcomeRecord {
    pub kind: VerificationKind,
    pub obligation_id: String,
    pub caller: String,
    pub callee: Option<String>,
    pub invariant_key: Option<String>,
    pub outcome: VerificationOutcome,
    pub fixture: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub(crate) struct VerificationOutcomeFile {
    pub schema_version: u32,
    pub profile: String,
    pub records: Vec<VerificationOutcomeRecord>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct VerificationOutcomeDelta {
    pub key: String,
    pub baseline: VerificationOutcome,
    pub candidate: VerificationOutcome,
}

#[derive(Default)]
struct ActiveCollector {
    profile: Option<VerificationProfile>,
    records: Vec<VerificationOutcomeRecord>,
}

static COLLECTOR: OnceLock<Mutex<ActiveCollector>> = OnceLock::new();
thread_local! {
    static FIXTURE_CONTEXT: RefCell<Option<String>> = const { RefCell::new(None) };
}

fn collector() -> &'static Mutex<ActiveCollector> {
    COLLECTOR.get_or_init(|| Mutex::new(ActiveCollector::default()))
}

pub(crate) fn with_fixture_context<T>(fixture: &str, run: impl FnOnce() -> T) -> T {
    FIXTURE_CONTEXT.with(|slot| {
        let previous = slot.replace(Some(fixture.to_string()));
        let output = run();
        slot.replace(previous);
        output
    })
}

fn current_fixture_context() -> Option<String> {
    FIXTURE_CONTEXT.with(|slot| slot.borrow().clone())
}

pub(crate) fn begin_outcome_collection(profile: VerificationProfile) -> anyhow::Result<()> {
    let mut guard = collector()
        .lock()
        .map_err(|_| anyhow::anyhow!("verification outcome collector lock poisoned"))?;
    if guard.profile.is_some() {
        anyhow::bail!("verification outcome collector is already active");
    }
    guard.profile = Some(profile);
    guard.records.clear();
    Ok(())
}

pub(crate) fn record_outcome(mut record: VerificationOutcomeRecord) {
    let Ok(mut guard) = collector().lock() else {
        return;
    };
    let Some(_profile) = guard.profile else {
        return;
    };
    if record.fixture.is_none() {
        record.fixture = current_fixture_context()
            .or_else(|| std::env::var("OAC_VERIFICATION_OUTCOME_FIXTURE").ok());
    }
    guard.records.push(record);
}

pub(crate) fn end_outcome_collection(path: &Path) -> anyhow::Result<VerificationOutcomeFile> {
    let mut guard = collector()
        .lock()
        .map_err(|_| anyhow::anyhow!("verification outcome collector lock poisoned"))?;
    let profile = guard
        .profile
        .take()
        .ok_or_else(|| anyhow::anyhow!("verification outcome collector is not active"))?;
    let mut records = std::mem::take(&mut guard.records);
    records.sort();

    let file = VerificationOutcomeFile {
        schema_version: OUTCOME_SCHEMA_VERSION,
        profile: profile.as_str().to_string(),
        records,
    };
    write_outcome_file(path, &file)?;
    Ok(file)
}

pub(crate) fn write_outcome_file(
    path: &Path,
    file: &VerificationOutcomeFile,
) -> anyhow::Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .map_err(|err| anyhow::anyhow!("failed to create {}: {}", parent.display(), err))?;
    }
    let mut text = serde_json::to_string_pretty(file)
        .map_err(|err| anyhow::anyhow!("failed to serialize {}: {}", path.display(), err))?;
    text.push('\n');
    std::fs::write(path, text)
        .map_err(|err| anyhow::anyhow!("failed to write {}: {}", path.display(), err))?;
    Ok(())
}

#[allow(dead_code)]
pub(crate) fn load_outcome_file(path: &Path) -> anyhow::Result<VerificationOutcomeFile> {
    let raw = std::fs::read_to_string(path)
        .map_err(|err| anyhow::anyhow!("failed to read {}: {}", path.display(), err))?;
    let parsed = serde_json::from_str::<VerificationOutcomeFile>(&raw)
        .map_err(|err| anyhow::anyhow!("failed to parse {}: {}", path.display(), err))?;
    if parsed.schema_version != OUTCOME_SCHEMA_VERSION {
        anyhow::bail!(
            "unsupported verification outcome schema {} in {}",
            parsed.schema_version,
            path.display()
        );
    }
    Ok(parsed)
}

pub(crate) fn forbidden_transition_deltas(
    baseline: &VerificationOutcomeFile,
    candidate: &VerificationOutcomeFile,
) -> anyhow::Result<Vec<VerificationOutcomeDelta>> {
    let baseline_map = baseline
        .records
        .iter()
        .map(|record| (record_key(record), record.outcome))
        .collect::<BTreeMap<_, _>>();
    let candidate_map = candidate
        .records
        .iter()
        .map(|record| (record_key(record), record.outcome))
        .collect::<BTreeMap<_, _>>();

    let baseline_keys = baseline_map.keys().cloned().collect::<BTreeSet<_>>();
    let candidate_keys = candidate_map.keys().cloned().collect::<BTreeSet<_>>();
    if baseline_keys != candidate_keys {
        let missing = baseline_keys
            .difference(&candidate_keys)
            .cloned()
            .collect::<Vec<_>>();
        let extra = candidate_keys
            .difference(&baseline_keys)
            .cloned()
            .collect::<Vec<_>>();
        anyhow::bail!(
            "verification obligation set changed; missing={:?}, extra={:?}",
            missing,
            extra
        );
    }

    let mut deltas = Vec::new();
    for key in baseline_keys {
        let baseline_outcome = *baseline_map.get(&key).expect("baseline key must exist");
        let candidate_outcome = *candidate_map.get(&key).expect("candidate key must exist");
        if baseline_outcome == VerificationOutcome::Unknown {
            continue;
        }
        if baseline_outcome != candidate_outcome {
            deltas.push(VerificationOutcomeDelta {
                key,
                baseline: baseline_outcome,
                candidate: candidate_outcome,
            });
        }
    }
    Ok(deltas)
}

fn record_key(record: &VerificationOutcomeRecord) -> String {
    format!("{:?}:{}", record.kind, record.obligation_id)
}

#[cfg(test)]
mod tests {
    use super::{
        forbidden_transition_deltas, VerificationKind, VerificationOutcome,
        VerificationOutcomeFile, VerificationOutcomeRecord,
    };

    fn record(
        kind: VerificationKind,
        obligation_id: &str,
        outcome: VerificationOutcome,
    ) -> VerificationOutcomeRecord {
        VerificationOutcomeRecord {
            kind,
            obligation_id: obligation_id.to_string(),
            caller: "main".to_string(),
            callee: None,
            invariant_key: None,
            outcome,
            fixture: None,
        }
    }

    #[test]
    fn allows_unknown_transitions_only() {
        let baseline = VerificationOutcomeFile {
            schema_version: 1,
            profile: "baseline".to_string(),
            records: vec![
                record(VerificationKind::Prove, "a", VerificationOutcome::Unknown),
                record(VerificationKind::Prove, "b", VerificationOutcome::Sat),
                record(
                    VerificationKind::StructInvariant,
                    "c",
                    VerificationOutcome::Unsat,
                ),
            ],
        };
        let candidate = VerificationOutcomeFile {
            schema_version: 1,
            profile: "candidate".to_string(),
            records: vec![
                record(VerificationKind::Prove, "a", VerificationOutcome::Unsat),
                record(VerificationKind::Prove, "b", VerificationOutcome::Sat),
                record(
                    VerificationKind::StructInvariant,
                    "c",
                    VerificationOutcome::Unsat,
                ),
            ],
        };

        let deltas = forbidden_transition_deltas(&baseline, &candidate).expect("compare");
        assert!(deltas.is_empty());
    }

    #[test]
    fn detects_forbidden_sat_or_unsat_transition() {
        let baseline = VerificationOutcomeFile {
            schema_version: 1,
            profile: "baseline".to_string(),
            records: vec![record(
                VerificationKind::Prove,
                "a",
                VerificationOutcome::Unsat,
            )],
        };
        let candidate = VerificationOutcomeFile {
            schema_version: 1,
            profile: "candidate".to_string(),
            records: vec![record(
                VerificationKind::Prove,
                "a",
                VerificationOutcome::Sat,
            )],
        };

        let deltas = forbidden_transition_deltas(&baseline, &candidate).expect("compare");
        assert_eq!(deltas.len(), 1);
    }
}
