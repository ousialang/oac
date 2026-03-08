use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::verification_checker::sanitize_ident;
use crate::verification_outcomes::VerificationKind;
use crate::verification_profile::VerificationProfile;

const CACHE_SCHEMA_VERSION: u32 = 1;
const CACHE_VERIFIER_VERSION: &str = "oac-proof-summary-v1";

#[derive(Clone, Copy, Debug, Eq, PartialEq, clap::ValueEnum)]
pub(crate) enum VerificationCacheMode {
    Trust,
    Strict,
    Off,
}

impl VerificationCacheMode {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Trust => "trust",
            Self::Strict => "strict",
            Self::Off => "off",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum VerificationCacheWritePolicy {
    PersistUnsat,
    ReadOnly,
}

#[derive(Clone, Debug)]
pub(crate) struct VerificationConfig {
    pub profile: VerificationProfile,
    pub cache_mode: VerificationCacheMode,
    pub cache_root: PathBuf,
    pub cache_write_policy: VerificationCacheWritePolicy,
}

impl VerificationConfig {
    pub(crate) fn new(
        profile: VerificationProfile,
        cache_mode: VerificationCacheMode,
        cache_root: PathBuf,
        cache_write_policy: VerificationCacheWritePolicy,
    ) -> Self {
        Self {
            profile,
            cache_mode,
            cache_root,
            cache_write_policy,
        }
    }

    pub(crate) fn cache_reads_enabled(&self) -> bool {
        self.cache_mode != VerificationCacheMode::Off
    }

    pub(crate) fn cache_trust_enabled(&self) -> bool {
        self.cache_mode == VerificationCacheMode::Trust
    }

    pub(crate) fn cache_writes_enabled(&self) -> bool {
        self.cache_mode != VerificationCacheMode::Off
            && self.cache_write_policy == VerificationCacheWritePolicy::PersistUnsat
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum VerificationSummaryKind {
    OrdinaryFunction,
    ModelInvariantFunction,
}

impl VerificationSummaryKind {
    fn as_str(self) -> &'static str {
        match self {
            Self::OrdinaryFunction => "ordinary_function",
            Self::ModelInvariantFunction => "model_invariant_function",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct VerificationSummaryInput {
    pub kind: VerificationKind,
    pub local_id: String,
    pub smt: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
pub(crate) struct VerificationSummaryObligation {
    pub kind: VerificationKind,
    pub local_id: String,
    pub smt_hash: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum VerificationSummaryResult {
    Unsat,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub(crate) struct VerificationSummaryFile {
    pub schema_version: u32,
    pub verifier_version: String,
    pub compiler_version: String,
    pub root_name: String,
    pub summary_kind: VerificationSummaryKind,
    pub content_hash: String,
    pub obligations: Vec<VerificationSummaryObligation>,
    pub result: VerificationSummaryResult,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct VerificationSummaryCandidate {
    root_name: String,
    summary_kind: VerificationSummaryKind,
    content_hash: String,
    obligations: Vec<VerificationSummaryObligation>,
}

impl VerificationSummaryCandidate {
    pub(crate) fn from_inputs(
        root_name: &str,
        summary_kind: VerificationSummaryKind,
        inputs: &[VerificationSummaryInput],
    ) -> Self {
        let mut obligations = inputs
            .iter()
            .map(|input| VerificationSummaryObligation {
                kind: input.kind,
                local_id: input.local_id.clone(),
                smt_hash: sha256_hex(input.smt.as_bytes()),
            })
            .collect::<Vec<_>>();
        obligations.sort();

        let content_hash = compute_content_hash(root_name, summary_kind, &obligations);
        Self {
            root_name: root_name.to_string(),
            summary_kind,
            content_hash,
            obligations,
        }
    }

    pub(crate) fn matches_persisted_unsat(&self, cache_root: &Path) -> anyhow::Result<bool> {
        let path = self.path(cache_root);
        if !path.exists() {
            return Ok(false);
        }

        let raw = match std::fs::read_to_string(&path) {
            Ok(raw) => raw,
            Err(_) => return Ok(false),
        };
        let parsed = match serde_json::from_str::<VerificationSummaryFile>(&raw) {
            Ok(parsed) => parsed,
            Err(_) => return Ok(false),
        };

        Ok(parsed == self.as_file())
    }

    pub(crate) fn persist_unsat(&self, cache_root: &Path) -> anyhow::Result<()> {
        let path = self.path(cache_root);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).map_err(|err| {
                anyhow::anyhow!(
                    "failed to create verification cache directory {}: {}",
                    parent.display(),
                    err
                )
            })?;
        }

        let mut text = serde_json::to_string_pretty(&self.as_file()).map_err(|err| {
            anyhow::anyhow!(
                "failed to serialize verification summary for {}: {}",
                self.root_name,
                err
            )
        })?;
        text.push('\n');
        std::fs::write(&path, text).map_err(|err| {
            anyhow::anyhow!(
                "failed to write verification summary {}: {}",
                path.display(),
                err
            )
        })?;
        Ok(())
    }

    fn path(&self, cache_root: &Path) -> PathBuf {
        cache_root
            .join(self.summary_kind.as_str())
            .join(sanitize_ident(&self.root_name))
            .join(format!("{}.json", self.content_hash))
    }

    fn as_file(&self) -> VerificationSummaryFile {
        VerificationSummaryFile {
            schema_version: CACHE_SCHEMA_VERSION,
            verifier_version: CACHE_VERIFIER_VERSION.to_string(),
            compiler_version: env!("CARGO_PKG_VERSION").to_string(),
            root_name: self.root_name.clone(),
            summary_kind: self.summary_kind,
            content_hash: self.content_hash.clone(),
            obligations: self.obligations.clone(),
            result: VerificationSummaryResult::Unsat,
        }
    }
}

fn compute_content_hash(
    root_name: &str,
    summary_kind: VerificationSummaryKind,
    obligations: &[VerificationSummaryObligation],
) -> String {
    let mut canonical = String::new();
    canonical.push_str(&format!("schema={CACHE_SCHEMA_VERSION}\n"));
    canonical.push_str(&format!("verifier={CACHE_VERIFIER_VERSION}\n"));
    canonical.push_str(&format!("kind={}\n", summary_kind.as_str()));
    canonical.push_str(&format!("root={root_name}\n"));
    for obligation in obligations {
        canonical.push_str(&format!(
            "obligation={}|{}|{}\n",
            verification_kind_label(obligation.kind),
            obligation.local_id,
            obligation.smt_hash
        ));
    }
    sha256_hex(canonical.as_bytes())
}

fn verification_kind_label(kind: VerificationKind) -> &'static str {
    match kind {
        VerificationKind::Precondition => "precondition",
        VerificationKind::Prove => "prove",
        VerificationKind::StructInvariant => "struct_invariant",
        VerificationKind::ModelInvariant => "model_invariant",
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(digest.len() * 2);
    for byte in digest {
        out.push(hex_digit((byte >> 4) & 0x0f));
        out.push(hex_digit(byte & 0x0f));
    }
    out
}

fn hex_digit(value: u8) -> char {
    match value {
        0..=9 => (b'0' + value) as char,
        10..=15 => (b'a' + (value - 10)) as char,
        _ => unreachable!("hex nybble must be in range"),
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::{
        VerificationCacheMode, VerificationCacheWritePolicy, VerificationConfig,
        VerificationSummaryCandidate, VerificationSummaryInput, VerificationSummaryKind,
    };
    use crate::verification_outcomes::VerificationKind;
    use crate::verification_profile::VerificationProfile;

    fn input(kind: VerificationKind, local_id: &str, smt: &str) -> VerificationSummaryInput {
        VerificationSummaryInput {
            kind,
            local_id: local_id.to_string(),
            smt: smt.to_string(),
        }
    }

    #[test]
    fn summary_hash_is_stable_across_input_order() {
        let a = VerificationSummaryCandidate::from_inputs(
            "main",
            VerificationSummaryKind::OrdinaryFunction,
            &[
                input(
                    VerificationKind::StructInvariant,
                    "main#0#0#inv",
                    "(query bad)",
                ),
                input(VerificationKind::Prove, "main#1#0", "(query bad-2)"),
            ],
        );
        let b = VerificationSummaryCandidate::from_inputs(
            "main",
            VerificationSummaryKind::OrdinaryFunction,
            &[
                input(VerificationKind::Prove, "main#1#0", "(query bad-2)"),
                input(
                    VerificationKind::StructInvariant,
                    "main#0#0#inv",
                    "(query bad)",
                ),
            ],
        );

        assert_eq!(a, b);
    }

    #[test]
    fn summary_hash_changes_when_smt_changes() {
        let a = VerificationSummaryCandidate::from_inputs(
            "main",
            VerificationSummaryKind::OrdinaryFunction,
            &[input(VerificationKind::Prove, "main#1#0", "(query bad)")],
        );
        let b = VerificationSummaryCandidate::from_inputs(
            "main",
            VerificationSummaryKind::OrdinaryFunction,
            &[input(
                VerificationKind::Prove,
                "main#1#0",
                "(query bad-with-different-body)",
            )],
        );

        assert_ne!(a, b);
    }

    #[test]
    fn persisted_summary_round_trips_as_matching_unsat() {
        let tmp = tempfile::tempdir().expect("create tempdir");
        let candidate = VerificationSummaryCandidate::from_inputs(
            "main",
            VerificationSummaryKind::OrdinaryFunction,
            &[input(VerificationKind::Prove, "main#1#0", "(query bad)")],
        );

        candidate
            .persist_unsat(tmp.path())
            .expect("persist summary file");

        assert!(
            candidate
                .matches_persisted_unsat(tmp.path())
                .expect("load summary"),
            "persisted summary should be recognized as a match"
        );
    }

    #[test]
    fn verification_config_reports_cache_policy_flags() {
        let trust = VerificationConfig::new(
            VerificationProfile::Candidate,
            VerificationCacheMode::Trust,
            PathBuf::from("target/oac/verification_cache"),
            VerificationCacheWritePolicy::PersistUnsat,
        );
        let strict_read_only = VerificationConfig::new(
            VerificationProfile::Baseline,
            VerificationCacheMode::Strict,
            PathBuf::from("target/oac/verification_cache"),
            VerificationCacheWritePolicy::ReadOnly,
        );

        assert!(trust.cache_reads_enabled());
        assert!(trust.cache_trust_enabled());
        assert!(trust.cache_writes_enabled());

        assert!(strict_read_only.cache_reads_enabled());
        assert!(!strict_read_only.cache_trust_enabled());
        assert!(!strict_read_only.cache_writes_enabled());
    }
}
