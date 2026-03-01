#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum VerificationProfile {
    Baseline,
    Candidate,
}

impl Default for VerificationProfile {
    fn default() -> Self {
        Self::Candidate
    }
}

impl VerificationProfile {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Baseline => "baseline",
            Self::Candidate => "candidate",
        }
    }
}
