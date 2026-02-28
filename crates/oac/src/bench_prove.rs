use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use anyhow::Context;
use serde::{Deserialize, Serialize};

use crate::diagnostics::{CompilerDiagnostic, CompilerDiagnosticBundle, DiagnosticStage};
use crate::{compile_source_with_artifacts, CompileSourceCodes, FrontendPipelineCodes};

const BASELINE_SCHEMA_VERSION: u32 = 1;
const REPORT_SCHEMA_VERSION: u32 = 1;
const DEFAULT_REGRESSION_PCT: f64 = 20.0;
const DEFAULT_REGRESSION_MS: u64 = 200;

const QUICK_SUITE_FIXTURE_COUNT: usize = 4;

#[derive(clap::Parser, Debug, Clone)]
#[clap(
    name = "bench-prove",
    about = "Benchmark proving and invariant verification performance."
)]
pub struct BenchProveOpts {
    #[clap(long, value_enum, default_value_t = BenchSuite::Full)]
    pub suite: BenchSuite,
    #[clap(long, default_value_t = 1)]
    pub iterations: usize,
    #[clap(long)]
    pub baseline: Option<PathBuf>,
    #[clap(long)]
    pub output: Option<PathBuf>,
    #[clap(long, default_value_t = false)]
    pub update_baseline: bool,
}

#[derive(clap::ValueEnum, Debug, Clone, Copy, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum BenchSuite {
    Full,
    Quick,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegressionThresholds {
    pub regression_pct: f64,
    pub regression_ms: u64,
}

impl Default for RegressionThresholds {
    fn default() -> Self {
        Self {
            regression_pct: DEFAULT_REGRESSION_PCT,
            regression_ms: DEFAULT_REGRESSION_MS,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BaselineFixture {
    pub id: String,
    pub source: String,
    pub expected_code: Option<String>,
    pub baseline_elapsed_ms: u64,
    pub baseline_prove_smt2_count: u64,
    pub baseline_prove_smt2_bytes: u64,
    pub baseline_inv_smt2_count: u64,
    pub baseline_inv_smt2_bytes: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProveBenchBaseline {
    pub schema_version: u32,
    pub thresholds: RegressionThresholds,
    pub fixtures: Vec<BaselineFixture>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HostMetadata {
    pub os: String,
    pub arch: String,
    pub family: String,
    pub hostname: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ToolMetadata {
    pub z3_version: Option<String>,
    pub qbe_version: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReportRunMetadata {
    pub timestamp_unix_ms: u64,
    pub suite: BenchSuite,
    pub iterations: usize,
    pub baseline_path: String,
    pub output_path: String,
    pub host: HostMetadata,
    pub tools: ToolMetadata,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReportFixture {
    pub id: String,
    pub source: String,
    pub expected_code: Option<String>,
    pub selected_outcome: String,
    pub selected_outcome_code: Option<String>,
    pub outcome_matches_expected: bool,
    pub elapsed_ms: u64,
    pub iteration_elapsed_ms: Vec<u64>,
    pub baseline_elapsed_ms: Option<u64>,
    pub delta_ms: Option<i64>,
    pub delta_pct: Option<f64>,
    pub regression: bool,
    pub prove_smt2_count: u64,
    pub prove_smt2_bytes: u64,
    pub inv_smt2_count: u64,
    pub inv_smt2_bytes: u64,
    pub baseline_prove_smt2_count: Option<u64>,
    pub baseline_prove_smt2_bytes: Option<u64>,
    pub baseline_inv_smt2_count: Option<u64>,
    pub baseline_inv_smt2_bytes: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReportSummary {
    pub total_fixtures: usize,
    pub unexpected_outcomes: usize,
    pub regressions: usize,
    pub total_elapsed_ms: u64,
    pub timing_regressions_report_only: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProveBenchReport {
    pub schema_version: u32,
    pub run: ReportRunMetadata,
    pub fixtures: Vec<ReportFixture>,
    pub summary: ReportSummary,
}

#[derive(Clone, Copy, Debug)]
struct FixtureSpec {
    id: &'static str,
    source: &'static str,
    expected_code: Option<&'static str>,
}

const FULL_SUITE_FIXTURES: [FixtureSpec; 6] = [
    FixtureSpec {
        id: "prove_pass",
        source: "crates/oac/execution_tests/prove_pass.oa",
        expected_code: None,
    },
    FixtureSpec {
        id: "prove_fail",
        source: "crates/oac/execution_tests/prove_fail.oa",
        expected_code: Some("OAC-PROVE-001"),
    },
    FixtureSpec {
        id: "struct_invariant_pass",
        source: "crates/oac/execution_tests/struct_invariant_pass.oa",
        expected_code: None,
    },
    FixtureSpec {
        id: "struct_invariant_fail",
        source: "crates/oac/execution_tests/struct_invariant_fail.oa",
        expected_code: Some("OAC-INV-001"),
    },
    FixtureSpec {
        id: "struct_invariant_pass_complex",
        source: "crates/oac/execution_tests/struct_invariant_pass_complex.oa",
        expected_code: Some("OAC-INV-001"),
    },
    FixtureSpec {
        id: "template_hash_table_i32",
        source: "crates/oac/execution_tests/template_hash_table_i32.oa",
        expected_code: Some("OAC-INV-001"),
    },
];

#[derive(Debug, Clone)]
struct ArtifactStats {
    count: u64,
    bytes: u64,
}

#[derive(Debug, Clone)]
enum IterationOutcome {
    Success,
    Failure { code: Option<String> },
}

#[derive(Debug, Clone)]
struct IterationSample {
    elapsed_ms: u64,
    outcome: IterationOutcome,
    prove_stats: ArtifactStats,
    inv_stats: ArtifactStats,
}

#[derive(Debug)]
struct BenchOutcome {
    report: ProveBenchReport,
    report_path: PathBuf,
    baseline_path: PathBuf,
    baseline_updated: bool,
    unexpected: Vec<String>,
}

pub(crate) fn run(
    current_dir: &Path,
    opts: BenchProveOpts,
) -> Result<(), CompilerDiagnosticBundle> {
    let execution = run_with_runner(current_dir, &opts, run_fixture_iteration).map_err(|err| {
        CompilerDiagnosticBundle::single(
            CompilerDiagnostic::new(
                "OAC-BENCH-001",
                DiagnosticStage::Internal,
                "bench-prove failed",
            )
            .with_note(err.to_string()),
        )
    })?;

    print_report_table(&execution.report);
    println!(
        "note: timing regressions are report-only in v1; unexpected outcomes still fail the command"
    );
    println!("report written to {}", execution.report_path.display());
    if execution.baseline_updated {
        println!("baseline updated at {}", execution.baseline_path.display());
    }

    if execution.unexpected.is_empty() {
        return Ok(());
    }

    let mut diagnostic = CompilerDiagnostic::new(
        "OAC-BENCH-002",
        DiagnosticStage::Internal,
        "benchmark suite found unexpected fixture outcomes",
    )
    .with_note(format!("report: {}", execution.report_path.display()));
    for entry in &execution.unexpected {
        diagnostic = diagnostic.with_note(entry.clone());
    }
    Err(CompilerDiagnosticBundle::single(diagnostic))
}

fn run_with_runner<F>(
    current_dir: &Path,
    opts: &BenchProveOpts,
    mut runner: F,
) -> anyhow::Result<BenchOutcome>
where
    F: FnMut(&Path, &FixtureSpec, usize, &Path) -> anyhow::Result<IterationSample>,
{
    if opts.iterations == 0 {
        anyhow::bail!("iterations must be greater than zero");
    }

    let fixtures = suite_fixtures(opts.suite);
    let baseline_path = opts
        .baseline
        .clone()
        .unwrap_or_else(|| default_baseline_path(current_dir));
    let output_path = opts
        .output
        .clone()
        .unwrap_or_else(|| default_report_path(current_dir));
    let runs_root = current_dir
        .join("target")
        .join("oac")
        .join("bench")
        .join("runs");
    std::fs::create_dir_all(&runs_root).with_context(|| {
        format!(
            "failed to create benchmark runs directory {}",
            runs_root.display()
        )
    })?;

    let baseline = if baseline_path.exists() {
        Some(load_baseline(&baseline_path)?)
    } else if opts.update_baseline {
        None
    } else {
        anyhow::bail!(
            "baseline file not found at {} (use --baseline or --update-baseline)",
            baseline_path.display()
        );
    };

    let baseline_thresholds = baseline
        .as_ref()
        .map(|value| value.thresholds.clone())
        .unwrap_or_default();
    let baseline_map = baseline
        .as_ref()
        .map(|value| {
            value
                .fixtures
                .iter()
                .map(|fixture| (fixture.id.clone(), fixture.clone()))
                .collect::<HashMap<_, _>>()
        })
        .unwrap_or_default();

    validate_baseline_for_suite(&baseline_map, &fixtures)?;

    let mut report_fixtures = Vec::new();
    let mut updated_baseline_entries = Vec::new();
    let mut unexpected = Vec::new();
    let mut total_elapsed_ms = 0_u64;

    for fixture in fixtures {
        let mut samples = Vec::with_capacity(opts.iterations);
        for iteration_index in 0..opts.iterations {
            samples.push(
                runner(current_dir, &fixture, iteration_index, &runs_root).with_context(|| {
                    format!("fixture {} iteration {}", fixture.id, iteration_index + 1)
                })?,
            );
        }

        let selected_idx = median_sample_index(&samples);
        let selected = samples
            .get(selected_idx)
            .ok_or_else(|| anyhow::anyhow!("missing selected sample for {}", fixture.id))?;
        let outcome_matches_expected = samples
            .iter()
            .all(|sample| outcome_matches(fixture.expected_code, &sample.outcome));

        if !outcome_matches_expected {
            let expected_label = expected_label(fixture.expected_code);
            for (index, sample) in samples.iter().enumerate() {
                if outcome_matches(fixture.expected_code, &sample.outcome) {
                    continue;
                }
                unexpected.push(format!(
                    "{} (iteration {}): expected {}, observed {}",
                    fixture.id,
                    index + 1,
                    expected_label,
                    outcome_label(&sample.outcome)
                ));
            }
        }

        let elapsed_ms_values = samples
            .iter()
            .map(|sample| sample.elapsed_ms)
            .collect::<Vec<_>>();
        let elapsed_ms = median_u64(&elapsed_ms_values);
        total_elapsed_ms = total_elapsed_ms.saturating_add(elapsed_ms);

        let baseline_fixture = baseline_map.get(fixture.id);
        let (delta_ms, delta_pct, regression) =
            classify_regression(elapsed_ms, baseline_fixture, &baseline_thresholds);

        let selected_outcome_code = match &selected.outcome {
            IterationOutcome::Success => None,
            IterationOutcome::Failure { code } => code.clone(),
        };

        report_fixtures.push(ReportFixture {
            id: fixture.id.to_string(),
            source: fixture.source.to_string(),
            expected_code: fixture.expected_code.map(str::to_string),
            selected_outcome: outcome_kind_label(&selected.outcome).to_string(),
            selected_outcome_code,
            outcome_matches_expected,
            elapsed_ms,
            iteration_elapsed_ms: elapsed_ms_values,
            baseline_elapsed_ms: baseline_fixture.map(|entry| entry.baseline_elapsed_ms),
            delta_ms,
            delta_pct,
            regression,
            prove_smt2_count: selected.prove_stats.count,
            prove_smt2_bytes: selected.prove_stats.bytes,
            inv_smt2_count: selected.inv_stats.count,
            inv_smt2_bytes: selected.inv_stats.bytes,
            baseline_prove_smt2_count: baseline_fixture
                .map(|entry| entry.baseline_prove_smt2_count),
            baseline_prove_smt2_bytes: baseline_fixture
                .map(|entry| entry.baseline_prove_smt2_bytes),
            baseline_inv_smt2_count: baseline_fixture.map(|entry| entry.baseline_inv_smt2_count),
            baseline_inv_smt2_bytes: baseline_fixture.map(|entry| entry.baseline_inv_smt2_bytes),
        });

        updated_baseline_entries.push(BaselineFixture {
            id: fixture.id.to_string(),
            source: fixture.source.to_string(),
            expected_code: fixture.expected_code.map(str::to_string),
            baseline_elapsed_ms: elapsed_ms,
            baseline_prove_smt2_count: selected.prove_stats.count,
            baseline_prove_smt2_bytes: selected.prove_stats.bytes,
            baseline_inv_smt2_count: selected.inv_stats.count,
            baseline_inv_smt2_bytes: selected.inv_stats.bytes,
        });
    }

    let regressions = report_fixtures
        .iter()
        .filter(|fixture| fixture.regression)
        .count();
    let summary = ReportSummary {
        total_fixtures: report_fixtures.len(),
        unexpected_outcomes: unexpected.len(),
        regressions,
        total_elapsed_ms,
        timing_regressions_report_only: true,
    };
    let report = ProveBenchReport {
        schema_version: REPORT_SCHEMA_VERSION,
        run: ReportRunMetadata {
            timestamp_unix_ms: now_unix_ms()?,
            suite: opts.suite,
            iterations: opts.iterations,
            baseline_path: baseline_path.display().to_string(),
            output_path: output_path.display().to_string(),
            host: host_metadata(),
            tools: tool_metadata(),
        },
        fixtures: report_fixtures,
        summary,
    };

    write_json_file(&output_path, &report)?;

    let mut baseline_updated = false;
    if opts.update_baseline {
        if !unexpected.is_empty() {
            anyhow::bail!("cannot update baseline when unexpected fixture outcomes are present");
        }

        let updated = update_baseline_data(
            baseline.unwrap_or(ProveBenchBaseline {
                schema_version: BASELINE_SCHEMA_VERSION,
                thresholds: RegressionThresholds::default(),
                fixtures: Vec::new(),
            }),
            updated_baseline_entries,
        );
        write_json_file(&baseline_path, &updated)?;
        baseline_updated = true;
    }

    Ok(BenchOutcome {
        report,
        report_path: output_path,
        baseline_path,
        baseline_updated,
        unexpected,
    })
}

fn run_fixture_iteration(
    current_dir: &Path,
    fixture: &FixtureSpec,
    iteration_index: usize,
    runs_root: &Path,
) -> anyhow::Result<IterationSample> {
    let source_path = current_dir.join(fixture.source);
    let fixture_dir = runs_root
        .join(fixture.id)
        .join(format!("iter_{}", iteration_index + 1));
    if fixture_dir.exists() {
        std::fs::remove_dir_all(&fixture_dir).with_context(|| {
            format!(
                "failed to clear previous fixture directory {}",
                fixture_dir.display()
            )
        })?;
    }
    std::fs::create_dir_all(&fixture_dir).with_context(|| {
        format!(
            "failed to create fixture directory {}",
            fixture_dir.display()
        )
    })?;

    let started = Instant::now();
    let compile_result = compile_source_with_artifacts(
        &source_path,
        &fixture_dir,
        None,
        "app",
        bench_compile_codes(),
    );
    let elapsed_ms = u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX);
    let outcome = match compile_result {
        Ok(_) => IterationOutcome::Success,
        Err(bundle) => {
            let code = bundle.diagnostics.first().map(|diag| diag.code.clone());
            IterationOutcome::Failure { code }
        }
    };

    let prove_stats = smt2_dir_stats(&fixture_dir.join("prove"))?;
    let inv_stats = smt2_dir_stats(&fixture_dir.join("struct_invariants"))?;

    Ok(IterationSample {
        elapsed_ms,
        outcome,
        prove_stats,
        inv_stats,
    })
}

fn bench_compile_codes() -> CompileSourceCodes<'static> {
    CompileSourceCodes {
        frontend: FrontendPipelineCodes {
            read_source_io_code: "OAC-BENCH-010",
            tokenize_code: "OAC-BENCH-011",
            serialize_tokens_io_code: "OAC-BENCH-012",
            write_tokens_io_code: "OAC-BENCH-013",
            parse_code: "OAC-BENCH-014",
            parse_message: "failed to parse benchmark source",
            import_code: "OAC-BENCH-015",
            import_message: "failed to resolve benchmark imports",
            comptime_code: "OAC-BENCH-016",
            comptime_message: "failed to execute benchmark comptime applies",
        },
        serialize_ast_io_code: "OAC-BENCH-017",
        write_ast_io_code: "OAC-BENCH-018",
    }
}

fn smt2_dir_stats(dir: &Path) -> anyhow::Result<ArtifactStats> {
    if !dir.exists() {
        return Ok(ArtifactStats { count: 0, bytes: 0 });
    }

    let mut count = 0_u64;
    let mut bytes = 0_u64;
    for entry in std::fs::read_dir(dir)
        .with_context(|| format!("failed to read artifact directory {}", dir.display()))?
    {
        let entry = entry.with_context(|| {
            format!(
                "failed to read entry in artifact directory {}",
                dir.display()
            )
        })?;
        let path = entry.path();
        let Some(ext) = path.extension() else {
            continue;
        };
        if ext != "smt2" {
            continue;
        }
        let metadata = entry
            .metadata()
            .with_context(|| format!("failed to inspect artifact {}", path.display()))?;
        count = count.saturating_add(1);
        bytes = bytes.saturating_add(metadata.len());
    }
    Ok(ArtifactStats { count, bytes })
}

fn outcome_matches(expected_code: Option<&str>, outcome: &IterationOutcome) -> bool {
    match (expected_code, outcome) {
        (None, IterationOutcome::Success) => true,
        (Some(expected), IterationOutcome::Failure { code }) => code.as_deref() == Some(expected),
        _ => false,
    }
}

fn expected_label(expected_code: Option<&str>) -> String {
    expected_code
        .map(|code| format!("failure({code})"))
        .unwrap_or_else(|| "success".to_string())
}

fn outcome_label(outcome: &IterationOutcome) -> String {
    match outcome {
        IterationOutcome::Success => "success".to_string(),
        IterationOutcome::Failure { code } => code
            .as_ref()
            .map(|value| format!("failure({value})"))
            .unwrap_or_else(|| "failure(<unknown>)".to_string()),
    }
}

fn outcome_kind_label(outcome: &IterationOutcome) -> &'static str {
    match outcome {
        IterationOutcome::Success => "success",
        IterationOutcome::Failure { .. } => "failure",
    }
}

fn median_sample_index(samples: &[IterationSample]) -> usize {
    let mut ordered = samples
        .iter()
        .enumerate()
        .map(|(idx, sample)| (idx, sample.elapsed_ms))
        .collect::<Vec<_>>();
    ordered.sort_by_key(|(idx, elapsed)| (*elapsed, *idx));
    ordered[(ordered.len() - 1) / 2].0
}

fn median_u64(values: &[u64]) -> u64 {
    let mut ordered = values.to_vec();
    ordered.sort_unstable();
    ordered[(ordered.len() - 1) / 2]
}

fn classify_regression(
    elapsed_ms: u64,
    baseline: Option<&BaselineFixture>,
    thresholds: &RegressionThresholds,
) -> (Option<i64>, Option<f64>, bool) {
    let Some(baseline) = baseline else {
        return (None, None, false);
    };
    let baseline_ms = baseline.baseline_elapsed_ms;
    let delta_ms = i64::try_from(elapsed_ms).unwrap_or(i64::MAX)
        - i64::try_from(baseline_ms).unwrap_or(i64::MAX);
    let delta_pct = if baseline_ms == 0 {
        None
    } else {
        Some(((delta_ms as f64) / (baseline_ms as f64)) * 100.0)
    };
    let regression = delta_ms >= i64::try_from(thresholds.regression_ms).unwrap_or(i64::MAX)
        && delta_pct
            .map(|pct| pct >= thresholds.regression_pct)
            .unwrap_or(false);
    (Some(delta_ms), delta_pct, regression)
}

fn suite_fixtures(suite: BenchSuite) -> Vec<FixtureSpec> {
    match suite {
        BenchSuite::Full => FULL_SUITE_FIXTURES.to_vec(),
        BenchSuite::Quick => FULL_SUITE_FIXTURES[..QUICK_SUITE_FIXTURE_COUNT].to_vec(),
    }
}

fn load_baseline(path: &Path) -> anyhow::Result<ProveBenchBaseline> {
    let raw = std::fs::read_to_string(path)
        .with_context(|| format!("failed to read baseline file {}", path.display()))?;
    let parsed = serde_json::from_str::<ProveBenchBaseline>(&raw)
        .with_context(|| format!("failed to parse baseline file {}", path.display()))?;
    validate_baseline(&parsed)?;
    Ok(parsed)
}

fn validate_baseline(baseline: &ProveBenchBaseline) -> anyhow::Result<()> {
    if baseline.schema_version != BASELINE_SCHEMA_VERSION {
        anyhow::bail!(
            "unsupported baseline schema version {} (expected {})",
            baseline.schema_version,
            BASELINE_SCHEMA_VERSION
        );
    }
    if baseline.thresholds.regression_pct < 0.0 {
        anyhow::bail!("baseline threshold regression_pct must be non-negative");
    }
    let mut ids = BTreeMap::new();
    for fixture in &baseline.fixtures {
        if ids.insert(fixture.id.clone(), ()).is_some() {
            anyhow::bail!("duplicate fixture id `{}` in baseline", fixture.id);
        }
    }
    Ok(())
}

fn validate_baseline_for_suite(
    baseline_map: &HashMap<String, BaselineFixture>,
    fixtures: &[FixtureSpec],
) -> anyhow::Result<()> {
    for fixture in fixtures {
        let Some(entry) = baseline_map.get(fixture.id) else {
            continue;
        };
        if entry.source != fixture.source {
            anyhow::bail!(
                "baseline source mismatch for `{}`: expected `{}`, found `{}`",
                fixture.id,
                fixture.source,
                entry.source
            );
        }
        if entry.expected_code.as_deref() != fixture.expected_code {
            anyhow::bail!(
                "baseline expected_code mismatch for `{}`: expected `{:?}`, found `{:?}`",
                fixture.id,
                fixture.expected_code,
                entry.expected_code
            );
        }
    }
    Ok(())
}

fn default_baseline_path(current_dir: &Path) -> PathBuf {
    current_dir
        .join("crates")
        .join("oac")
        .join("bench")
        .join("prove_baseline.json")
}

fn default_report_path(current_dir: &Path) -> PathBuf {
    current_dir
        .join("target")
        .join("oac")
        .join("bench")
        .join("prove")
        .join("latest.json")
}

fn host_metadata() -> HostMetadata {
    HostMetadata {
        os: std::env::consts::OS.to_string(),
        arch: std::env::consts::ARCH.to_string(),
        family: std::env::consts::FAMILY.to_string(),
        hostname: std::env::var("HOSTNAME")
            .ok()
            .or_else(|| std::env::var("COMPUTERNAME").ok()),
    }
}

fn tool_metadata() -> ToolMetadata {
    ToolMetadata {
        z3_version: detect_tool_version("z3", &["--version"]),
        qbe_version: detect_tool_version("qbe", &["-v"])
            .and_then(sanitize_qbe_version_line)
            .or_else(|| {
                detect_tool_version("qbe", &["--version"]).and_then(sanitize_qbe_version_line)
            }),
    }
}

fn sanitize_qbe_version_line(line: String) -> Option<String> {
    let lowered = line.to_ascii_lowercase();
    if lowered.contains("illegal option") || lowered.contains("usage:") {
        return None;
    }
    Some(line)
}

fn detect_tool_version(program: &str, args: &[&str]) -> Option<String> {
    let output = Command::new(program).args(args).output().ok()?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let merged = format!("{stdout}\n{stderr}");
    merged
        .lines()
        .map(str::trim)
        .find(|line| !line.is_empty())
        .map(str::to_string)
}

fn now_unix_ms() -> anyhow::Result<u64> {
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .context("system clock appears to be before unix epoch")?;
    Ok(u64::try_from(now.as_millis()).unwrap_or(u64::MAX))
}

fn write_json_file<T: Serialize>(path: &Path, value: &T) -> anyhow::Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .with_context(|| format!("failed to create output directory {}", parent.display()))?;
    }
    let mut data = serde_json::to_string_pretty(value)
        .with_context(|| format!("failed to serialize JSON for {}", path.display()))?;
    data.push('\n');
    std::fs::write(path, data).with_context(|| format!("failed to write {}", path.display()))?;
    Ok(())
}

fn update_baseline_data(
    current: ProveBenchBaseline,
    updates: Vec<BaselineFixture>,
) -> ProveBenchBaseline {
    let mut map = current
        .fixtures
        .into_iter()
        .map(|fixture| (fixture.id.clone(), fixture))
        .collect::<HashMap<_, _>>();
    for update in updates {
        map.insert(update.id.clone(), update);
    }

    let mut ordered = Vec::new();
    for fixture in FULL_SUITE_FIXTURES {
        if let Some(value) = map.remove(fixture.id) {
            ordered.push(value);
        }
    }
    let mut rest = map.into_iter().collect::<Vec<_>>();
    rest.sort_by(|(left, _), (right, _)| left.cmp(right));
    for (_, fixture) in rest {
        ordered.push(fixture);
    }

    ProveBenchBaseline {
        schema_version: BASELINE_SCHEMA_VERSION,
        thresholds: RegressionThresholds::default(),
        fixtures: ordered,
    }
}

fn print_report_table(report: &ProveBenchReport) {
    println!(
        "{:<34} {:>10} {:>20} {:>6} {:>12}",
        "fixture", "elapsed", "delta", "reg", "outcome"
    );
    for fixture in &report.fixtures {
        let delta = match (fixture.delta_ms, fixture.delta_pct) {
            (Some(ms), Some(pct)) => format!("{ms:+} ms ({pct:+.1}%)"),
            (Some(ms), None) => format!("{ms:+} ms"),
            _ => "n/a".to_string(),
        };
        let outcome = if fixture.outcome_matches_expected {
            "expected".to_string()
        } else {
            "unexpected".to_string()
        };
        println!(
            "{:<34} {:>10} {:>20} {:>6} {:>12}",
            fixture.id,
            format!("{} ms", fixture.elapsed_ms),
            delta,
            if fixture.regression { "yes" } else { "no" },
            outcome
        );
    }
}

#[cfg(test)]
mod tests {
    use super::{
        median_u64, outcome_matches, run_with_runner, suite_fixtures, BaselineFixture,
        BenchProveOpts, BenchSuite, IterationOutcome, IterationSample, ProveBenchBaseline,
        RegressionThresholds,
    };
    use tempfile::tempdir;

    fn sample_success(elapsed_ms: u64) -> IterationSample {
        IterationSample {
            elapsed_ms,
            outcome: IterationOutcome::Success,
            prove_stats: super::ArtifactStats {
                count: 1,
                bytes: 10,
            },
            inv_stats: super::ArtifactStats {
                count: 2,
                bytes: 20,
            },
        }
    }

    fn sample_failure(elapsed_ms: u64, code: &str) -> IterationSample {
        IterationSample {
            elapsed_ms,
            outcome: IterationOutcome::Failure {
                code: Some(code.to_string()),
            },
            prove_stats: super::ArtifactStats { count: 0, bytes: 0 },
            inv_stats: super::ArtifactStats {
                count: 1,
                bytes: 99,
            },
        }
    }

    #[test]
    fn suite_selection_matches_contract() {
        assert_eq!(suite_fixtures(BenchSuite::Full).len(), 6);
        assert_eq!(suite_fixtures(BenchSuite::Quick).len(), 4);
    }

    #[test]
    fn median_is_stable_for_even_and_odd_counts() {
        assert_eq!(median_u64(&[9, 1, 3]), 3);
        assert_eq!(median_u64(&[20, 10, 30, 40]), 20);
    }

    #[test]
    fn outcome_matching_respects_expected_codes() {
        assert!(outcome_matches(None, &IterationOutcome::Success));
        assert!(outcome_matches(
            Some("OAC-INV-001"),
            &IterationOutcome::Failure {
                code: Some("OAC-INV-001".to_string())
            }
        ));
        assert!(!outcome_matches(
            Some("OAC-INV-001"),
            &IterationOutcome::Failure {
                code: Some("OAC-PROVE-001".to_string())
            }
        ));
        assert!(!outcome_matches(
            None,
            &IterationOutcome::Failure { code: None }
        ));
    }

    #[test]
    fn quick_run_writes_valid_report_json() {
        let dir = tempdir().expect("tempdir");
        let baseline_path = dir.path().join("baseline.json");
        let output_path = dir.path().join("report.json");
        let baseline = ProveBenchBaseline {
            schema_version: 1,
            thresholds: RegressionThresholds {
                regression_pct: 20.0,
                regression_ms: 200,
            },
            fixtures: vec![
                BaselineFixture {
                    id: "prove_pass".to_string(),
                    source: "crates/oac/execution_tests/prove_pass.oa".to_string(),
                    expected_code: None,
                    baseline_elapsed_ms: 100,
                    baseline_prove_smt2_count: 1,
                    baseline_prove_smt2_bytes: 10,
                    baseline_inv_smt2_count: 0,
                    baseline_inv_smt2_bytes: 0,
                },
                BaselineFixture {
                    id: "prove_fail".to_string(),
                    source: "crates/oac/execution_tests/prove_fail.oa".to_string(),
                    expected_code: Some("OAC-PROVE-001".to_string()),
                    baseline_elapsed_ms: 100,
                    baseline_prove_smt2_count: 1,
                    baseline_prove_smt2_bytes: 10,
                    baseline_inv_smt2_count: 0,
                    baseline_inv_smt2_bytes: 0,
                },
                BaselineFixture {
                    id: "struct_invariant_pass".to_string(),
                    source: "crates/oac/execution_tests/struct_invariant_pass.oa".to_string(),
                    expected_code: None,
                    baseline_elapsed_ms: 100,
                    baseline_prove_smt2_count: 0,
                    baseline_prove_smt2_bytes: 0,
                    baseline_inv_smt2_count: 1,
                    baseline_inv_smt2_bytes: 50,
                },
                BaselineFixture {
                    id: "struct_invariant_fail".to_string(),
                    source: "crates/oac/execution_tests/struct_invariant_fail.oa".to_string(),
                    expected_code: Some("OAC-INV-001".to_string()),
                    baseline_elapsed_ms: 100,
                    baseline_prove_smt2_count: 0,
                    baseline_prove_smt2_bytes: 0,
                    baseline_inv_smt2_count: 1,
                    baseline_inv_smt2_bytes: 50,
                },
            ],
        };
        super::write_json_file(&baseline_path, &baseline).expect("write baseline");

        let opts = BenchProveOpts {
            suite: BenchSuite::Quick,
            iterations: 1,
            baseline: Some(baseline_path),
            output: Some(output_path.clone()),
            update_baseline: false,
        };

        let result = run_with_runner(dir.path(), &opts, |_current_dir, fixture, _iter, _root| {
            let sample = match fixture.id {
                "prove_pass" => sample_success(80),
                "prove_fail" => sample_failure(90, "OAC-PROVE-001"),
                "struct_invariant_pass" => sample_success(105),
                "struct_invariant_fail" => sample_failure(120, "OAC-INV-001"),
                _ => panic!("unexpected fixture"),
            };
            Ok(sample)
        })
        .expect("run benchmark");

        assert!(result.unexpected.is_empty());
        let raw = std::fs::read_to_string(&output_path).expect("read report");
        let parsed = serde_json::from_str::<super::ProveBenchReport>(&raw).expect("parse report");
        assert_eq!(parsed.schema_version, 1);
        assert_eq!(parsed.fixtures.len(), 4);
        assert_eq!(parsed.summary.total_fixtures, 4);
    }

    #[test]
    fn update_baseline_is_deterministic() {
        let dir = tempdir().expect("tempdir");
        let baseline_path = dir.path().join("baseline.json");
        let output_path = dir.path().join("report.json");
        let opts = BenchProveOpts {
            suite: BenchSuite::Full,
            iterations: 1,
            baseline: Some(baseline_path.clone()),
            output: Some(output_path),
            update_baseline: true,
        };

        run_with_runner(dir.path(), &opts, |_current_dir, fixture, _iter, _root| {
            if fixture.expected_code.is_some() {
                let code = fixture.expected_code.expect("expected code");
                Ok(sample_failure(200, code))
            } else {
                Ok(sample_success(100))
            }
        })
        .expect("first baseline update");
        let first = std::fs::read_to_string(&baseline_path).expect("baseline text");

        run_with_runner(dir.path(), &opts, |_current_dir, fixture, _iter, _root| {
            if fixture.expected_code.is_some() {
                let code = fixture.expected_code.expect("expected code");
                Ok(sample_failure(200, code))
            } else {
                Ok(sample_success(100))
            }
        })
        .expect("second baseline update");
        let second = std::fs::read_to_string(&baseline_path).expect("baseline text");

        assert_eq!(first, second);
    }
}
