mod builtins;
mod comptime;
mod diagnostics;
mod flat_imports;
mod invariant_metadata;
mod ir;
mod lsp;
mod parser;
mod prove;
mod qbe_backend;
mod riscv_smt; // Add the new module
mod struct_invariants;
mod test_framework;
mod tokenizer;
mod verification_cycles;

use std::collections::HashSet;
use std::env;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use clap::Parser;
use diagnostics::{
    diagnostic_from_anyhow, diagnostic_from_panic, diagnostic_from_tokenizer_error,
    CompilerDiagnostic, CompilerDiagnosticBundle, DiagnosticStage,
};
use tracing::info;
use tracing::{debug, trace, warn};
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{fmt, EnvFilter, Layer};

fn main() {
    let outcome = std::panic::catch_unwind(|| {
        initialize_logging();
        run()
    });

    match outcome {
        Ok(Ok(())) => {}
        Ok(Err(bundle)) => {
            eprintln!("{}", bundle.render_terminal_auto());
            std::process::exit(1);
        }
        Err(payload) => {
            let bundle = CompilerDiagnosticBundle::single(diagnostic_from_panic(payload));
            eprintln!("{}", bundle.render_terminal_auto());
            std::process::exit(101);
        }
    }
}

fn run() -> Result<(), CompilerDiagnosticBundle> {
    let oac = Oac::parse();

    match oac.subcmd {
        OacSubcommand::Build(build) => {
            let current_dir = std::env::current_dir().map_err(|err| {
                io_stage_error("OAC-IO-001", "failed to get current directory", err)
            })?;
            compile(&current_dir, build)?;
        }
        OacSubcommand::Test(test) => {
            let current_dir = std::env::current_dir().map_err(|err| {
                io_stage_error("OAC-IO-002", "failed to get current directory", err)
            })?;
            run_tests(&current_dir, test)?;
        }
        OacSubcommand::Lsp(_) => {
            lsp::run().map_err(|err| {
                CompilerDiagnosticBundle::from_anyhow(
                    DiagnosticStage::Internal,
                    "OAC-LSP-001",
                    "language server failed",
                    &err,
                    None,
                    None,
                )
            })?;
        }
        OacSubcommand::RiscvSmt(riscv_smt_opts) => {
            let current_dir = std::env::current_dir().map_err(|err| {
                io_stage_error("OAC-IO-003", "failed to get current directory", err)
            })?;
            process_riscv_smt(&current_dir, riscv_smt_opts)?;
        }
    }

    Ok(())
}

fn process_riscv_smt(
    _current_dir: &Path,
    opts: RiscvSmtOpts,
) -> Result<(), CompilerDiagnosticBundle> {
    let elf_path = Path::new(&opts.elf_file);
    if opts.check {
        let result = riscv_smt::check_returns_zero_within_cycles(elf_path).map_err(|err| {
            CompilerDiagnosticBundle::from_anyhow(
                DiagnosticStage::Resolve,
                "OAC-RISCV-001",
                "failed to run RISC-V SMT check",
                &err,
                None,
                None,
            )
        })?;
        if result {
            println!(
                "Program {} is SATISFIABLE to return 0 within {} cycles.",
                opts.elf_file,
                riscv_smt::MAX_CYCLES
            );
        } else {
            println!(
                "Program {} is UNSATISFIABLE to return 0 within {} cycles.",
                opts.elf_file,
                riscv_smt::MAX_CYCLES
            );
        }
    } else {
        let smt_expression =
            riscv_smt::elf_to_smt_returns_zero_within_cycles(elf_path).map_err(|err| {
                CompilerDiagnosticBundle::from_anyhow(
                    DiagnosticStage::Resolve,
                    "OAC-RISCV-002",
                    "failed to build RISC-V SMT expression",
                    &err,
                    None,
                    None,
                )
            })?;
        if let Some(output_path) = opts.output {
            std::fs::write(&output_path, smt_expression).map_err(|err| {
                io_stage_error(
                    "OAC-IO-004",
                    format!("failed to write SMT output {}", output_path),
                    err,
                )
            })?;
            info!("SMT expression written to {}", output_path);
        } else {
            println!("{}", smt_expression);
        }
    }
    Ok(())
}

fn compile(current_dir: &Path, build: Build) -> Result<(), CompilerDiagnosticBundle> {
    let target_dir = current_dir.join("target").join("oac");
    std::fs::create_dir_all(&target_dir).map_err(|err| {
        io_stage_error(
            "OAC-IO-005",
            format!("failed to create target directory {}", target_dir.display()),
            err,
        )
    })?;

    let source_path = Path::new(&build.source);
    let source = std::fs::read_to_string(source_path).map_err(|err| {
        io_stage_error(
            "OAC-IO-006",
            format!("failed to read source {}", source_path.display()),
            err,
        )
    })?;
    trace!(source_len = source.len(), "Read input file");

    let tokens = tokenizer::tokenize(source.clone()).map_err(|err| {
        CompilerDiagnosticBundle::single(diagnostic_from_tokenizer_error(
            "OAC-TOKENIZE-001",
            &source,
            Some(source_path),
            &err,
        ))
    })?;
    let tokens_path = target_dir.join("tokens.json");
    let tokens_json = serde_json::to_string_pretty(&tokens)
        .map_err(|err| io_stage_error("OAC-IO-007", "failed to serialize tokens", err))?;
    std::fs::write(&tokens_path, tokens_json).map_err(|err| {
        io_stage_error(
            "OAC-IO-008",
            format!("failed to write {}", tokens_path.display()),
            err,
        )
    })?;
    trace!(tokens_path = %tokens_path.display(), "Tokenized source file");

    let root_ast = parser::parse(tokens).map_err(|err| {
        stage_error_from_anyhow(
            DiagnosticStage::Parse,
            "OAC-PARSE-001",
            "failed to parse source",
            err,
            Some(source_path),
            Some(&source),
        )
    })?;
    let mut ast = flat_imports::resolve_ast(root_ast, source_path).map_err(|err| {
        stage_error_from_anyhow(
            DiagnosticStage::Import,
            "OAC-IMPORT-001",
            "failed to resolve imports",
            err,
            Some(source_path),
            Some(&source),
        )
    })?;
    comptime::execute_comptime_applies(&mut ast).map_err(|err| {
        stage_error_from_anyhow(
            DiagnosticStage::Comptime,
            "OAC-COMPTIME-001",
            "failed to execute comptime applies",
            err,
            Some(source_path),
            Some(&source),
        )
    })?;
    let ast_path = target_dir.join("ast.json");
    let ast_json = serde_json::to_string_pretty(&ast)
        .map_err(|err| io_stage_error("OAC-IO-009", "failed to serialize AST", err))?;
    std::fs::write(&ast_path, ast_json).map_err(|err| {
        io_stage_error(
            "OAC-IO-010",
            format!("failed to write {}", ast_path.display()),
            err,
        )
    })?;
    debug!(ast_path = %ast_path.display(), "Parsed source file");

    compile_ast_to_executable(
        &target_dir,
        ast,
        build.arch.as_deref(),
        "app",
        Some(source_path),
        Some(&source),
    )?;

    Ok(())
}

fn run_tests(current_dir: &Path, test: Test) -> Result<(), CompilerDiagnosticBundle> {
    let target_dir = current_dir.join("target").join("oac").join("test");
    std::fs::create_dir_all(&target_dir).map_err(|err| {
        io_stage_error(
            "OAC-IO-011",
            format!(
                "failed to create test target directory {}",
                target_dir.display()
            ),
            err,
        )
    })?;

    let source_path = Path::new(&test.source);
    let source = std::fs::read_to_string(source_path).map_err(|err| {
        io_stage_error(
            "OAC-IO-012",
            format!("failed to read source {}", source_path.display()),
            err,
        )
    })?;
    trace!(source_len = source.len(), "Read test source file");

    let tokens = tokenizer::tokenize(source.clone()).map_err(|err| {
        CompilerDiagnosticBundle::single(diagnostic_from_tokenizer_error(
            "OAC-TOKENIZE-002",
            &source,
            Some(source_path),
            &err,
        ))
    })?;
    let tokens_path = target_dir.join("tokens.json");
    let tokens_json = serde_json::to_string_pretty(&tokens)
        .map_err(|err| io_stage_error("OAC-IO-013", "failed to serialize tokens", err))?;
    std::fs::write(&tokens_path, tokens_json).map_err(|err| {
        io_stage_error(
            "OAC-IO-014",
            format!("failed to write {}", tokens_path.display()),
            err,
        )
    })?;
    trace!(tokens_path = %tokens_path.display(), "Tokenized test source file");

    let root_ast = parser::parse(tokens).map_err(|err| {
        stage_error_from_anyhow(
            DiagnosticStage::Parse,
            "OAC-PARSE-002",
            "failed to parse test source",
            err,
            Some(source_path),
            Some(&source),
        )
    })?;
    let mut ast = flat_imports::resolve_ast(root_ast, source_path).map_err(|err| {
        stage_error_from_anyhow(
            DiagnosticStage::Import,
            "OAC-IMPORT-002",
            "failed to resolve test imports",
            err,
            Some(source_path),
            Some(&source),
        )
    })?;
    comptime::execute_comptime_applies(&mut ast).map_err(|err| {
        stage_error_from_anyhow(
            DiagnosticStage::Comptime,
            "OAC-COMPTIME-002",
            "failed to execute test comptime applies",
            err,
            Some(source_path),
            Some(&source),
        )
    })?;

    let lowered = test_framework::lower_tests_to_program(ast).map_err(|err| {
        stage_error_from_anyhow(
            DiagnosticStage::Resolve,
            "OAC-TEST-001",
            "failed to lower test declarations",
            err,
            Some(source_path),
            Some(&source),
        )
    })?;
    let test_count = lowered.test_names.len();
    let lowered_ast = lowered.ast;
    let ast_path = target_dir.join("ast.json");
    let ast_json = serde_json::to_string_pretty(&lowered_ast)
        .map_err(|err| io_stage_error("OAC-IO-015", "failed to serialize lowered AST", err))?;
    std::fs::write(&ast_path, ast_json).map_err(|err| {
        io_stage_error(
            "OAC-IO-016",
            format!("failed to write {}", ast_path.display()),
            err,
        )
    })?;
    debug!(ast_path = %ast_path.display(), "Lowered test AST");

    let executable_path = compile_ast_to_executable(
        &target_dir,
        lowered_ast,
        None,
        "app",
        Some(source_path),
        Some(&source),
    )?;

    let output = std::process::Command::new(&executable_path)
        .output()
        .map_err(|err| {
            io_stage_error(
                "OAC-IO-017",
                format!(
                    "failed to execute test binary {}",
                    executable_path.display()
                ),
                err,
            )
        })?;
    print!("{}", String::from_utf8_lossy(&output.stdout));
    eprint!("{}", String::from_utf8_lossy(&output.stderr));
    if !output.status.success() {
        let exit_code = output
            .status
            .code()
            .map_or("signal".to_string(), |code| code.to_string());
        let diagnostic = CompilerDiagnostic::new(
            "OAC-TEST-002",
            DiagnosticStage::Io,
            format!(
                "test run failed after launching {} test(s) (exit code: {})",
                test_count, exit_code
            ),
        )
        .with_note("runtime assertion failures exit with code 242");
        return Err(CompilerDiagnosticBundle::single(diagnostic));
    }

    println!("test run passed: {} test(s)", test_count);
    Ok(())
}

fn compile_ast_to_executable(
    target_dir: &Path,
    ast: parser::Ast,
    arch: Option<&str>,
    executable_name: &str,
    source_path: Option<&Path>,
    source_text: Option<&str>,
) -> Result<PathBuf, CompilerDiagnosticBundle> {
    let ir = ir::resolve(ast).map_err(|err| {
        stage_error_from_anyhow(
            DiagnosticStage::Resolve,
            "OAC-RESOLVE-001",
            "failed to resolve/type-check program",
            err,
            source_path,
            source_text,
        )
    })?;
    let ir_path = target_dir.join("ir.json");
    let ir_json = serde_json::to_string_pretty(&ir)
        .map_err(|err| io_stage_error("OAC-IO-018", "failed to serialize IR", err))?;
    std::fs::write(&ir_path, ir_json).map_err(|err| {
        io_stage_error(
            "OAC-IO-019",
            format!("failed to write {}", ir_path.display()),
            err,
        )
    })?;
    info!(ir_path = %ir_path.display(), "IR generated and type-checked");
    let qbe_ir = qbe_backend::compile(ir.clone());
    prove::verify_prove_obligations_with_qbe(&ir, &qbe_ir, target_dir).map_err(|err| {
        stage_error_from_anyhow(
            DiagnosticStage::Prove,
            "OAC-PROVE-001",
            "prove obligation verification failed",
            err,
            source_path,
            source_text,
        )
    })?;
    struct_invariants::verify_struct_invariants_with_qbe(&ir, &qbe_ir, target_dir).map_err(
        |err| {
            stage_error_from_anyhow(
                DiagnosticStage::StructInvariant,
                "OAC-INV-001",
                "struct invariant verification failed",
                err,
                source_path,
                source_text,
            )
        },
    )?;
    reject_proven_non_terminating_main(&qbe_ir).map_err(|err| {
        stage_error_from_anyhow(
            DiagnosticStage::LoopClassifier,
            "OAC-LOOP-001",
            "loop non-termination classification failed",
            err,
            source_path,
            source_text,
        )
    })?;
    let qbe_ir_text = qbe_ir.to_string();

    let qbe_ir_path = target_dir.join("ir.qbe");
    std::fs::write(&qbe_ir_path, &qbe_ir_text).map_err(|err| {
        io_stage_error(
            "OAC-IO-020",
            format!("failed to write {}", qbe_ir_path.display()),
            err,
        )
    })?;
    info!(qbe_ir_path = %qbe_ir_path.display(), "QBE IR generated");

    let assembly_path = target_dir.join("assembly.s");
    let mut qbe_cmd = std::process::Command::new("qbe");

    if let Some(arch) = arch {
        qbe_cmd.arg("-t").arg(arch);
    }

    let qbe_output = qbe_cmd
        .arg("-o")
        .arg(&assembly_path)
        .arg(&qbe_ir_path)
        .output()
        .map_err(|err| io_stage_error("OAC-IO-021", "failed to run qbe", err))?;

    if !qbe_output.status.success() {
        let stderr = String::from_utf8_lossy(&qbe_output.stderr)
            .trim()
            .to_string();
        let diagnostic = CompilerDiagnostic::new(
            "OAC-QBE-001",
            DiagnosticStage::Qbe,
            "compilation of QBE IR to assembly failed",
        )
        .with_note("valid archs: amd64_sysv, amd64_apple, arm64, arm64_apple, rv64")
        .with_note(stderr);
        return Err(CompilerDiagnosticBundle::single(diagnostic));
    }

    debug!(assembly_path = %assembly_path.display(), "QBE IR compiled to assembly");

    let executable_path = target_dir.join(executable_name);
    let linker_attempts = resolve_linker_attempts(arch).map_err(|err| {
        stage_error_from_anyhow(
            DiagnosticStage::Linker,
            "OAC-LINK-001",
            "failed to resolve linker configuration",
            err,
            None,
            None,
        )
    })?;
    let mut failures = Vec::new();

    for attempt in linker_attempts {
        let command_display = format_linker_command(
            &attempt.program,
            &attempt.args,
            &executable_path,
            &assembly_path,
        );

        let mut cc_cmd = std::process::Command::new(&attempt.program);
        cc_cmd
            .args(&attempt.args)
            .arg("-g")
            .arg("-o")
            .arg(&executable_path)
            .arg(&assembly_path);

        let cc_output = match cc_cmd.output() {
            Ok(output) => output,
            Err(err) => {
                failures.push(format!("{command_display}: failed to start: {err}"));
                continue;
            }
        };

        let stderr = String::from_utf8_lossy(&cc_output.stderr);
        if cc_output.status.success() {
            if !stderr.trim().is_empty() {
                eprintln!("{stderr}");
            }
            info!(
                executable_path = %executable_path.display(),
                linker = %command_display,
                "Assembly compiled to executable"
            );
            return Ok(executable_path);
        }

        failures.push(format!(
            "{command_display}: {}",
            format_status_and_stderr(&cc_output.status, &stderr)
        ));
    }

    let mut diagnostic = CompilerDiagnostic::new(
        "OAC-LINK-002",
        DiagnosticStage::Linker,
        format!(
            "compilation of assembly to executable failed after trying {} linker command(s)",
            failures.len()
        ),
    );
    for failure in failures {
        diagnostic = diagnostic.with_note(failure);
    }
    Err(CompilerDiagnosticBundle::single(diagnostic))
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct LinkerAttempt {
    program: String,
    args: Vec<String>,
}

fn resolve_linker_attempts(arch: Option<&str>) -> anyhow::Result<Vec<LinkerAttempt>> {
    let configured_command = env::var("OAC_CC")
        .ok()
        .map(|raw| ("OAC_CC", raw))
        .or_else(|| env::var("CC").ok().map(|raw| ("CC", raw)));
    let target_override = env::var("OAC_CC_TARGET").ok();
    let extra_flags = env::var("OAC_CC_FLAGS")
        .ok()
        .map(|raw| split_words(&raw))
        .unwrap_or_default();

    resolve_linker_attempts_for_config(
        arch,
        configured_command
            .as_ref()
            .map(|(name, raw)| (*name, raw.as_str())),
        target_override.as_deref(),
        &extra_flags,
    )
}

fn resolve_linker_attempts_for_config(
    arch: Option<&str>,
    configured_command: Option<(&str, &str)>,
    target_override: Option<&str>,
    extra_flags: &[String],
) -> anyhow::Result<Vec<LinkerAttempt>> {
    let mut attempts = Vec::new();
    let mut include_defaults = true;

    if let Some((var_name, raw_command)) = configured_command {
        let mut words = split_words(raw_command);
        if words.is_empty() {
            return Err(anyhow::anyhow!("{var_name} must not be empty"));
        }

        let program = words.remove(0);
        let mut args = words;
        if let Some(target) = target_override {
            args.push(format!("--target={target}"));
        }
        args.extend(extra_flags.iter().cloned());
        attempts.push(LinkerAttempt { program, args });
        include_defaults = var_name != "OAC_CC";
    }

    if !include_defaults {
        return Ok(dedup_linker_attempts(attempts));
    }

    if let Some(target) = target_override
        .map(std::borrow::ToOwned::to_owned)
        .or_else(|| {
            arch.and_then(default_target_triple_for_qbe_arch)
                .map(str::to_owned)
        })
    {
        attempts.push(LinkerAttempt {
            program: "cc".to_string(),
            args: vec![format!("--target={target}")],
        });
        attempts.push(LinkerAttempt {
            program: "clang".to_string(),
            args: vec![format!("--target={target}")],
        });
    }

    if let Some(arch) = arch {
        if let Some(cross_cc) = default_gnu_cross_cc_for_qbe_arch(arch) {
            attempts.push(LinkerAttempt {
                program: cross_cc.to_string(),
                args: Vec::new(),
            });
        }
    }

    attempts.push(LinkerAttempt {
        program: "cc".to_string(),
        args: Vec::new(),
    });

    let configured_prefix = configured_command.map(|(var, _)| var);
    for (idx, attempt) in attempts.iter_mut().enumerate() {
        if idx == 0 && matches!(configured_prefix, Some("CC")) {
            continue;
        }
        attempt.args.extend(extra_flags.iter().cloned());
    }

    Ok(dedup_linker_attempts(attempts))
}

fn default_target_triple_for_qbe_arch(arch: &str) -> Option<&'static str> {
    match arch {
        "amd64_sysv" => Some("x86_64-linux-gnu"),
        "amd64_apple" => Some("x86_64-apple-darwin"),
        "arm64" => Some("aarch64-linux-gnu"),
        "arm64_apple" => Some("aarch64-apple-darwin"),
        "rv64" => Some("riscv64-linux-gnu"),
        _ => None,
    }
}

fn default_gnu_cross_cc_for_qbe_arch(arch: &str) -> Option<&'static str> {
    match arch {
        "amd64_sysv" => Some("x86_64-linux-gnu-gcc"),
        "arm64" => Some("aarch64-linux-gnu-gcc"),
        "rv64" => Some("riscv64-linux-gnu-gcc"),
        _ => None,
    }
}

fn split_words(raw: &str) -> Vec<String> {
    raw.split_whitespace().map(str::to_owned).collect()
}

fn dedup_linker_attempts(attempts: Vec<LinkerAttempt>) -> Vec<LinkerAttempt> {
    let mut seen = HashSet::new();
    let mut deduped = Vec::new();
    for attempt in attempts {
        if seen.insert(attempt.clone()) {
            deduped.push(attempt);
        }
    }
    deduped
}

fn format_linker_command(
    program: &str,
    args: &[String],
    executable: &Path,
    assembly: &Path,
) -> String {
    let mut parts = Vec::new();
    parts.push(program.to_string());
    parts.extend(args.iter().cloned());
    parts.push("-g".to_string());
    parts.push("-o".to_string());
    parts.push(executable.display().to_string());
    parts.push(assembly.display().to_string());
    parts.join(" ")
}

fn format_status_and_stderr(status: &std::process::ExitStatus, stderr: &str) -> String {
    let status_text = status.code().map_or_else(
        || "terminated by signal".to_string(),
        |code| format!("exit code {code}"),
    );
    let stderr = stderr.trim();
    if stderr.is_empty() {
        status_text
    } else {
        format!("{status_text}: {stderr}")
    }
}

fn reject_proven_non_terminating_main(qbe_module: &qbe::Module) -> anyhow::Result<()> {
    let Some(main_function) = qbe_module.functions.iter().find(|f| f.name == "main") else {
        return Ok(());
    };

    let proofs = match qbe_smt::classify_simple_loops(main_function) {
        Ok(proofs) => proofs,
        Err(err) => {
            warn!(
                "non-termination classifier skipped due to unsupported main QBE shape: {}",
                err
            );
            return Ok(());
        }
    };

    let mut findings = Vec::new();
    for proof in proofs {
        if proof.status == qbe_smt::LoopProofStatus::NonTerminating {
            findings.push(proof);
        }
    }

    if findings.is_empty() {
        return Ok(());
    }

    let mut message = String::from("proven non-terminating loop(s) in `main`:\n");
    for finding in findings {
        message.push_str(&format!(
            "- @{}: {}\n",
            finding.header_label, finding.reason
        ));
    }

    Err(anyhow::anyhow!(message.trim_end().to_string()))
}
fn initialize_logging() {
    let env_filter = env::var("RUST_LOG").unwrap_or_default();
    let parsed_filter = EnvFilter::from_str(&env_filter).unwrap_or_else(|_| EnvFilter::default());

    tracing_subscriber::registry()
        .with(
            fmt::layer()
                .with_writer(std::io::stderr)
                .with_filter(parsed_filter),
        )
        .init();
}

fn io_stage_error(
    code: &str,
    message: impl Into<String>,
    err: impl Into<anyhow::Error>,
) -> CompilerDiagnosticBundle {
    let error = err.into();
    let mut diagnostic = CompilerDiagnostic::new(code, DiagnosticStage::Io, message.into());
    for cause in error.chain() {
        diagnostic = diagnostic.with_note(cause.to_string());
    }
    CompilerDiagnosticBundle::single(diagnostic)
}

fn stage_error_from_anyhow(
    stage: DiagnosticStage,
    code: &str,
    message: impl Into<String>,
    err: anyhow::Error,
    source_path: Option<&Path>,
    source_text: Option<&str>,
) -> CompilerDiagnosticBundle {
    CompilerDiagnosticBundle::single(diagnostic_from_anyhow(
        stage,
        code,
        message,
        &err,
        source_path,
        source_text,
    ))
}

#[derive(clap::Parser)]
struct Oac {
    #[clap(subcommand)]
    subcmd: OacSubcommand,
}

#[derive(clap::Subcommand)]
enum OacSubcommand {
    Build(Build),
    Test(Test),
    Lsp(LspOpts),
    RiscvSmt(RiscvSmtOpts),
}

#[derive(clap::Parser)]
struct Build {
    source: String,
    arch: Option<String>,
}

#[derive(clap::Parser)]
struct Test {
    source: String,
}

#[derive(clap::Parser, Debug)]
#[clap(name = "lsp", about = "Run the Ousia Language Server over stdio.")]
struct LspOpts {}

#[derive(clap::Parser, Debug)]
#[clap(
    name = "riscv-smt",
    about = "Turn a RISC-V ELF into an SMT expression."
)]
struct RiscvSmtOpts {
    /// Path to the RISC-V ELF file
    #[clap(short, long)]
    elf_file: String,

    /// Output SMT file path (optional, prints to stdout if not provided)
    #[clap(short, long)]
    output: Option<String>,

    /// Check if the program returns 0 within MAX_CYCLES instead of generating SMT
    #[clap(short, long, default_value = "false")]
    check: bool,
}

#[cfg(test)]
mod tests {
    use super::{
        reject_proven_non_terminating_main, resolve_linker_attempts_for_config, LinkerAttempt,
    };
    use qbe::{Block, BlockItem, Cmp, Function, Instr, Linkage, Module, Statement, Type, Value};

    fn temp(name: &str) -> Value {
        Value::Temporary(name.to_string())
    }

    fn assign(dest: &str, ty: Type, instr: Instr) -> Statement {
        Statement::Assign(temp(dest), ty, instr)
    }

    fn volatile(instr: Instr) -> Statement {
        Statement::Volatile(instr)
    }

    fn block(label: &str, statements: Vec<Statement>) -> Block {
        Block {
            label: label.to_string(),
            items: statements
                .into_iter()
                .map(BlockItem::Statement)
                .collect::<Vec<_>>(),
        }
    }

    fn module_with_main(blocks: Vec<Block>) -> Module {
        Module {
            functions: vec![Function {
                linkage: Linkage::default(),
                name: "main".to_string(),
                arguments: vec![],
                return_ty: Some(Type::Word),
                blocks,
            }],
            types: vec![],
            data: vec![],
        }
    }

    #[test]
    fn rejects_proven_non_terminating_loop_in_main() {
        let module = module_with_main(vec![
            block(
                "start",
                vec![assign("i", Type::Word, Instr::Copy(Value::Const(7)))],
            ),
            block(
                "while_cond",
                vec![
                    assign("zero", Type::Word, Instr::Copy(Value::Const(0))),
                    assign(
                        "cond",
                        Type::Word,
                        Instr::Cmp(Type::Word, Cmp::Sgt, temp("i"), temp("zero")),
                    ),
                    volatile(Instr::Jnz(
                        temp("cond"),
                        "while_body".to_string(),
                        "while_end".to_string(),
                    )),
                ],
            ),
            block(
                "while_body",
                vec![
                    assign(
                        "next",
                        Type::Word,
                        Instr::Call(
                            "sub".to_string(),
                            vec![(Type::Word, temp("i")), (Type::Word, Value::Const(0))],
                            None,
                        ),
                    ),
                    assign("i", Type::Word, Instr::Copy(temp("next"))),
                    volatile(Instr::Jmp("while_cond".to_string())),
                ],
            ),
            block(
                "while_end",
                vec![volatile(Instr::Ret(Some(Value::Const(0))))],
            ),
        ]);

        let err = reject_proven_non_terminating_main(&module).expect_err("expected rejection");
        assert!(err.to_string().contains("proven non-terminating loop"));
    }

    #[test]
    fn allows_unknown_or_terminating_loops() {
        let module = module_with_main(vec![
            block(
                "start",
                vec![assign("i", Type::Word, Instr::Copy(Value::Const(7)))],
            ),
            block(
                "while_cond",
                vec![
                    assign(
                        "cond",
                        Type::Word,
                        Instr::Cmp(Type::Word, Cmp::Sgt, temp("i"), Value::Const(0)),
                    ),
                    volatile(Instr::Jnz(
                        temp("cond"),
                        "while_body".to_string(),
                        "while_end".to_string(),
                    )),
                ],
            ),
            block(
                "while_body",
                vec![
                    assign("next", Type::Word, Instr::Sub(temp("i"), Value::Const(1))),
                    assign("i", Type::Word, Instr::Copy(temp("next"))),
                    volatile(Instr::Jmp("while_cond".to_string())),
                ],
            ),
            block(
                "while_end",
                vec![volatile(Instr::Ret(Some(Value::Const(0))))],
            ),
        ]);

        reject_proven_non_terminating_main(&module).expect("unknown loops should pass");
    }

    #[test]
    fn linker_attempts_default_to_cc_for_host_builds() {
        let attempts =
            resolve_linker_attempts_for_config(None, None, None, &[]).expect("attempt resolution");
        assert_eq!(
            attempts,
            vec![LinkerAttempt {
                program: "cc".to_string(),
                args: Vec::new(),
            }]
        );
    }

    #[test]
    fn linker_attempts_for_rv64_include_cross_fallbacks() {
        let attempts = resolve_linker_attempts_for_config(Some("rv64"), None, None, &[])
            .expect("attempt resolution");

        assert_eq!(
            attempts[0],
            LinkerAttempt {
                program: "cc".to_string(),
                args: vec!["--target=riscv64-linux-gnu".to_string()],
            }
        );

        assert!(attempts.contains(&LinkerAttempt {
            program: "clang".to_string(),
            args: vec!["--target=riscv64-linux-gnu".to_string()],
        }));
        assert!(attempts.contains(&LinkerAttempt {
            program: "riscv64-linux-gnu-gcc".to_string(),
            args: Vec::new(),
        }));
        assert!(attempts.contains(&LinkerAttempt {
            program: "cc".to_string(),
            args: Vec::new(),
        }));
    }

    #[test]
    fn configured_linker_command_is_respected() {
        let extra_flags = vec!["-static".to_string()];
        let attempts = resolve_linker_attempts_for_config(
            Some("rv64"),
            Some(("OAC_CC", "custom-cc --driver-mode=clang")),
            None,
            &extra_flags,
        )
        .expect("attempt resolution");

        assert_eq!(
            attempts,
            vec![LinkerAttempt {
                program: "custom-cc".to_string(),
                args: vec!["--driver-mode=clang".to_string(), "-static".to_string()],
            }]
        );
    }

    #[test]
    fn configured_linker_target_override_is_applied() {
        let attempts = resolve_linker_attempts_for_config(
            Some("rv64"),
            Some(("OAC_CC", "clang")),
            Some("aarch64-linux-gnu"),
            &[],
        )
        .expect("attempt resolution");

        assert_eq!(
            attempts,
            vec![LinkerAttempt {
                program: "clang".to_string(),
                args: vec!["--target=aarch64-linux-gnu".to_string()],
            }]
        );
    }

    #[test]
    fn cc_env_keeps_default_fallbacks() {
        let attempts = resolve_linker_attempts_for_config(
            Some("rv64"),
            Some(("CC", "clang")),
            Some("aarch64-linux-gnu"),
            &[],
        )
        .expect("attempt resolution");

        assert_eq!(
            attempts[0],
            LinkerAttempt {
                program: "clang".to_string(),
                args: vec!["--target=aarch64-linux-gnu".to_string()],
            }
        );

        assert!(attempts.contains(&LinkerAttempt {
            program: "cc".to_string(),
            args: vec!["--target=aarch64-linux-gnu".to_string()],
        }));
        assert!(attempts.contains(&LinkerAttempt {
            program: "cc".to_string(),
            args: Vec::new(),
        }));
    }
}
