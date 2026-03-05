mod ast_walk;
mod bench_prove;
mod builtins;
mod cli_output;
mod codegen_runtime;
mod comptime;
mod diagnostics;
mod flat_imports;
mod invariant_metadata;
mod ir;
mod llvm_backend;
mod lsp;
mod model_invariants;
mod parser;
mod prove;
mod qbe_backend;
mod riscv_smt;
mod runtime_layout;
mod struct_invariants;
mod symbol_keys;
mod test_framework;
mod tokenizer;
mod verification_checker;
mod verification_cycles;
mod verification_outcomes;
mod verification_profile;
mod verification_solver;

use std::collections::HashSet;
use std::env;
use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::time::Instant;

use clap::Parser;
use diagnostics::{
    diagnostic_from_anyhow, diagnostic_from_panic, diagnostic_from_tokenizer_error,
    CompilerDiagnostic, CompilerDiagnosticBundle, DiagnosticStage,
};
use tracing::{debug, info, trace, warn};
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{fmt, EnvFilter, Layer};

#[derive(Clone, Copy, Debug, Eq, PartialEq, clap::ValueEnum)]
pub(crate) enum RuntimeBackend {
    Qbe,
    Llvm,
}

impl RuntimeBackend {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            RuntimeBackend::Qbe => "qbe",
            RuntimeBackend::Llvm => "llvm",
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CodegenOptions {
    pub backend: RuntimeBackend,
    pub qbe_arch: Option<String>,
    pub target: Option<String>,
}

impl CodegenOptions {
    pub(crate) fn qbe_default() -> Self {
        Self {
            backend: RuntimeBackend::Qbe,
            qbe_arch: None,
            target: None,
        }
    }

    fn validate(&self) -> Result<(), CompilerDiagnosticBundle> {
        if self.backend == RuntimeBackend::Llvm && self.qbe_arch.is_some() {
            let diagnostic = CompilerDiagnostic::new(
                "OAC-CLI-001",
                DiagnosticStage::Internal,
                "--qbe-arch is only valid when --backend qbe",
            );
            return Err(CompilerDiagnosticBundle::single(diagnostic));
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DiagnosticColorMode {
    Auto,
    Explicit(bool),
}

impl DiagnosticColorMode {
    fn for_subcommand(subcommand: &OacSubcommand) -> Self {
        match subcommand {
            OacSubcommand::Build(build) => DiagnosticColorMode::Explicit(build.use_color()),
            OacSubcommand::Test(test) => DiagnosticColorMode::Explicit(test.use_color()),
            _ => DiagnosticColorMode::Auto,
        }
    }

    fn render_bundle(self, bundle: &CompilerDiagnosticBundle) -> String {
        match self {
            DiagnosticColorMode::Auto => bundle.render_terminal_auto(),
            DiagnosticColorMode::Explicit(use_color) => bundle.render_with_color(use_color),
        }
    }
}

fn main() {
    let oac = Oac::parse();
    let diagnostic_color_mode = DiagnosticColorMode::for_subcommand(&oac.subcmd);

    let outcome = std::panic::catch_unwind(|| {
        initialize_logging();
        run(oac)
    });

    match outcome {
        Ok(Ok(())) => {}
        Ok(Err(bundle)) => {
            eprintln!("{}", diagnostic_color_mode.render_bundle(&bundle));
            std::process::exit(1);
        }
        Err(payload) => {
            let bundle = CompilerDiagnosticBundle::single(diagnostic_from_panic(payload));
            eprintln!("{}", diagnostic_color_mode.render_bundle(&bundle));
            std::process::exit(101);
        }
    }
}

fn run(oac: Oac) -> Result<(), CompilerDiagnosticBundle> {
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
        OacSubcommand::BenchProve(bench_opts) => {
            let current_dir = std::env::current_dir().map_err(|err| {
                io_stage_error("OAC-IO-024", "failed to get current directory", err)
            })?;
            bench_prove::run(&current_dir, bench_opts)?;
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

#[derive(Clone, Copy)]
pub(crate) struct FrontendPipelineCodes<'a> {
    pub read_source_io_code: &'a str,
    pub tokenize_code: &'a str,
    pub serialize_tokens_io_code: &'a str,
    pub write_tokens_io_code: &'a str,
    pub parse_code: &'a str,
    pub parse_message: &'a str,
    pub import_code: &'a str,
    pub import_message: &'a str,
    pub comptime_code: &'a str,
    pub comptime_message: &'a str,
}

#[derive(Clone, Copy)]
pub(crate) struct CompileSourceCodes<'a> {
    pub frontend: FrontendPipelineCodes<'a>,
    pub serialize_ast_io_code: &'a str,
    pub write_ast_io_code: &'a str,
}

pub(crate) fn parse_source_to_ast_with_artifacts(
    source_path: &Path,
    target_dir: &Path,
    codes: &FrontendPipelineCodes<'_>,
) -> Result<(String, parser::Ast), CompilerDiagnosticBundle> {
    let source = std::fs::read_to_string(source_path).map_err(|err| {
        io_stage_error(
            codes.read_source_io_code,
            format!("failed to read source {}", source_path.display()),
            err,
        )
    })?;
    trace!(source_len = source.len(), "Read source file");

    let tokens = tokenizer::tokenize(source.clone()).map_err(|err| {
        CompilerDiagnosticBundle::single(diagnostic_from_tokenizer_error(
            codes.tokenize_code,
            &source,
            Some(source_path),
            &err,
        ))
    })?;
    let tokens_path = target_dir.join("tokens.json");
    let tokens_json = serde_json::to_string_pretty(&tokens).map_err(|err| {
        io_stage_error(
            codes.serialize_tokens_io_code,
            "failed to serialize tokens",
            err,
        )
    })?;
    std::fs::write(&tokens_path, tokens_json).map_err(|err| {
        io_stage_error(
            codes.write_tokens_io_code,
            format!("failed to write {}", tokens_path.display()),
            err,
        )
    })?;
    trace!(tokens_path = %tokens_path.display(), "Tokenized source file");

    let root_ast = parser::parse(tokens).map_err(|err| {
        stage_error_from_anyhow(
            DiagnosticStage::Parse,
            codes.parse_code,
            codes.parse_message,
            err,
            Some(source_path),
            Some(&source),
        )
    })?;
    let mut ast = flat_imports::resolve_ast(root_ast, source_path).map_err(|err| {
        stage_error_from_anyhow(
            DiagnosticStage::Import,
            codes.import_code,
            codes.import_message,
            err,
            Some(source_path),
            Some(&source),
        )
    })?;
    comptime::execute_comptime_applies(&mut ast).map_err(|err| {
        stage_error_from_anyhow(
            DiagnosticStage::Comptime,
            codes.comptime_code,
            codes.comptime_message,
            err,
            Some(source_path),
            Some(&source),
        )
    })?;

    Ok((source, ast))
}

pub(crate) fn compile_source_with_artifacts(
    source_path: &Path,
    target_dir: &Path,
    codegen_options: CodegenOptions,
    executable_name: &str,
    codes: CompileSourceCodes<'_>,
) -> Result<PathBuf, CompilerDiagnosticBundle> {
    compile_source_with_artifacts_with_profile_and_reporter(
        source_path,
        target_dir,
        codegen_options,
        executable_name,
        codes,
        verification_profile::VerificationProfile::default(),
        None,
    )
}

pub(crate) fn compile_source_with_artifacts_with_profile(
    source_path: &Path,
    target_dir: &Path,
    codegen_options: CodegenOptions,
    executable_name: &str,
    codes: CompileSourceCodes<'_>,
    verification_profile: verification_profile::VerificationProfile,
) -> Result<PathBuf, CompilerDiagnosticBundle> {
    compile_source_with_artifacts_with_profile_and_reporter(
        source_path,
        target_dir,
        codegen_options,
        executable_name,
        codes,
        verification_profile,
        None,
    )
}

fn compile_source_with_artifacts_with_profile_and_reporter(
    source_path: &Path,
    target_dir: &Path,
    codegen_options: CodegenOptions,
    executable_name: &str,
    codes: CompileSourceCodes<'_>,
    verification_profile: verification_profile::VerificationProfile,
    reporter: Option<&mut cli_output::CliReporter>,
) -> Result<PathBuf, CompilerDiagnosticBundle> {
    codegen_options.validate()?;
    let mut reporter = reporter;
    let (source, ast) = run_compiler_stage(reporter.as_deref_mut(), "prepare source", || {
        let (source, ast) =
            parse_source_to_ast_with_artifacts(source_path, target_dir, &codes.frontend)?;
        let ast_path = target_dir.join("ast.json");
        let ast_json = serde_json::to_string_pretty(&ast).map_err(|err| {
            io_stage_error(codes.serialize_ast_io_code, "failed to serialize AST", err)
        })?;
        std::fs::write(&ast_path, ast_json).map_err(|err| {
            io_stage_error(
                codes.write_ast_io_code,
                format!("failed to write {}", ast_path.display()),
                err,
            )
        })?;
        debug!(ast_path = %ast_path.display(), "Parsed source file");
        Ok((source, ast))
    })?;

    compile_ast_to_executable_with_profile_and_reporter(
        target_dir,
        ast,
        codegen_options,
        executable_name,
        Some(source_path),
        Some(&source),
        verification_profile,
        reporter,
    )
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
    let codegen_options = build.codegen_options();
    let mut reporter = cli_output::CliReporter::stderr(build.quiet, build.use_color());
    reporter.header("oac build");
    reporter.metadata("source", source_path.display());
    reporter.metadata("backend", codegen_options.backend.as_str());
    reporter.metadata(
        "target",
        codegen_options.target.as_deref().unwrap_or("host"),
    );
    if let Some(qbe_arch) = codegen_options.qbe_arch.as_deref() {
        reporter.metadata("qbe-arch", qbe_arch);
    }

    let command_start = Instant::now();
    match compile_source_with_artifacts_with_profile_and_reporter(
        source_path,
        &target_dir,
        codegen_options,
        "app",
        CompileSourceCodes {
            frontend: FrontendPipelineCodes {
                read_source_io_code: "OAC-IO-006",
                tokenize_code: "OAC-TOKENIZE-001",
                serialize_tokens_io_code: "OAC-IO-007",
                write_tokens_io_code: "OAC-IO-008",
                parse_code: "OAC-PARSE-001",
                parse_message: "failed to parse source",
                import_code: "OAC-IMPORT-001",
                import_message: "failed to resolve imports",
                comptime_code: "OAC-COMPTIME-001",
                comptime_message: "failed to execute comptime applies",
            },
            serialize_ast_io_code: "OAC-IO-009",
            write_ast_io_code: "OAC-IO-010",
        },
        verification_profile::VerificationProfile::default(),
        Some(&mut reporter),
    ) {
        Ok(executable_path) => {
            reporter.finish_success(command_start.elapsed(), executable_path.display());
            Ok(())
        }
        Err(err) => {
            reporter.finish_failure(command_start.elapsed());
            Err(err)
        }
    }
}

fn run_compiler_stage<T>(
    reporter: Option<&mut cli_output::CliReporter>,
    stage: &str,
    action: impl FnOnce() -> Result<T, CompilerDiagnosticBundle>,
) -> Result<T, CompilerDiagnosticBundle> {
    let mut reporter = reporter;
    if let Some(reporter) = reporter.as_deref_mut() {
        reporter.stage_start(stage);
    }
    let stage_start = Instant::now();
    let result = action();
    let elapsed = stage_start.elapsed();
    if let Some(reporter) = reporter.as_deref_mut() {
        if result.is_ok() {
            reporter.stage_success(stage, elapsed);
        } else {
            reporter.stage_failure(stage, elapsed);
        }
    }
    result
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
    let codegen_options = test.codegen_options();
    let mut reporter = cli_output::CliReporter::stderr(test.quiet, test.use_color());
    reporter.header("oac test");
    reporter.metadata("source", source_path.display());
    reporter.metadata("backend", codegen_options.backend.as_str());
    reporter.metadata(
        "target",
        codegen_options.target.as_deref().unwrap_or("host"),
    );
    if let Some(qbe_arch) = codegen_options.qbe_arch.as_deref() {
        reporter.metadata("qbe-arch", qbe_arch);
    }

    let command_start = Instant::now();
    let result = (|| {
        let (source, ast) = run_compiler_stage(Some(&mut reporter), "prepare source", || {
            parse_source_to_ast_with_artifacts(
                source_path,
                &target_dir,
                &FrontendPipelineCodes {
                    read_source_io_code: "OAC-IO-012",
                    tokenize_code: "OAC-TOKENIZE-002",
                    serialize_tokens_io_code: "OAC-IO-013",
                    write_tokens_io_code: "OAC-IO-014",
                    parse_code: "OAC-PARSE-002",
                    parse_message: "failed to parse test source",
                    import_code: "OAC-IMPORT-002",
                    import_message: "failed to resolve test imports",
                    comptime_code: "OAC-COMPTIME-002",
                    comptime_message: "failed to execute test comptime applies",
                },
            )
        })?;

        let (lowered_ast, test_count) =
            run_compiler_stage(Some(&mut reporter), "collect tests", || {
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
                let ast_json = serde_json::to_string_pretty(&lowered_ast).map_err(|err| {
                    io_stage_error("OAC-IO-015", "failed to serialize lowered AST", err)
                })?;
                std::fs::write(&ast_path, ast_json).map_err(|err| {
                    io_stage_error(
                        "OAC-IO-016",
                        format!("failed to write {}", ast_path.display()),
                        err,
                    )
                })?;
                debug!(ast_path = %ast_path.display(), "Lowered test AST");
                Ok((lowered_ast, test_count))
            })?;

        let executable_path = compile_ast_to_executable_with_profile_and_reporter(
            &target_dir,
            lowered_ast,
            codegen_options,
            "app",
            Some(source_path),
            Some(&source),
            verification_profile::VerificationProfile::default(),
            Some(&mut reporter),
        )?;

        run_compiler_stage(Some(&mut reporter), "run tests", || {
            execute_test_binary(&executable_path, test_count)
        })?;
        Ok((executable_path, test_count))
    })();

    match result {
        Ok((executable_path, test_count)) => {
            reporter.finish_tests(
                command_start.elapsed(),
                test_count,
                executable_path.display(),
            );
            Ok(())
        }
        Err(err) => {
            reporter.finish_failure(command_start.elapsed());
            Err(err)
        }
    }
}

fn execute_test_binary(
    executable_path: &Path,
    test_count: usize,
) -> Result<(), CompilerDiagnosticBundle> {
    let output = std::process::Command::new(executable_path)
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
    Ok(())
}

#[allow(dead_code)]
pub(crate) fn compile_ast_to_executable(
    target_dir: &Path,
    ast: parser::Ast,
    codegen_options: CodegenOptions,
    executable_name: &str,
    source_path: Option<&Path>,
    source_text: Option<&str>,
) -> Result<PathBuf, CompilerDiagnosticBundle> {
    compile_ast_to_executable_with_profile_and_reporter(
        target_dir,
        ast,
        codegen_options,
        executable_name,
        source_path,
        source_text,
        verification_profile::VerificationProfile::default(),
        None,
    )
}

#[allow(dead_code)]
pub(crate) fn compile_ast_to_executable_with_profile(
    target_dir: &Path,
    ast: parser::Ast,
    codegen_options: CodegenOptions,
    executable_name: &str,
    source_path: Option<&Path>,
    source_text: Option<&str>,
    verification_profile: verification_profile::VerificationProfile,
) -> Result<PathBuf, CompilerDiagnosticBundle> {
    compile_ast_to_executable_with_profile_and_reporter(
        target_dir,
        ast,
        codegen_options,
        executable_name,
        source_path,
        source_text,
        verification_profile,
        None,
    )
}

fn compile_ast_to_executable_with_profile_and_reporter(
    target_dir: &Path,
    ast: parser::Ast,
    codegen_options: CodegenOptions,
    executable_name: &str,
    source_path: Option<&Path>,
    source_text: Option<&str>,
    verification_profile: verification_profile::VerificationProfile,
    reporter: Option<&mut cli_output::CliReporter>,
) -> Result<PathBuf, CompilerDiagnosticBundle> {
    codegen_options.validate()?;
    let mut reporter = reporter;
    let (ir, qbe_ir) = run_compiler_stage(reporter.as_deref_mut(), "check program", || {
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
        Ok((ir, qbe_ir))
    })?;

    run_compiler_stage(reporter.as_deref_mut(), "check proofs", || {
        prove::verify_prove_obligations_with_qbe_with_profile(
            &ir,
            &qbe_ir,
            target_dir,
            verification_profile,
        )
        .map_err(|err| {
            stage_error_from_anyhow(
                DiagnosticStage::Prove,
                "OAC-PROVE-001",
                "prove obligation verification failed",
                err,
                source_path,
                source_text,
            )
        })
    })?;

    run_compiler_stage(reporter.as_deref_mut(), "check data rules", || {
        struct_invariants::verify_struct_invariants_with_qbe_with_profile(
            &ir,
            &qbe_ir,
            target_dir,
            verification_profile,
        )
        .map_err(|err| {
            stage_error_from_anyhow(
                DiagnosticStage::StructInvariant,
                "OAC-INV-001",
                "struct invariant verification failed",
                err,
                source_path,
                source_text,
            )
        })
    })?;

    run_compiler_stage(reporter.as_deref_mut(), "check global rules", || {
        model_invariants::verify_model_invariants_with_qbe_with_profile(
            &ir,
            &qbe_ir,
            target_dir,
            verification_profile,
        )
        .map_err(|err| {
            stage_error_from_anyhow(
                DiagnosticStage::ModelInvariant,
                "OAC-MINV-001",
                "model invariant verification failed",
                err,
                source_path,
                source_text,
            )
        })
    })?;

    run_compiler_stage(reporter.as_deref_mut(), "check loops", || {
        reject_proven_non_terminating_main(&qbe_ir).map_err(|err| {
            stage_error_from_anyhow(
                DiagnosticStage::LoopClassifier,
                "OAC-LOOP-001",
                "loop non-termination classification failed",
                err,
                source_path,
                source_text,
            )
        })
    })?;

    let codegen_stage = match codegen_options.backend {
        RuntimeBackend::Qbe => "generate backend",
        RuntimeBackend::Llvm => "generate backend",
    };

    // Verification is always QBE-sourced; runtime backend selection only affects
    // post-verification artifact emission/link inputs.
    let runtime_artifacts = run_compiler_stage(reporter.as_deref_mut(), codegen_stage, || {
        codegen_runtime::emit_runtime_artifacts(&ir, &qbe_ir, target_dir, &codegen_options)
    })?;
    debug!(
        backend = codegen_options.backend.as_str(),
        ir_artifact = %runtime_artifacts.ir_artifact_path.display(),
        linker_input = %runtime_artifacts.linker_input_path.display(),
        "Runtime backend artifacts generated"
    );

    let executable_path = target_dir.join(executable_name);
    run_compiler_stage(reporter.as_deref_mut(), "link executable", || {
        link_runtime_artifacts(&runtime_artifacts, &codegen_options, &executable_path)
    })?;
    Ok(executable_path)
}

fn link_runtime_artifacts(
    runtime_artifacts: &codegen_runtime::RuntimeArtifacts,
    codegen_options: &CodegenOptions,
    executable_path: &Path,
) -> Result<(), CompilerDiagnosticBundle> {
    let linker_attempts = resolve_linker_attempts(
        codegen_options.qbe_arch.as_deref(),
        codegen_options.target.as_deref(),
    )
    .map_err(|err| {
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
            executable_path,
            &runtime_artifacts.linker_input_path,
        );

        let mut cc_cmd = std::process::Command::new(&attempt.program);
        cc_cmd
            .args(&attempt.args)
            .arg("-g")
            .arg("-o")
            .arg(executable_path)
            .arg(&runtime_artifacts.linker_input_path);

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
                backend = codegen_options.backend.as_str(),
                "Backend output compiled to executable"
            );
            return Ok(());
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
            "compilation of backend output to executable failed after trying {} linker command(s)",
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

fn resolve_linker_attempts(
    qbe_arch: Option<&str>,
    requested_target: Option<&str>,
) -> anyhow::Result<Vec<LinkerAttempt>> {
    let configured_command = env::var("OAC_CC")
        .ok()
        .map(|raw| ("OAC_CC", raw))
        .or_else(|| env::var("CC").ok().map(|raw| ("CC", raw)));
    let env_target_override = env::var("OAC_CC_TARGET").ok();
    let extra_flags = env::var("OAC_CC_FLAGS")
        .ok()
        .map(|raw| split_words(&raw))
        .unwrap_or_default();

    resolve_linker_attempts_for_config(
        qbe_arch,
        requested_target,
        configured_command
            .as_ref()
            .map(|(name, raw)| (*name, raw.as_str())),
        env_target_override.as_deref(),
        &extra_flags,
    )
}

fn resolve_linker_attempts_for_config(
    qbe_arch: Option<&str>,
    requested_target: Option<&str>,
    configured_command: Option<(&str, &str)>,
    env_target_override: Option<&str>,
    extra_flags: &[String],
) -> anyhow::Result<Vec<LinkerAttempt>> {
    let mut attempts = Vec::new();
    let mut include_defaults = true;
    let effective_target = env_target_override
        .map(std::borrow::ToOwned::to_owned)
        .or_else(|| requested_target.map(str::to_owned))
        .or_else(|| {
            qbe_arch
                .and_then(default_target_triple_for_qbe_arch)
                .map(str::to_owned)
        });

    if let Some((var_name, raw_command)) = configured_command {
        let mut words = split_words(raw_command);
        if words.is_empty() {
            return Err(anyhow::anyhow!("{var_name} must not be empty"));
        }

        let program = words.remove(0);
        let mut args = words;
        if let Some(target) = &effective_target {
            args.push(format!("--target={target}"));
        }
        args.extend(extra_flags.iter().cloned());
        attempts.push(LinkerAttempt { program, args });
        include_defaults = var_name != "OAC_CC";
    }

    if !include_defaults {
        return Ok(dedup_linker_attempts(attempts));
    }

    if let Some(target) = &effective_target {
        attempts.push(LinkerAttempt {
            program: "cc".to_string(),
            args: vec![format!("--target={target}")],
        });
        attempts.push(LinkerAttempt {
            program: "clang".to_string(),
            args: vec![format!("--target={target}")],
        });
    }

    if let Some(arch) = qbe_arch {
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
    linker_input: &Path,
) -> String {
    let mut parts = Vec::new();
    parts.push(program.to_string());
    parts.extend(args.iter().cloned());
    parts.push("-g".to_string());
    parts.push("-o".to_string());
    parts.push(executable.display().to_string());
    parts.push(linker_input.display().to_string());
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
    BenchProve(bench_prove::BenchProveOpts),
}

#[derive(clap::Parser)]
struct Build {
    source: String,
    #[clap(long, value_enum, default_value_t = RuntimeBackend::Qbe)]
    backend: RuntimeBackend,
    #[clap(long)]
    qbe_arch: Option<String>,
    #[clap(long)]
    target: Option<String>,
    #[clap(long)]
    quiet: bool,
    #[clap(long)]
    no_color: bool,
}

impl Build {
    fn codegen_options(&self) -> CodegenOptions {
        CodegenOptions {
            backend: self.backend,
            qbe_arch: self.qbe_arch.clone(),
            target: self.target.clone(),
        }
    }

    fn use_color(&self) -> bool {
        !self.no_color && std::io::stderr().is_terminal()
    }
}

#[derive(clap::Parser)]
struct Test {
    source: String,
    #[clap(long, value_enum, default_value_t = RuntimeBackend::Qbe)]
    backend: RuntimeBackend,
    #[clap(long)]
    qbe_arch: Option<String>,
    #[clap(long)]
    target: Option<String>,
    #[clap(long)]
    quiet: bool,
    #[clap(long)]
    no_color: bool,
}

impl Test {
    fn codegen_options(&self) -> CodegenOptions {
        CodegenOptions {
            backend: self.backend,
            qbe_arch: self.qbe_arch.clone(),
            target: self.target.clone(),
        }
    }

    fn use_color(&self) -> bool {
        !self.no_color && std::io::stderr().is_terminal()
    }
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
    use clap::Parser;
    use qbe::{Block, BlockItem, Cmp, Function, Instr, Linkage, Module, Statement, Type, Value};

    use super::{
        reject_proven_non_terminating_main, resolve_linker_attempts_for_config, LinkerAttempt, Oac,
        OacSubcommand, RuntimeBackend,
    };

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
    fn bench_prove_cli_defaults_are_stable() {
        let parsed = Oac::parse_from(["oac", "bench-prove"]);
        match parsed.subcmd {
            OacSubcommand::BenchProve(opts) => {
                assert_eq!(opts.suite, crate::bench_prove::BenchSuite::Full);
                assert_eq!(opts.iterations, 1);
                assert!(opts.baseline.is_none());
                assert!(opts.output.is_none());
                assert!(!opts.update_baseline);
                assert!(!opts.strict_outcome_gate);
            }
            _ => panic!("expected bench-prove subcommand"),
        }
    }

    #[test]
    fn bench_prove_cli_parses_explicit_flags() {
        let parsed = Oac::parse_from([
            "oac",
            "bench-prove",
            "--suite",
            "quick",
            "--iterations",
            "3",
            "--baseline",
            "custom-baseline.json",
            "--output",
            "custom-report.json",
            "--update-baseline",
            "--strict-outcome-gate",
        ]);
        match parsed.subcmd {
            OacSubcommand::BenchProve(opts) => {
                assert_eq!(opts.suite, crate::bench_prove::BenchSuite::Quick);
                assert_eq!(opts.iterations, 3);
                assert_eq!(
                    opts.baseline.as_deref(),
                    Some(std::path::Path::new("custom-baseline.json"))
                );
                assert_eq!(
                    opts.output.as_deref(),
                    Some(std::path::Path::new("custom-report.json"))
                );
                assert!(opts.update_baseline);
                assert!(opts.strict_outcome_gate);
            }
            _ => panic!("expected bench-prove subcommand"),
        }
    }

    #[test]
    fn linker_attempts_default_to_cc_for_host_builds() {
        let attempts = resolve_linker_attempts_for_config(None, None, None, None, &[])
            .expect("attempt resolution");
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
        let attempts = resolve_linker_attempts_for_config(Some("rv64"), None, None, None, &[])
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
            None,
            Some(("OAC_CC", "custom-cc --driver-mode=clang")),
            None,
            &extra_flags,
        )
        .expect("attempt resolution");

        assert_eq!(
            attempts,
            vec![LinkerAttempt {
                program: "custom-cc".to_string(),
                args: vec![
                    "--driver-mode=clang".to_string(),
                    "--target=riscv64-linux-gnu".to_string(),
                    "-static".to_string(),
                ],
            }]
        );
    }

    #[test]
    fn configured_linker_target_override_is_applied() {
        let attempts = resolve_linker_attempts_for_config(
            Some("rv64"),
            None,
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
            None,
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

    #[test]
    fn requested_target_is_applied_to_default_linker_attempts() {
        let attempts =
            resolve_linker_attempts_for_config(None, Some("aarch64-linux-gnu"), None, None, &[])
                .expect("attempt resolution");

        assert_eq!(
            attempts[0],
            LinkerAttempt {
                program: "cc".to_string(),
                args: vec!["--target=aarch64-linux-gnu".to_string()],
            }
        );
        assert!(attempts.contains(&LinkerAttempt {
            program: "clang".to_string(),
            args: vec!["--target=aarch64-linux-gnu".to_string()],
        }));
    }

    #[test]
    fn build_cli_defaults_to_qbe_backend() {
        let parsed = Oac::parse_from(["oac", "build", "main.oa"]);
        match parsed.subcmd {
            OacSubcommand::Build(build) => {
                assert_eq!(build.source, "main.oa");
                assert_eq!(build.backend, RuntimeBackend::Qbe);
                assert!(build.qbe_arch.is_none());
                assert!(build.target.is_none());
                assert!(!build.quiet);
                assert!(!build.no_color);
            }
            _ => panic!("expected build subcommand"),
        }
    }

    #[test]
    fn build_cli_parses_backend_and_target_flags() {
        let parsed = Oac::parse_from([
            "oac",
            "build",
            "main.oa",
            "--backend",
            "llvm",
            "--target",
            "aarch64-linux-gnu",
        ]);
        match parsed.subcmd {
            OacSubcommand::Build(build) => {
                assert_eq!(build.backend, RuntimeBackend::Llvm);
                assert_eq!(build.target.as_deref(), Some("aarch64-linux-gnu"));
                assert!(build.qbe_arch.is_none());
                assert!(!build.quiet);
                assert!(!build.no_color);
            }
            _ => panic!("expected build subcommand"),
        }
    }

    #[test]
    fn build_cli_parses_quiet_and_no_color_flags() {
        let parsed = Oac::parse_from(["oac", "build", "main.oa", "--quiet", "--no-color"]);
        match parsed.subcmd {
            OacSubcommand::Build(build) => {
                assert!(build.quiet);
                assert!(build.no_color);
            }
            _ => panic!("expected build subcommand"),
        }
    }

    #[test]
    fn build_cli_rejects_removed_positional_arch_argument() {
        let parsed = Oac::try_parse_from(["oac", "build", "main.oa", "amd64_sysv"]);
        assert!(
            parsed.is_err(),
            "positional arch argument should be rejected"
        );
    }

    #[test]
    fn test_cli_defaults_to_qbe_backend() {
        let parsed = Oac::parse_from(["oac", "test", "main.oa"]);
        match parsed.subcmd {
            OacSubcommand::Test(test) => {
                assert_eq!(test.source, "main.oa");
                assert_eq!(test.backend, RuntimeBackend::Qbe);
                assert!(test.qbe_arch.is_none());
                assert!(test.target.is_none());
                assert!(!test.quiet);
                assert!(!test.no_color);
            }
            _ => panic!("expected test subcommand"),
        }
    }

    #[test]
    fn test_cli_parses_backend_and_target_flags() {
        let parsed = Oac::parse_from([
            "oac",
            "test",
            "main.oa",
            "--backend",
            "llvm",
            "--target",
            "aarch64-linux-gnu",
        ]);
        match parsed.subcmd {
            OacSubcommand::Test(test) => {
                assert_eq!(test.backend, RuntimeBackend::Llvm);
                assert_eq!(test.target.as_deref(), Some("aarch64-linux-gnu"));
                assert!(test.qbe_arch.is_none());
                assert!(!test.quiet);
                assert!(!test.no_color);
            }
            _ => panic!("expected test subcommand"),
        }
    }

    #[test]
    fn test_cli_parses_quiet_and_no_color_flags() {
        let parsed = Oac::parse_from(["oac", "test", "main.oa", "--quiet", "--no-color"]);
        match parsed.subcmd {
            OacSubcommand::Test(test) => {
                assert!(test.quiet);
                assert!(test.no_color);
            }
            _ => panic!("expected test subcommand"),
        }
    }

    #[test]
    fn test_cli_rejects_removed_positional_arch_argument() {
        let parsed = Oac::try_parse_from(["oac", "test", "main.oa", "amd64_sysv"]);
        assert!(
            parsed.is_err(),
            "positional arch argument should be rejected"
        );
    }

    #[test]
    fn codegen_options_reject_qbe_arch_for_llvm_backend() {
        let opts = super::CodegenOptions {
            backend: RuntimeBackend::Llvm,
            qbe_arch: Some("rv64".to_string()),
            target: None,
        };
        let err = opts
            .validate()
            .expect_err("llvm backend should reject --qbe-arch");
        assert!(err
            .render_plain()
            .contains("--qbe-arch is only valid when --backend qbe"));
    }
}
