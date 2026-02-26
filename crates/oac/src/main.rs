mod builtins;
mod comptime;
mod flat_imports;
mod ir;
mod lsp;
mod parser;
mod prove;
mod qbe_backend;
mod riscv_smt; // Add the new module
mod struct_invariants;
mod test_framework;
mod tokenizer;

use std::collections::HashSet;
use std::env;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use clap::Parser;
use tracing::info;
use tracing::{debug, trace, warn};
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{fmt, EnvFilter, Layer};

fn main() -> anyhow::Result<()> {
    initialize_logging();

    let oac = Oac::parse();

    match oac.subcmd {
        OacSubcommand::Build(build) => {
            let current_dir = std::env::current_dir()?;
            compile(&current_dir, build)?;
        }
        OacSubcommand::Test(test) => {
            let current_dir = std::env::current_dir()?;
            run_tests(&current_dir, test)?;
        }
        OacSubcommand::Lsp(_) => {
            lsp::run()?;
        }
        OacSubcommand::RiscvSmt(riscv_smt_opts) => {
            let current_dir = std::env::current_dir()?;
            process_riscv_smt(&current_dir, riscv_smt_opts)?;
        }
    }

    Ok(())
}

fn process_riscv_smt(_current_dir: &Path, opts: RiscvSmtOpts) -> anyhow::Result<()> {
    let elf_path = Path::new(&opts.elf_file);
    if opts.check {
        let result = riscv_smt::check_returns_zero_within_cycles(elf_path)?;
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
        let smt_expression = riscv_smt::elf_to_smt_returns_zero_within_cycles(elf_path)?;
        if let Some(output_path) = opts.output {
            std::fs::write(&output_path, smt_expression)?;
            info!("SMT expression written to {}", output_path);
        } else {
            println!("{}", smt_expression);
        }
    }
    Ok(())
}

fn compile(current_dir: &Path, build: Build) -> anyhow::Result<()> {
    let target_dir = current_dir.join("target").join("oac");
    std::fs::create_dir_all(&target_dir)?;

    let source_path = Path::new(&build.source);
    let source = std::fs::read_to_string(source_path)?;
    trace!(source_len = source.len(), "Read input file");

    let tokens = tokenizer::tokenize(source)?;
    let tokens_path = target_dir.join("tokens.json");
    std::fs::write(&tokens_path, serde_json::to_string_pretty(&tokens)?)?;
    trace!(tokens_path = %tokens_path.display(), "Tokenized source file");

    let root_ast = parser::parse(tokens)?;
    let mut ast = flat_imports::resolve_ast(root_ast, source_path)?;
    comptime::execute_comptime_applies(&mut ast)?;
    let ast_path = target_dir.join("ast.json");
    std::fs::write(&ast_path, serde_json::to_string_pretty(&ast)?)?;
    debug!(ast_path = %ast_path.display(), "Parsed source file");

    compile_ast_to_executable(&target_dir, ast, build.arch.as_deref(), "app")?;

    Ok(())
}

fn run_tests(current_dir: &Path, test: Test) -> anyhow::Result<()> {
    let target_dir = current_dir.join("target").join("oac").join("test");
    std::fs::create_dir_all(&target_dir)?;

    let source_path = Path::new(&test.source);
    let source = std::fs::read_to_string(source_path)?;
    trace!(source_len = source.len(), "Read test source file");

    let tokens = tokenizer::tokenize(source)?;
    let tokens_path = target_dir.join("tokens.json");
    std::fs::write(&tokens_path, serde_json::to_string_pretty(&tokens)?)?;
    trace!(tokens_path = %tokens_path.display(), "Tokenized test source file");

    let root_ast = parser::parse(tokens)?;
    let mut ast = flat_imports::resolve_ast(root_ast, source_path)?;
    comptime::execute_comptime_applies(&mut ast)?;

    let lowered = test_framework::lower_tests_to_program(ast)?;
    let test_count = lowered.test_names.len();
    let lowered_ast = lowered.ast;
    let ast_path = target_dir.join("ast.json");
    std::fs::write(&ast_path, serde_json::to_string_pretty(&lowered_ast)?)?;
    debug!(ast_path = %ast_path.display(), "Lowered test AST");

    let executable_path = compile_ast_to_executable(&target_dir, lowered_ast, None, "app")?;

    let output = std::process::Command::new(&executable_path).output()?;
    print!("{}", String::from_utf8_lossy(&output.stdout));
    eprint!("{}", String::from_utf8_lossy(&output.stderr));
    if !output.status.success() {
        let exit_code = output
            .status
            .code()
            .map_or("signal".to_string(), |code| code.to_string());
        return Err(anyhow::anyhow!(
            "test run failed after launching {} test(s) (exit code: {})",
            test_count,
            exit_code
        ));
    }

    println!("test run passed: {} test(s)", test_count);
    Ok(())
}

fn compile_ast_to_executable(
    target_dir: &Path,
    ast: parser::Ast,
    arch: Option<&str>,
    executable_name: &str,
) -> anyhow::Result<PathBuf> {
    let ir = ir::resolve(ast)?;
    let ir_path = target_dir.join("ir.json");
    std::fs::write(&ir_path, serde_json::to_string_pretty(&ir)?)?;
    info!(ir_path = %ir_path.display(), "IR generated and type-checked");
    let qbe_ir = qbe_backend::compile(ir.clone());
    prove::verify_prove_obligations_with_qbe(&ir, &qbe_ir, target_dir)?;
    struct_invariants::verify_struct_invariants_with_qbe(&ir, &qbe_ir, target_dir)?;
    reject_proven_non_terminating_main(&qbe_ir)?;
    let qbe_ir_text = qbe_ir.to_string();

    let qbe_ir_path = target_dir.join("ir.qbe");
    std::fs::write(&qbe_ir_path, &qbe_ir_text)?;
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
        .output()?;

    if !qbe_output.status.success() {
        return Err(anyhow::anyhow!(
            "Compilation of QBE IR to assembly failed: {} (valid archs: amd64_sysv, amd64_apple, arm64, arm64_apple, rv64)",
            String::from_utf8_lossy(&qbe_output.stderr)
        ));
    }

    debug!(assembly_path = %assembly_path.display(), "QBE IR compiled to assembly");

    let executable_path = target_dir.join(executable_name);
    let linker_attempts = resolve_linker_attempts(arch)?;
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

    Err(anyhow::anyhow!(
        "Compilation of assembly to executable failed after trying {} linker command(s):\n{}",
        failures.len(),
        failures.join("\n")
    ))
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

    tracing_subscriber::registry()
        .with(
            fmt::layer()
                .with_writer(std::io::stderr)
                .with_filter(EnvFilter::from_str(&env_filter).unwrap()),
        )
        .init();
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
