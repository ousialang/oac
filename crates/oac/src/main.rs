mod builtins;
mod flat_imports;
mod ir;
mod parser;
mod qbe_backend;
mod riscv_smt; // Add the new module
mod tokenizer;

use std::env;
use std::path::Path;
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
    let ast = flat_imports::resolve_ast(root_ast, source_path)?;
    let ast_path = target_dir.join("ast.json");
    std::fs::write(&ast_path, serde_json::to_string_pretty(&ast)?)?;
    debug!(ast_path = %ast_path.display(), "Parsed source file");

    let ir = ir::resolve(ast.clone())?;
    let ir_path = target_dir.join("ir.json");
    std::fs::write(&ir_path, serde_json::to_string_pretty(&ir)?)?;
    info!(ir_path = %ir_path.display(), "IR generated and type-checked");

    let qbe_ir = qbe_backend::compile(ir);
    let qbe_ir_text = qbe_ir.to_string();
    let qbe_ir_path = target_dir.join("ir.qbe");
    std::fs::write(&qbe_ir_path, &qbe_ir_text)?;
    info!(qbe_ir_path = %qbe_ir_path.display(), "QBE IR generated");
    try_emit_qbe_smt_sidecar(&qbe_ir_text, &target_dir);

    let assembly_path = target_dir.join("assembly.s");
    let mut qbe_cmd = std::process::Command::new("qbe");

    if let Some(arch) = build.arch.as_ref() {
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

    let executable_path = target_dir.join("app");

    let mut cc_cmd = std::process::Command::new("zig");
    cc_cmd.arg("cc").arg("-g").arg("-o").arg(&executable_path);
    if let Some(arch) = build.arch.as_ref() {
        let cc_arch = match arch.as_str() {
            "rv64" => "riscv64-linux-gnu",
            _ => panic!("invalid arch"),
        };

        cc_cmd
            .arg("-target")
            .arg(cc_arch)
            .arg("-march=generic_rv64");
    }

    cc_cmd.arg(&assembly_path);

    let cc_output = cc_cmd.output()?;
    println!("{}", String::from_utf8_lossy(&cc_output.stderr));

    info!(executable_path = %executable_path.display(), "Assembly compiled to executable");

    Ok(())
}

fn try_emit_qbe_smt_sidecar(qbe_ir_text: &str, target_dir: &Path) {
    let smt_path = target_dir.join("ir.smt2");
    let options = qbe_smt::EncodeOptions {
        max_steps: 256,
        emit_model: false,
    };
    let qbe_slice = extract_qbe_function_for_smt(qbe_ir_text).unwrap_or_else(|| {
        warn!("No QBE function body found for SMT generation; continuing build");
        String::new()
    });
    if qbe_slice.is_empty() {
        return;
    }

    let smt = match qbe_smt::qbe_to_smt(&qbe_slice, &options) {
        Ok(smt) => smt,
        Err(err) => {
            warn!(error = %err, "Failed to generate QBE SMT sidecar; continuing build");
            return;
        }
    };

    if let Err(err) = std::fs::write(&smt_path, smt) {
        warn!(
            smt_path = %smt_path.display(),
            error = %err,
            "Failed to write QBE SMT sidecar; continuing build"
        );
        return;
    }

    info!(smt_path = %smt_path.display(), "QBE SMT sidecar generated");
}

fn extract_qbe_function_for_smt(qbe_ir_text: &str) -> Option<String> {
    // Prefer $main so the sidecar aligns with the executable entrypoint.
    extract_named_qbe_function(qbe_ir_text, "main")
        .or_else(|| extract_first_qbe_function(qbe_ir_text))
}

fn extract_named_qbe_function(qbe_ir_text: &str, function_name: &str) -> Option<String> {
    extract_qbe_function(qbe_ir_text, |line| {
        line.contains("function") && line.contains(&format!("${function_name}("))
    })
}

fn extract_first_qbe_function(qbe_ir_text: &str) -> Option<String> {
    extract_qbe_function(qbe_ir_text, |line| {
        line.contains("function") && line.contains('$')
    })
}

fn extract_qbe_function<F>(qbe_ir_text: &str, predicate: F) -> Option<String>
where
    F: Fn(&str) -> bool,
{
    let lines: Vec<&str> = qbe_ir_text.lines().collect();
    let start = lines.iter().position(|line| predicate(line.trim()))?;

    let mut depth: i32 = 0;
    let mut started_body = false;
    let mut out = String::new();

    for line in lines.iter().skip(start) {
        out.push_str(line);
        out.push('\n');

        for ch in line.chars() {
            if ch == '{' {
                depth += 1;
                started_body = true;
            } else if ch == '}' {
                depth -= 1;
            }
        }

        if started_body && depth == 0 {
            break;
        }
    }

    if started_body {
        Some(out)
    } else {
        None
    }
}

fn initialize_logging() {
    let env_filter = env::var("RUST_LOG").unwrap_or_default();

    tracing_subscriber::registry()
        .with(fmt::layer().with_filter(EnvFilter::from_str(&env_filter).unwrap()))
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
    RiscvSmt(RiscvSmtOpts),
}

#[derive(clap::Parser)]
struct Build {
    source: String,
    arch: Option<String>,
}

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
