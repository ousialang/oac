mod builtins;
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
use tracing::{debug, trace};
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

    let source = std::fs::read_to_string(build.source)?;
    trace!(source_len = source.len(), "Read input file");

    let tokens = tokenizer::tokenize(source)?;
    let tokens_path = target_dir.join("tokens.json");
    std::fs::write(&tokens_path, serde_json::to_string_pretty(&tokens)?)?;
    trace!(tokens_path = %tokens_path.display(), "Tokenized source file");

    let ast = parser::parse(tokens)?;
    let ast_path = target_dir.join("ast.json");
    std::fs::write(&ast_path, serde_json::to_string_pretty(&ast)?)?;
    debug!(ast_path = %ast_path.display(), "Parsed source file");

    let ir = ir::resolve(ast.clone())?;
    let ir_path = target_dir.join("ir.json");
    std::fs::write(&ir_path, serde_json::to_string_pretty(&ir)?)?;
    info!(ir_path = %ir_path.display(), "IR generated and type-checked");

    let qbe_ir = qbe_backend::compile(ir);
    let qbe_ir_path = target_dir.join("ir.qbe");
    std::fs::write(&qbe_ir_path, qbe_ir.to_string())?;
    info!(qbe_ir_path = %qbe_ir_path.display(), "QBE IR generated");

    let assembly_path = target_dir.join("assembly.s");
    let qbe_output = std::process::Command::new("qbe")
        .arg("-t")
        .arg("arm64_apple")
        .arg("-o")
        .arg(&assembly_path)
        .arg(&qbe_ir_path)
        .output()?;

    if !qbe_output.status.success() {
        return Err(anyhow::anyhow!(
            "Compilation of QBE IR to assembly failed: {}",
            String::from_utf8_lossy(&qbe_output.stderr)
        ));
    }

    debug!(assembly_path = %assembly_path.display(), "QBE IR compiled to assembly");

    let executable_path = target_dir.join("app");
    let cc_output = std::process::Command::new("cc")
        .arg(&assembly_path)
        .arg("-o")
        .arg(&executable_path)
        .output()?;
    println!("{}", String::from_utf8_lossy(&cc_output.stderr));

    info!(executable_path = %executable_path.display(), "Assembly compiled to executable");

    Ok(())
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
