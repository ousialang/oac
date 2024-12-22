mod builtins;
mod ir;
mod parser;
mod qbe_backend;
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

    let assembly_path = target_dir.join("assembly.s");
    std::process::Command::new("qbe")
        .arg("-o")
        .arg(&assembly_path)
        .arg(&qbe_ir_path)
        .output()?;

    let executable_path = target_dir.join("app");
    std::process::Command::new("cc")
        .arg(&assembly_path)
        .arg("-o")
        .arg(&executable_path)
        .output()?;

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
}

#[derive(clap::Parser)]
struct Build {
    source: String,
}
