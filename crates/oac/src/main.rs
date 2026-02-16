mod builtins;
mod flat_imports;
mod ir;
mod lsp;
mod parser;
mod qbe_backend;
mod riscv_smt; // Add the new module
mod struct_invariants;
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
    let ast = flat_imports::resolve_ast(root_ast, source_path)?;
    let ast_path = target_dir.join("ast.json");
    std::fs::write(&ast_path, serde_json::to_string_pretty(&ast)?)?;
    debug!(ast_path = %ast_path.display(), "Parsed source file");

    let ir = ir::resolve(ast.clone())?;
    let ir_path = target_dir.join("ir.json");
    std::fs::write(&ir_path, serde_json::to_string_pretty(&ir)?)?;
    info!(ir_path = %ir_path.display(), "IR generated and type-checked");
    struct_invariants::verify_struct_invariants(&ir, &target_dir)?;

    let qbe_ir = qbe_backend::compile(ir);
    reject_proven_non_terminating_main(&qbe_ir)?;
    let qbe_ir_text = qbe_ir.to_string();

    let qbe_ir_path = target_dir.join("ir.qbe");
    std::fs::write(&qbe_ir_path, &qbe_ir_text)?;
    info!(qbe_ir_path = %qbe_ir_path.display(), "QBE IR generated");

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
    Lsp(LspOpts),
    RiscvSmt(RiscvSmtOpts),
}

#[derive(clap::Parser)]
struct Build {
    source: String,
    arch: Option<String>,
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
    use super::reject_proven_non_terminating_main;
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
}
