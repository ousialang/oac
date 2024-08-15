mod parser;
mod qbe_backend;
mod resolver;
mod tokenizer;

use clap::Parser;

fn main() -> anyhow::Result<()> {
    let oac = Oac::parse();

    match oac.subcmd {
        OacSubcommand::Build(build) => {
            let source = std::fs::read_to_string(build.source).unwrap();
            let tokens = tokenizer::tokenize(source)?;
            let ast = parser::parse(tokens).unwrap();
            dbg!("{:?}", &ast);
            let resolved_program = resolver::resolve(ast.clone()).unwrap();
            dbg!("{:?}", resolved_program);
            let qbe_ir = qbe_backend::compile(ast);
            std::fs::write(build.target, qbe_ir.to_string()).unwrap();
        }
    }

    Ok(())
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
    target: String,
}
