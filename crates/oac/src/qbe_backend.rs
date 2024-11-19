use qbe::*;

use crate::{ir::ResolvedProgram, parser::Ast};

pub fn compile(ir: ResolvedProgram) -> qbe::Module<'static> {
    let mut module = qbe::Module::default();

    module.add_data(qbe::DataDef::new(
        Linkage::private(),
        "fmt".to_string(),
        None,
        vec![
            (qbe::Type::Byte, DataItem::Str("%s\\n\\n".to_string())),
            (qbe::Type::Byte, DataItem::Const(0)),
        ],
    ));

    module.add_data(qbe::DataDef::new(
        Linkage::private(),
        "string_contents".to_string(),
        None,
        vec![
            (qbe::Type::Byte, DataItem::Str("foobar".to_string())),
            (qbe::Type::Byte, DataItem::Const(0)),
        ],
    ));

    let mut func = qbe::Function::new(
        qbe::Linkage::public(),
        "main".to_string(),
        vec![],
        Some(qbe::Type::Word),
    );
    func.add_block("start".to_string());
    func.add_instr(qbe::Instr::Call(
        "printf".into(),
        vec![
            (qbe::Type::Long, qbe::Value::Global("fmt".into())),
            (
                qbe::Type::Long,
                qbe::Value::Global("string_contents".into()),
            ),
        ],
    ));
    func.add_instr(qbe::Instr::Ret(Some(qbe::Value::Const(0))));

    module.add_function(func);
    module
}

#[cfg(test)]
mod tests {
    use std::fs;

    use crate::{ir, parser, qbe_backend, tokenizer};
    use std::io::Write;

    #[test]
    fn execution_tests() {
        let test_files = fs::read_dir("execution_tests").unwrap();

        for path in test_files {
            let tmp = tempfile::tempdir().unwrap();

            let path = path.unwrap().path();

            let source = std::fs::read_to_string(&path).unwrap();
            let tokens = tokenizer::tokenize(source).unwrap();
            let ast = parser::parse(tokens).unwrap();
            let ir = ir::resolve(ast).unwrap();
            let qbe_ir = qbe_backend::compile(ir);

            let qbe_ir_filepath = tmp.path().join("test.qbe");

            let mut file = std::fs::File::create(&qbe_ir_filepath).unwrap();
            file.write_all(qbe_ir.to_string().as_bytes()).unwrap();

            let assembly_filepath = tmp.path().join("test.s");
            // run qbe -o $path $path.s && cc $path.s
            std::process::Command::new("qbe")
                .arg("-o")
                .arg(&assembly_filepath)
                .arg(&qbe_ir_filepath)
                .output()
                .unwrap();
            std::process::Command::new("cc")
                .arg(&assembly_filepath)
                .output()
                .unwrap();

            // run the executable and store the output in a string
            let output = std::process::Command::new("./a.out").output().unwrap();
            let output = String::from_utf8(output.stdout).unwrap();

            insta::assert_snapshot!(path.display().to_string(), output);
        }
    }
}
