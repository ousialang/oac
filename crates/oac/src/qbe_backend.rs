use qbe::*;

use crate::parser::Ast;

pub fn compile(ast: Ast) -> qbe::Module<'static> {
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
