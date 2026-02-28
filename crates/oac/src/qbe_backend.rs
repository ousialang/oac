use std::{collections::HashMap, sync::Arc, vec};

use qbe::*;
use tracing::trace;

use crate::{
    builtins::BuiltInType,
    ir::{self, ResolvedProgram},
    parser::{self, Op, StructDef, UnaryOp},
    symbol_keys::{trait_impl_method_key, trait_method_key},
};

type QbeAssignName = String;
type Variables = HashMap<String, (QbeAssignName, ir::TypeRef)>;
pub(crate) const PROVE_MARKER_PREFIX: &str = ".oac_prove_site_";
const ASSERT_FAILURE_EXIT_CODE: u64 = 242;
const TAGGED_UNION_PAYLOAD_OFFSET_BYTES: u64 = 8;
const TAGGED_UNION_SIZE_BYTES: u64 = 16;

struct CodegenCtx {
    module: qbe::Module,
    resolved: Arc<ResolvedProgram>,
    qbe_types_by_name: HashMap<String, qbe::Type>,
}

fn add_builtins(ctx: &mut CodegenCtx) {
    {
        let mut sum = qbe::Function::new(
            qbe::Linkage::public(),
            "sum".to_string(),
            vec![
                (qbe::Type::Word, qbe::Value::Temporary("a".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("b".to_string())),
            ],
            Some(qbe::Type::Word),
        );

        sum.add_block("start".to_string());

        sum.assign_instr(
            Value::Temporary("c".to_string()),
            Type::Word,
            Instr::Add(
                Value::Temporary("a".to_string()),
                Value::Temporary("b".to_string()),
            ),
        );
        sum.add_instr(Instr::Ret(Some(Value::Temporary("c".to_string()))));

        ctx.module.add_function(sum);
    }

    {
        let mut sub = Function::new(
            qbe::Linkage::public(),
            "sub".to_string(),
            vec![
                (qbe::Type::Word, qbe::Value::Temporary("a".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("b".to_string())),
            ],
            Some(qbe::Type::Word),
        );

        sub.add_block("start".to_string());

        sub.assign_instr(
            Value::Temporary("c".to_string()),
            Type::Word,
            Instr::Sub(
                Value::Temporary("a".to_string()),
                Value::Temporary("b".to_string()),
            ),
        );
        sub.add_instr(Instr::Ret(Some(Value::Temporary("c".to_string()))));
        ctx.module.add_function(sub);
    }

    {
        let mut eq = Function::new(
            qbe::Linkage::public(),
            "eq".to_string(),
            vec![
                (qbe::Type::Word, qbe::Value::Temporary("a".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("b".to_string())),
            ],
            Some(qbe::Type::Word),
        );

        eq.add_block("start".to_string());

        eq.assign_instr(
            Value::Temporary("c".to_string()),
            Type::Word,
            Instr::Cmp(
                Type::Word,
                qbe::Cmp::Eq,
                Value::Temporary("a".to_string()),
                Value::Temporary("b".to_string()),
            ),
        );
        eq.add_instr(Instr::Ret(Some(Value::Temporary("c".to_string()))));
        ctx.module.add_function(eq);
    }

    {
        let mut lt = Function::new(
            qbe::Linkage::public(),
            "lt".to_string(),
            vec![
                (qbe::Type::Word, qbe::Value::Temporary("a".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("b".to_string())),
            ],
            Some(qbe::Type::Word),
        );

        lt.add_block("start".to_string());

        lt.assign_instr(
            Value::Temporary("c".to_string()),
            Type::Word,
            Instr::Cmp(
                Type::Word,
                qbe::Cmp::Slt,
                Value::Temporary("a".to_string()),
                Value::Temporary("b".to_string()),
            ),
        );
        lt.add_instr(Instr::Ret(Some(Value::Temporary("c".to_string()))));
        ctx.module.add_function(lt);
    }

    {
        ctx.module.add_data(qbe::DataDef::new(
            Linkage::private(),
            "integer_fmt".to_string(),
            None,
            vec![
                (qbe::Type::Byte, DataItem::Str("%u\n".to_string())),
                (qbe::Type::Byte, DataItem::Const(0)),
            ],
        ));
    }

    {
        let mut print = Function::new(
            qbe::Linkage::public(),
            "print".to_string(),
            vec![(Type::Word, Value::Temporary("a".to_string()))],
            Some(Type::Word),
        );

        print.add_block("start".to_string());
        print.add_instr(Instr::Call(
            "printf".to_string(),
            vec![
                (qbe::Type::Long, qbe::Value::Global("integer_fmt".into())),
                (qbe::Type::Word, qbe::Value::Temporary("a".to_string())),
            ],
            Some(1),
        ));
        print.add_instr(Instr::Ret(Some(Value::Const(0))));

        ctx.module.add_function(print);
    }

    {
        let mut f = Function::new(
            Linkage::private(),
            "i32_to_i64".to_string(),
            vec![(qbe::Type::Word, qbe::Value::Temporary("a".to_string()))],
            Some(Type::Long),
        );
        f.add_block("start".to_string());
        let long = new_id(&["long"]);
        f.assign_instr(
            Value::Temporary(long.to_string()),
            qbe::Type::Long,
            Instr::Extsw(Value::Temporary("a".to_string())),
        );
        f.add_instr(Instr::Ret(Some(Value::Temporary(long))));
        ctx.module.add_function(f);
    }

    {
        let mut f = Function::new(
            Linkage::public(),
            "load_u8".to_string(),
            vec![(qbe::Type::Long, qbe::Value::Temporary("addr".to_string()))],
            Some(Type::Word),
        );
        f.add_block("start".to_string());
        let value = new_id(&["load", "u8"]);
        f.assign_instr(
            Value::Temporary(value.clone()),
            qbe::Type::Word,
            Instr::Load(Type::UnsignedByte, Value::Temporary("addr".to_string())),
        );
        f.add_instr(Instr::Ret(Some(Value::Temporary(value))));
        ctx.module.add_function(f);
    }

    {
        let mut f = Function::new(
            Linkage::public(),
            "load_i32".to_string(),
            vec![(qbe::Type::Long, qbe::Value::Temporary("addr".to_string()))],
            Some(Type::Word),
        );
        f.add_block("start".to_string());
        let value = new_id(&["load", "i32"]);
        f.assign_instr(
            Value::Temporary(value.clone()),
            qbe::Type::Word,
            Instr::Load(Type::Word, Value::Temporary("addr".to_string())),
        );
        f.add_instr(Instr::Ret(Some(Value::Temporary(value))));
        ctx.module.add_function(f);
    }

    {
        let mut f = Function::new(
            Linkage::public(),
            "load_i64".to_string(),
            vec![(qbe::Type::Long, qbe::Value::Temporary("addr".to_string()))],
            Some(Type::Long),
        );
        f.add_block("start".to_string());
        let value = new_id(&["load", "i64"]);
        f.assign_instr(
            Value::Temporary(value.clone()),
            qbe::Type::Long,
            Instr::Load(Type::Long, Value::Temporary("addr".to_string())),
        );
        f.add_instr(Instr::Ret(Some(Value::Temporary(value))));
        ctx.module.add_function(f);
    }

    {
        let mut f = Function::new(
            Linkage::public(),
            "load_bool".to_string(),
            vec![(qbe::Type::Long, qbe::Value::Temporary("addr".to_string()))],
            Some(Type::Word),
        );
        f.add_block("start".to_string());
        let raw = new_id(&["load", "bool", "raw"]);
        f.assign_instr(
            Value::Temporary(raw.clone()),
            qbe::Type::Word,
            Instr::Load(Type::Word, Value::Temporary("addr".to_string())),
        );
        let value = new_id(&["load", "bool", "value"]);
        f.assign_instr(
            Value::Temporary(value.clone()),
            qbe::Type::Word,
            Instr::Cmp(
                Type::Word,
                qbe::Cmp::Ne,
                Value::Temporary(raw),
                Value::Const(0),
            ),
        );
        f.add_instr(Instr::Ret(Some(Value::Temporary(value))));
        ctx.module.add_function(f);
    }

    {
        let mut f = Function::new(
            Linkage::public(),
            "store_u8".to_string(),
            vec![
                (qbe::Type::Long, qbe::Value::Temporary("addr".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("value".to_string())),
            ],
            None,
        );
        f.add_block("start".to_string());
        f.add_instr(Instr::Store(
            Type::Byte,
            Value::Temporary("addr".to_string()),
            Value::Temporary("value".to_string()),
        ));
        f.add_instr(Instr::Ret(None));
        ctx.module.add_function(f);
    }

    {
        let mut f = Function::new(
            Linkage::public(),
            "store_i32".to_string(),
            vec![
                (qbe::Type::Long, qbe::Value::Temporary("addr".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("value".to_string())),
            ],
            None,
        );
        f.add_block("start".to_string());
        f.add_instr(Instr::Store(
            Type::Word,
            Value::Temporary("addr".to_string()),
            Value::Temporary("value".to_string()),
        ));
        f.add_instr(Instr::Ret(None));
        ctx.module.add_function(f);
    }

    {
        let mut f = Function::new(
            Linkage::public(),
            "store_i64".to_string(),
            vec![
                (qbe::Type::Long, qbe::Value::Temporary("addr".to_string())),
                (qbe::Type::Long, qbe::Value::Temporary("value".to_string())),
            ],
            None,
        );
        f.add_block("start".to_string());
        f.add_instr(Instr::Store(
            Type::Long,
            Value::Temporary("addr".to_string()),
            Value::Temporary("value".to_string()),
        ));
        f.add_instr(Instr::Ret(None));
        ctx.module.add_function(f);
    }

    {
        let mut f = Function::new(
            Linkage::public(),
            "store_bool".to_string(),
            vec![
                (qbe::Type::Long, qbe::Value::Temporary("addr".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("value".to_string())),
            ],
            None,
        );
        f.add_block("start".to_string());
        f.add_instr(Instr::Store(
            Type::Word,
            Value::Temporary("addr".to_string()),
            Value::Temporary("value".to_string()),
        ));
        f.add_instr(Instr::Ret(None));
        ctx.module.add_function(f);
    }

    {
        let mut payload_fn = Function::new(
            Linkage::private(),
            "__string_payload".to_string(),
            vec![(qbe::Type::Long, qbe::Value::Temporary("s".to_string()))],
            Some(Type::Long),
        );
        payload_fn.add_block("start".to_string());
        let payload_addr = new_id(&["string", "payload", "addr"]);
        payload_fn.assign_instr(
            Value::Temporary(payload_addr.clone()),
            qbe::Type::Long,
            Instr::Add(
                Value::Temporary("s".to_string()),
                Value::Const(TAGGED_UNION_PAYLOAD_OFFSET_BYTES),
            ),
        );
        let payload = new_id(&["string", "payload"]);
        payload_fn.assign_instr(
            Value::Temporary(payload.clone()),
            qbe::Type::Long,
            Instr::Load(qbe::Type::Long, Value::Temporary(payload_addr)),
        );
        payload_fn.add_instr(Instr::Ret(Some(Value::Temporary(payload))));
        ctx.module.add_function(payload_fn);
    }

    {
        let bytes_struct = std_bytes_struct(ctx);
        let bytes_ptr_offset = calculate_struct_field_offset(ctx, &bytes_struct, "ptr");

        let mut ptr_fn = Function::new(
            Linkage::private(),
            "__string_data_ptr".to_string(),
            vec![(qbe::Type::Long, qbe::Value::Temporary("s".to_string()))],
            Some(Type::Long),
        );
        ptr_fn.add_block("start".to_string());
        let bytes_ptr = new_id(&["string", "bytes", "ptr"]);
        ptr_fn.assign_instr(
            Value::Temporary(bytes_ptr.clone()),
            qbe::Type::Long,
            Instr::Call(
                "__string_payload".to_string(),
                vec![(qbe::Type::Long, Value::Temporary("s".to_string()))],
                None,
            ),
        );
        let data_ptr = new_id(&["string", "data", "ptr"]);
        ptr_fn.assign_instr(
            Value::Temporary(data_ptr.clone()),
            qbe::Type::Long,
            Instr::Add(Value::Temporary(bytes_ptr), Value::Const(bytes_ptr_offset)),
        );
        let data_ptr_value = new_id(&["string", "data", "ptr", "value"]);
        ptr_fn.assign_instr(
            Value::Temporary(data_ptr_value.clone()),
            qbe::Type::Long,
            Instr::Load(qbe::Type::Long, Value::Temporary(data_ptr)),
        );
        ptr_fn.add_instr(Instr::Ret(Some(Value::Temporary(data_ptr_value))));
        ctx.module.add_function(ptr_fn);
    }

    {
        let bytes_struct = std_bytes_struct(ctx);
        let bytes_len_offset = calculate_struct_field_offset(ctx, &bytes_struct, "len");

        let mut len_fn = Function::new(
            Linkage::private(),
            "__string_data_len".to_string(),
            vec![(qbe::Type::Long, qbe::Value::Temporary("s".to_string()))],
            Some(Type::Word),
        );
        len_fn.add_block("start".to_string());
        let bytes_ptr = new_id(&["bytes", "ptr"]);
        len_fn.assign_instr(
            Value::Temporary(bytes_ptr.clone()),
            qbe::Type::Long,
            Instr::Call(
                "__string_payload".to_string(),
                vec![(qbe::Type::Long, Value::Temporary("s".to_string()))],
                None,
            ),
        );
        let len_addr = new_id(&["bytes", "len", "addr"]);
        len_fn.assign_instr(
            Value::Temporary(len_addr.clone()),
            qbe::Type::Long,
            Instr::Add(Value::Temporary(bytes_ptr), Value::Const(bytes_len_offset)),
        );
        let len = new_id(&["string", "len"]);
        len_fn.assign_instr(
            Value::Temporary(len.clone()),
            qbe::Type::Word,
            Instr::Load(qbe::Type::Word, Value::Temporary(len_addr)),
        );
        len_fn.add_instr(Instr::Ret(Some(Value::Temporary(len))));
        ctx.module.add_function(len_fn);
    }

    {
        let mut char_at = Function::new(
            Linkage::public(),
            "char_at".to_string(),
            vec![
                (qbe::Type::Long, qbe::Value::Temporary("s".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("index".to_string())),
            ],
            Some(Type::Word),
        );
        char_at.add_block("start".to_string());

        let base_ptr = new_id(&["string", "base"]);
        char_at.assign_instr(
            Value::Temporary(base_ptr.clone()),
            qbe::Type::Long,
            Instr::Call(
                "__string_data_ptr".to_string(),
                vec![(qbe::Type::Long, qbe::Value::Temporary("s".to_string()))],
                None,
            ),
        );

        let index_i64 = new_id(&["index", "i64"]);
        char_at.assign_instr(
            Value::Temporary(index_i64.clone()),
            qbe::Type::Long,
            Instr::Call(
                "i32_to_i64".to_string(),
                vec![(qbe::Type::Word, qbe::Value::Temporary("index".to_string()))],
                None,
            ),
        );

        let address = new_id(&["char", "address"]);
        char_at.assign_instr(
            Value::Temporary(address.clone()),
            qbe::Type::Long,
            Instr::Add(Value::Temporary(base_ptr), Value::Temporary(index_i64)),
        );

        let ch = new_id(&["char"]);
        char_at.assign_instr(
            Value::Temporary(ch.clone()),
            qbe::Type::Word,
            Instr::Load(Type::UnsignedByte, Value::Temporary(address)),
        );
        char_at.add_instr(Instr::Ret(Some(Value::Temporary(ch))));

        ctx.module.add_function(char_at);
    }

    {
        let mut string_len = Function::new(
            Linkage::public(),
            "string_len".to_string(),
            vec![(qbe::Type::Long, qbe::Value::Temporary("s".to_string()))],
            Some(Type::Word),
        );
        string_len.add_block("start".to_string());
        let len = new_id(&["string", "len"]);
        string_len.assign_instr(
            Value::Temporary(len.clone()),
            qbe::Type::Word,
            Instr::Call(
                "__string_data_len".to_string(),
                vec![(qbe::Type::Long, qbe::Value::Temporary("s".to_string()))],
                None,
            ),
        );
        string_len.add_instr(Instr::Ret(Some(Value::Temporary(len))));
        ctx.module.add_function(string_len);
    }

    {
        let bytes_struct = std_bytes_struct(ctx);
        let bytes_len_offset = calculate_struct_field_offset(ctx, &bytes_struct, "len");
        let bytes_size = struct_size_bytes(ctx, &bytes_struct);
        let string_enum = std_string_enum(ctx);
        let string_heap_tag = enum_variant_tag(&string_enum, "Heap");

        let mut slice = Function::new(
            Linkage::public(),
            "slice".to_string(),
            vec![
                (qbe::Type::Long, qbe::Value::Temporary("s".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("start".to_string())),
                (qbe::Type::Word, qbe::Value::Temporary("len".to_string())),
            ],
            Some(Type::Long),
        );
        slice.add_block("start".to_string());

        let src_base = new_id(&["slice", "src", "base"]);
        slice.assign_instr(
            Value::Temporary(src_base.clone()),
            qbe::Type::Long,
            Instr::Call(
                "__string_data_ptr".to_string(),
                vec![(qbe::Type::Long, qbe::Value::Temporary("s".to_string()))],
                None,
            ),
        );

        let len_plus_one = new_id(&["len", "plus", "one"]);
        slice.assign_instr(
            Value::Temporary(len_plus_one.clone()),
            qbe::Type::Word,
            Instr::Add(Value::Temporary("len".to_string()), Value::Const(1)),
        );
        let alloc_size_i64 = new_id(&["alloc", "size", "i64"]);
        slice.assign_instr(
            Value::Temporary(alloc_size_i64.clone()),
            qbe::Type::Long,
            Instr::Call(
                "i32_to_i64".to_string(),
                vec![(qbe::Type::Word, qbe::Value::Temporary(len_plus_one))],
                None,
            ),
        );

        let dst = new_id(&["slice", "dst"]);
        slice.assign_instr(
            Value::Temporary(dst.clone()),
            qbe::Type::Long,
            Instr::Call(
                "malloc".to_string(),
                vec![(qbe::Type::Long, qbe::Value::Temporary(alloc_size_i64))],
                None,
            ),
        );

        let start_i64 = new_id(&["start", "i64"]);
        slice.assign_instr(
            Value::Temporary(start_i64.clone()),
            qbe::Type::Long,
            Instr::Call(
                "i32_to_i64".to_string(),
                vec![(qbe::Type::Word, qbe::Value::Temporary("start".to_string()))],
                None,
            ),
        );
        let src = new_id(&["slice", "src"]);
        slice.assign_instr(
            Value::Temporary(src.clone()),
            qbe::Type::Long,
            Instr::Add(Value::Temporary(src_base), Value::Temporary(start_i64)),
        );

        let copy_n_i64 = new_id(&["copy", "n", "i64"]);
        slice.assign_instr(
            Value::Temporary(copy_n_i64.clone()),
            qbe::Type::Long,
            Instr::Call(
                "i32_to_i64".to_string(),
                vec![(qbe::Type::Word, qbe::Value::Temporary("len".to_string()))],
                None,
            ),
        );
        slice.add_instr(Instr::Call(
            "memcpy".to_string(),
            vec![
                (qbe::Type::Long, qbe::Value::Temporary(dst.clone())),
                (qbe::Type::Long, qbe::Value::Temporary(src)),
                (qbe::Type::Long, qbe::Value::Temporary(copy_n_i64.clone())),
            ],
            None,
        ));

        let nul_addr = new_id(&["nul", "addr"]);
        slice.assign_instr(
            Value::Temporary(nul_addr.clone()),
            qbe::Type::Long,
            Instr::Add(Value::Temporary(dst.clone()), Value::Temporary(copy_n_i64)),
        );
        slice.add_instr(Instr::Store(
            Type::Byte,
            Value::Temporary(nul_addr),
            Value::Const(0),
        ));

        let bytes_ptr = new_id(&["slice", "bytes", "alloc"]);
        slice.assign_instr(
            Value::Temporary(bytes_ptr.clone()),
            qbe::Type::Long,
            Instr::Call(
                "malloc".to_string(),
                vec![(qbe::Type::Long, Value::Const(bytes_size))],
                None,
            ),
        );
        slice.add_instr(Instr::Store(
            qbe::Type::Long,
            Value::Temporary(bytes_ptr.clone()),
            Value::Temporary(dst),
        ));
        let bytes_len_addr = new_id(&["slice", "bytes", "len", "addr"]);
        slice.assign_instr(
            Value::Temporary(bytes_len_addr.clone()),
            qbe::Type::Long,
            Instr::Add(
                Value::Temporary(bytes_ptr.clone()),
                Value::Const(bytes_len_offset),
            ),
        );
        slice.add_instr(Instr::Store(
            qbe::Type::Word,
            Value::Temporary(bytes_len_addr),
            Value::Temporary("len".to_string()),
        ));

        let string_ptr = new_id(&["slice", "string", "alloc"]);
        slice.assign_instr(
            Value::Temporary(string_ptr.clone()),
            qbe::Type::Long,
            Instr::Call(
                "malloc".to_string(),
                vec![(qbe::Type::Long, Value::Const(TAGGED_UNION_SIZE_BYTES))],
                None,
            ),
        );
        slice.add_instr(Instr::Store(
            qbe::Type::Word,
            Value::Temporary(string_ptr.clone()),
            Value::Const(string_heap_tag as u64),
        ));
        let payload_addr = new_id(&["slice", "string", "payload", "addr"]);
        slice.assign_instr(
            Value::Temporary(payload_addr.clone()),
            qbe::Type::Long,
            Instr::Add(
                Value::Temporary(string_ptr.clone()),
                Value::Const(TAGGED_UNION_PAYLOAD_OFFSET_BYTES),
            ),
        );
        slice.add_instr(Instr::Store(
            qbe::Type::Long,
            Value::Temporary(payload_addr),
            Value::Temporary(bytes_ptr),
        ));
        slice.add_instr(Instr::Ret(Some(Value::Temporary(string_ptr))));
        ctx.module.add_function(slice);
    }

    {
        let mut print_str = Function::new(
            qbe::Linkage::public(),
            "print_str".to_string(),
            vec![(Type::Long, Value::Temporary("s".to_string()))],
            Some(Type::Word),
        );
        print_str.add_block("start".to_string());
        let ptr = new_id(&["print_str", "ptr"]);
        print_str.assign_instr(
            Value::Temporary(ptr.clone()),
            qbe::Type::Long,
            Instr::Call(
                "__string_data_ptr".to_string(),
                vec![(qbe::Type::Long, qbe::Value::Temporary("s".to_string()))],
                None,
            ),
        );
        let len = new_id(&["print_str", "len"]);
        print_str.assign_instr(
            Value::Temporary(len.clone()),
            qbe::Type::Word,
            Instr::Call(
                "__string_data_len".to_string(),
                vec![(qbe::Type::Long, qbe::Value::Temporary("s".to_string()))],
                None,
            ),
        );
        let len_i64 = new_id(&["print_str", "len", "i64"]);
        print_str.assign_instr(
            Value::Temporary(len_i64.clone()),
            qbe::Type::Long,
            Instr::Call(
                "i32_to_i64".to_string(),
                vec![(qbe::Type::Word, qbe::Value::Temporary(len))],
                None,
            ),
        );
        print_str.add_instr(Instr::Call(
            "write".to_string(),
            vec![
                (qbe::Type::Word, Value::Const(1)),
                (qbe::Type::Long, Value::Temporary(ptr)),
                (qbe::Type::Long, Value::Temporary(len_i64)),
            ],
            None,
        ));
        print_str.add_instr(Instr::Ret(Some(Value::Const(0))));
        ctx.module.add_function(print_str);
    }

    ctx.qbe_types_by_name
        .insert("Int".to_string(), qbe::Type::Word);
    ctx.qbe_types_by_name
        .insert("PtrInt".to_string(), qbe::Type::Long);
    ctx.qbe_types_by_name
        .insert("Bool".to_string(), qbe::Type::Word);
    ctx.qbe_types_by_name
        .insert("U8".to_string(), qbe::Type::Word);
    ctx.qbe_types_by_name
        .insert("I32".to_string(), qbe::Type::Word);
    ctx.qbe_types_by_name
        .insert("I64".to_string(), qbe::Type::Long);
    ctx.qbe_types_by_name
        .insert("FP32".to_string(), qbe::Type::Single);
    ctx.qbe_types_by_name
        .insert("FP64".to_string(), qbe::Type::Double);
}

fn type_to_qbe(ty: &ir::TypeDef) -> qbe::Type {
    match ty {
        ir::TypeDef::BuiltIn(BuiltInType::Bool) => qbe::Type::Word,
        ir::TypeDef::BuiltIn(BuiltInType::U8) => qbe::Type::Word,
        ir::TypeDef::BuiltIn(BuiltInType::I32) => qbe::Type::Word,
        ir::TypeDef::BuiltIn(BuiltInType::FP32) => qbe::Type::Single,
        ir::TypeDef::BuiltIn(BuiltInType::FP64) => qbe::Type::Double,
        ir::TypeDef::BuiltIn(BuiltInType::Void) => {
            panic!("Void cannot be lowered to a QBE value type")
        }
        ir::TypeDef::BuiltIn(BuiltInType::Semantic) => {
            panic!("semantic-only builtin types cannot be lowered to QBE")
        }
        ir::TypeDef::BuiltIn(BuiltInType::I64) | ir::TypeDef::Struct(_) => qbe::Type::Long, // pointer to struct
        ir::TypeDef::Enum(enum_def) => {
            if enum_def.is_tagged_union {
                qbe::Type::Long
            } else {
                qbe::Type::Word
            }
        }
    }
}

fn compile_type(ctx: &mut CodegenCtx, type_def: &ir::TypeDef) {
    trace!("Compiling type {:?}", type_def);

    match type_def {
        ir::TypeDef::BuiltIn(_) => {} // We generated those already
        ir::TypeDef::Enum(enum_def) => {
            ctx.qbe_types_by_name.insert(
                enum_def.name.clone(),
                if enum_def.is_tagged_union {
                    qbe::Type::Long
                } else {
                    qbe::Type::Word
                },
            );
        }
        ir::TypeDef::Struct(StructDef {
            struct_fields,
            name,
        }) => {
            let mut items = vec![];
            for field in struct_fields.iter() {
                let field_type = ctx.resolved.type_definitions.get(&field.ty).unwrap();
                let qbe_type = type_to_qbe(field_type);
                items.push((qbe_type, 1));
            }
            let typedef = qbe::TypeDef {
                name: name.to_string(),
                align: None,
                items,
            };

            let type_def = ctx.module.add_type(typedef.clone());
            ctx.qbe_types_by_name.insert(
                name.to_string(),
                qbe::Type::Aggregate(Arc::new(type_def.clone())),
            );
        }
    }
}

fn type_ref_to_qbe(ctx: &CodegenCtx, type_name: &str) -> qbe::Type {
    let ty = ctx
        .resolved
        .type_definitions
        .get(type_name)
        .unwrap_or_else(|| panic!("Unknown type {}", type_name));
    type_to_qbe(ty)
}

fn compile_match_subject(
    ctx: &mut CodegenCtx,
    qbe_func: &mut qbe::Function,
    subject: &parser::Expression,
    variables: &mut Variables,
    label_root: &str,
) -> (QbeAssignName, ir::TypeRef, ir::EnumTypeDef, QbeAssignName) {
    let (subject_var, subject_ty) = compile_expr(ctx, qbe_func, subject, variables);
    let enum_def = match ctx.resolved.type_definitions.get(&subject_ty) {
        Some(ir::TypeDef::Enum(enum_def)) => enum_def.clone(),
        _ => panic!("match subject must be enum"),
    };

    let tag_var = if enum_def.is_tagged_union {
        let id = new_id(&[label_root, "tag"]);
        qbe_func.assign_instr(
            qbe::Value::Temporary(id.clone()),
            qbe::Type::Word,
            qbe::Instr::Load(qbe::Type::Word, qbe::Value::Temporary(subject_var.clone())),
        );
        id
    } else {
        subject_var.clone()
    };

    (subject_var, subject_ty, enum_def, tag_var)
}

fn resolve_match_pattern<'a>(
    enum_def: &'a ir::EnumTypeDef,
    subject_ty: &str,
    pattern: &parser::MatchPattern,
) -> (&'a ir::EnumVariant, Option<String>) {
    match pattern {
        parser::MatchPattern::Variant {
            type_name,
            variant_name,
            binder,
        } => {
            assert_eq!(type_name, subject_ty);
            let variant = enum_def
                .variants
                .iter()
                .find(|v| v.name == *variant_name)
                .unwrap();
            (variant, binder.clone())
        }
    }
}

fn bind_match_payload(
    ctx: &mut CodegenCtx,
    qbe_func: &mut qbe::Function,
    arm_variables: &mut Variables,
    subject_var: &str,
    variant: &ir::EnumVariant,
    binder: Option<String>,
    label_root: &str,
) {
    if let (Some(binder), Some(payload_ty)) = (binder, variant.payload_ty.clone()) {
        let payload_addr = new_id(&[label_root, "payload", "addr"]);
        qbe_func.assign_instr(
            qbe::Value::Temporary(payload_addr.clone()),
            qbe::Type::Long,
            qbe::Instr::Add(
                qbe::Value::Temporary(subject_var.to_string()),
                qbe::Value::Const(8),
            ),
        );
        let payload_var = new_id(&[label_root, "payload"]);
        let payload_qbe_ty = type_ref_to_qbe(ctx, &payload_ty);
        qbe_func.assign_instr(
            qbe::Value::Temporary(payload_var.clone()),
            payload_qbe_ty.clone(),
            qbe::Instr::Load(payload_qbe_ty, qbe::Value::Temporary(payload_addr)),
        );
        arm_variables.insert(binder, (payload_var, payload_ty));
    }
}

enum MatchArmOutcome {
    FallsThrough,
    Terminated,
}

fn lower_match_dispatch<Arm, PatternOf, CompileArm>(
    ctx: &mut CodegenCtx,
    qbe_func: &mut qbe::Function,
    variables: &Variables,
    subject_var: &str,
    subject_ty: &str,
    enum_def: &ir::EnumTypeDef,
    tag_var: &str,
    arms: &[Arm],
    pattern_of: PatternOf,
    label_root: &str,
    force_end_block: bool,
    mut compile_arm: CompileArm,
) -> String
where
    PatternOf: Fn(&Arm) -> &parser::MatchPattern,
    CompileArm: FnMut(&mut CodegenCtx, &mut qbe::Function, &mut Variables, &Arm) -> MatchArmOutcome,
{
    let end_label = new_id(&[label_root, "end"]);
    let mut any_arm_falls_through = false;

    for (i, arm) in arms.iter().enumerate() {
        let arm_label = new_id(&[label_root, "arm"]);
        let next_label = if i + 1 < arms.len() {
            Some(new_id(&[label_root, "next"]))
        } else {
            None
        };

        let (variant, binder) = resolve_match_pattern(enum_def, subject_ty, pattern_of(arm));

        let cmp_var = new_id(&[label_root, "cmp"]);
        qbe_func.assign_instr(
            qbe::Value::Temporary(cmp_var.clone()),
            qbe::Type::Word,
            qbe::Instr::Cmp(
                qbe::Type::Word,
                qbe::Cmp::Eq,
                qbe::Value::Temporary(tag_var.to_string()),
                qbe::Value::Const(variant.tag as u64),
            ),
        );
        qbe_func.add_instr(qbe::Instr::Jnz(
            qbe::Value::Temporary(cmp_var),
            arm_label.clone(),
            next_label.clone().unwrap_or_else(|| arm_label.clone()),
        ));

        qbe_func.add_block(arm_label);
        let mut arm_variables = variables.clone();
        bind_match_payload(
            ctx,
            qbe_func,
            &mut arm_variables,
            subject_var,
            variant,
            binder,
            label_root,
        );

        let outcome = compile_arm(ctx, qbe_func, &mut arm_variables, arm);
        if matches!(outcome, MatchArmOutcome::FallsThrough) {
            any_arm_falls_through = true;
            qbe_func.add_instr(qbe::Instr::Jmp(end_label.clone()));
        }

        if let Some(next_label) = next_label {
            qbe_func.add_block(next_label);
        }
    }

    if force_end_block || any_arm_falls_through {
        qbe_func.add_block(end_label.clone());
    }
    end_label
}

fn compile_statement(
    ctx: &mut CodegenCtx,
    qbe_func: &mut qbe::Function,
    statement: &parser::Statement,
    variables: &mut Variables,
    prove_site_counter: &mut usize,
) {
    match statement {
        parser::Statement::StructDef { def } => {
            let struct_type = ctx.resolved.type_definitions.get(&def.name).unwrap();
            if let ir::TypeDef::Struct(_s) = struct_type {
                compile_type(ctx, &struct_type.clone());
            }
        }
        parser::Statement::Match { subject, arms } => {
            let (subject_var, subject_ty, enum_def, tag_var) =
                compile_match_subject(ctx, qbe_func, subject, variables, "match");
            lower_match_dispatch(
                ctx,
                qbe_func,
                variables,
                &subject_var,
                &subject_ty,
                &enum_def,
                &tag_var,
                arms,
                |arm| &arm.pattern,
                "match",
                false,
                |ctx, qbe_func, arm_variables, arm| {
                    for statement in &arm.body {
                        compile_statement(
                            ctx,
                            qbe_func,
                            statement,
                            arm_variables,
                            prove_site_counter,
                        );
                    }
                    if qbe_func.blocks.last().unwrap().jumps() {
                        MatchArmOutcome::Terminated
                    } else {
                        MatchArmOutcome::FallsThrough
                    }
                },
            );
        }
        parser::Statement::Conditional {
            condition,
            body,
            else_body,
        } => compile_conditional_statement(
            ctx,
            qbe_func,
            condition,
            body,
            else_body.as_deref(),
            variables,
            prove_site_counter,
        ),
        parser::Statement::While { condition, body } => {
            compile_while_statement(
                ctx,
                qbe_func,
                condition,
                body,
                variables,
                prove_site_counter,
            );
        }
        parser::Statement::Return { expr } => {
            let (expr_var, expr_ty) = compile_expr(ctx, qbe_func, &expr, variables);
            let return_var = maybe_clone_struct_value(ctx, qbe_func, &expr_var, &expr_ty);
            trace!(%expr_var, "Emitting return instruction");
            qbe_func.add_instr(qbe::Instr::Ret(Some(qbe::Value::Temporary(return_var))));
        }
        parser::Statement::Expression { expr } => {
            if compile_void_call_statement(ctx, qbe_func, expr, variables) {
                return;
            }
            compile_expr(ctx, qbe_func, &expr, variables);
        }
        parser::Statement::Prove { condition } => {
            compile_prove_statement(ctx, qbe_func, condition, variables, prove_site_counter);
        }
        parser::Statement::Assert { condition } => {
            compile_assert_statement(ctx, qbe_func, condition, variables);
        }
        parser::Statement::Assign { variable, value } => {
            compile_assign_statement(ctx, qbe_func, variable, value, variables);
        }
    }
}

fn compile_conditional_statement(
    ctx: &mut CodegenCtx,
    qbe_func: &mut qbe::Function,
    condition: &parser::Expression,
    body: &[parser::Statement],
    else_body: Option<&[parser::Statement]>,
    variables: &mut Variables,
    prove_site_counter: &mut usize,
) {
    let then_label = new_id(&["cond", "then"]);
    let else_label = new_id(&["cond", "else"]);
    let end_block_label = new_id(&["cond", "end"]);

    let condition_var = compile_expr(ctx, qbe_func, condition, variables).0;

    qbe_func.add_instr(qbe::Instr::Jnz(
        qbe::Value::Temporary(condition_var),
        then_label.clone(),
        if else_body.is_some() {
            else_label.clone()
        } else {
            end_block_label.clone()
        },
    ));

    qbe_func.add_block(&then_label);
    for statement in body {
        compile_statement(ctx, qbe_func, statement, variables, prove_site_counter);
    }
    let then_falls_through = !qbe_func.blocks.last().unwrap().jumps();
    if then_falls_through {
        qbe_func.add_instr(qbe::Instr::Jmp(end_block_label.clone()));
    }

    let mut else_falls_through = false;
    if let Some(else_body) = else_body {
        qbe_func.add_block(&else_label);
        for statement in else_body {
            compile_statement(ctx, qbe_func, statement, variables, prove_site_counter);
        }
        else_falls_through = !qbe_func.blocks.last().unwrap().jumps();
        if else_falls_through {
            qbe_func.add_instr(qbe::Instr::Jmp(end_block_label.clone()));
        }
    }

    let needs_end_block = else_body.is_none() || then_falls_through || else_falls_through;
    if needs_end_block {
        qbe_func.add_block(&end_block_label);
    }
}

fn compile_while_statement(
    ctx: &mut CodegenCtx,
    qbe_func: &mut qbe::Function,
    condition: &parser::Expression,
    body: &[parser::Statement],
    variables: &mut Variables,
    prove_site_counter: &mut usize,
) {
    let condition_label = new_id(&["while", "cond"]);
    let start_label = new_id(&["while", "start"]);
    let end_block_label = new_id(&["while", "end"]);

    qbe_func.add_block(condition_label.clone());
    let condition_var = compile_expr(ctx, qbe_func, condition, variables).0;

    qbe_func.add_instr(qbe::Instr::Jnz(
        qbe::Value::Temporary(condition_var),
        start_label.clone(),
        end_block_label.clone(),
    ));

    qbe_func.add_block(&start_label);
    for statement in body {
        compile_statement(ctx, qbe_func, statement, variables, prove_site_counter);
    }
    qbe_func.add_instr(qbe::Instr::Jmp(condition_label));

    qbe_func.add_block(&end_block_label);
}

fn compile_prove_statement(
    ctx: &mut CodegenCtx,
    qbe_func: &mut qbe::Function,
    condition: &parser::Expression,
    variables: &mut Variables,
    prove_site_counter: &mut usize,
) {
    let condition_var = compile_expr(ctx, qbe_func, condition, variables).0;
    let marker_temp = format!("{PROVE_MARKER_PREFIX}{}", *prove_site_counter);
    *prove_site_counter += 1;
    qbe_func.assign_instr(
        qbe::Value::Temporary(marker_temp),
        qbe::Type::Word,
        qbe::Instr::Copy(qbe::Value::Temporary(condition_var)),
    );
}

fn compile_assert_statement(
    ctx: &mut CodegenCtx,
    qbe_func: &mut qbe::Function,
    condition: &parser::Expression,
    variables: &mut Variables,
) {
    let condition_var = compile_expr(ctx, qbe_func, condition, variables).0;
    let assert_pass_label = new_id(&["assert", "pass"]);
    let assert_fail_label = new_id(&["assert", "fail"]);

    qbe_func.add_instr(qbe::Instr::Jnz(
        qbe::Value::Temporary(condition_var),
        assert_pass_label.clone(),
        assert_fail_label.clone(),
    ));

    qbe_func.add_block(assert_fail_label);
    qbe_func.add_instr(qbe::Instr::Call(
        "exit".to_string(),
        vec![(qbe::Type::Word, qbe::Value::Const(ASSERT_FAILURE_EXIT_CODE))],
        None,
    ));
    qbe_func.add_instr(qbe::Instr::Hlt);

    qbe_func.add_block(assert_pass_label);
}

fn compile_assign_statement(
    ctx: &mut CodegenCtx,
    qbe_func: &mut qbe::Function,
    variable: &str,
    value: &parser::Expression,
    variables: &mut Variables,
) {
    trace!(%variable, "Compiling assignment");

    let value_var = compile_expr(ctx, qbe_func, value, variables);
    if let Some(existing_var) = variables.get(variable) {
        let assigned_var = maybe_clone_struct_value(ctx, qbe_func, &value_var.0, &existing_var.1);
        let existing_type = ctx
            .resolved
            .type_definitions
            .get(&existing_var.1)
            .expect("existing variable type should exist");
        qbe_func.assign_instr(
            qbe::Value::Temporary(existing_var.0.clone()),
            type_to_qbe(existing_type),
            qbe::Instr::Copy(qbe::Value::Temporary(assigned_var)),
        );
    } else {
        let assigned_var = maybe_clone_struct_value(ctx, qbe_func, &value_var.0, &value_var.1);
        variables.insert(variable.to_string(), (assigned_var, value_var.1));
    }
}

fn compile_function(ctx: &mut CodegenCtx, func_def: ir::FunctionDefinition) {
    let qbe_args = func_def
        .sig
        .parameters
        .iter()
        .map(|param| {
            let type_def = ctx
                .resolved
                .type_definitions
                .get(&param.ty)
                .unwrap_or_else(|| panic!("unknown parameter type {}", param.ty));
            let ty = type_to_qbe(type_def);
            (ty, qbe::Value::Temporary(param.name.clone()))
        })
        .collect::<Vec<_>>();

    let return_type_def = ctx
        .resolved
        .type_definitions
        .get(&func_def.sig.return_type)
        .unwrap();

    let mut qbe_func = qbe::Function::new(
        qbe::Linkage::public(),
        func_def.name.clone(),
        qbe_args,
        Some(type_to_qbe(return_type_def)),
    );

    qbe_func.add_block("start".to_string());

    let mut variables = HashMap::new();
    let mut prove_site_counter = 0usize;
    for param in &func_def.sig.parameters {
        variables.insert(param.name.clone(), (param.name.clone(), param.ty.clone()));
    }

    for statement in &func_def.body {
        compile_statement(
            ctx,
            &mut qbe_func,
            statement,
            &mut variables,
            &mut prove_site_counter,
        );
    }

    ctx.module.add_function(qbe_func);
}

pub fn compile(ir: ResolvedProgram) -> qbe::Module {
    let mut ctx = CodegenCtx {
        module: qbe::Module::default(),
        resolved: Arc::new(ir),
        qbe_types_by_name: HashMap::new(),
    };

    add_builtins(&mut ctx);

    for type_def in ctx.resolved.clone().type_definitions.values() {
        compile_type(&mut ctx, type_def);
    }

    for func_def in ctx.resolved.clone().function_definitions.values() {
        compile_function(&mut ctx, func_def.clone());
    }

    ctx.module
}

fn new_id(labels: &[&str]) -> String {
    format!(
        ".L_{}_{}",
        labels.join("_"),
        uuid::Uuid::now_v7().as_simple()
    )
}

fn type_offset(ctx: &CodegenCtx, ty: &str) -> u64 {
    match ctx.resolved.type_definitions.get(ty) {
        Some(ty) => match ty {
            ir::TypeDef::BuiltIn(BuiltInType::Bool) => 4,
            ir::TypeDef::BuiltIn(BuiltInType::U8) => 4,
            ir::TypeDef::BuiltIn(BuiltInType::I32) => 4,
            ir::TypeDef::BuiltIn(BuiltInType::FP32) => 4,
            ir::TypeDef::BuiltIn(BuiltInType::Void) => {
                panic!("Void cannot be used in value-layout positions")
            }
            ir::TypeDef::BuiltIn(BuiltInType::Semantic) => {
                panic!("semantic-only builtin types cannot be used in value-layout positions")
            }
            ir::TypeDef::Enum(enum_def) => {
                if enum_def.is_tagged_union {
                    8
                } else {
                    4
                }
            }
            ir::TypeDef::BuiltIn(BuiltInType::I64)
            | ir::TypeDef::BuiltIn(BuiltInType::FP64)
            | ir::TypeDef::Struct(_) => 8,
        },
        None => panic!("Unknown type {}", ty),
    }
}

fn calculate_struct_field_offset(
    ctx: &mut CodegenCtx,
    struct_def: &StructDef,
    field_name: &str,
) -> u64 {
    let mut offset = 0;
    for field in struct_def.struct_fields.iter() {
        if field.name == *field_name {
            return offset;
        }
        offset += type_offset(ctx, &field.ty);
    }

    panic!(
        "Field {} not found in struct {}",
        field_name, struct_def.name
    );
}

fn struct_size_bytes(ctx: &CodegenCtx, struct_def: &StructDef) -> u64 {
    struct_def
        .struct_fields
        .iter()
        .map(|field| type_offset(ctx, &field.ty))
        .sum()
}

fn struct_size_bytes_by_name(ctx: &CodegenCtx, struct_name: &str) -> u64 {
    let type_def = ctx
        .resolved
        .type_definitions
        .get(struct_name)
        .unwrap_or_else(|| panic!("Unknown struct type {}", struct_name));
    let ir::TypeDef::Struct(struct_def) = type_def else {
        panic!("Type {} is not a struct", struct_name);
    };
    struct_size_bytes(ctx, struct_def)
}

fn non_zero_allocation_size(size: u64) -> u64 {
    if size == 0 {
        1
    } else {
        size
    }
}

fn alloc_struct_zeroed(func: &mut qbe::Function, size: u64) -> QbeAssignName {
    let id = new_id(&["struct", "alloc"]);
    func.assign_instr(
        Value::Temporary(id.clone()),
        qbe::Type::Long,
        Instr::Call(
            "calloc".to_string(),
            vec![
                (qbe::Type::Long, qbe::Value::Const(1)),
                (
                    qbe::Type::Long,
                    qbe::Value::Const(non_zero_allocation_size(size)),
                ),
            ],
            None,
        ),
    );
    id
}

fn clone_struct_bytes(
    ctx: &CodegenCtx,
    func: &mut qbe::Function,
    source_ptr: &str,
    struct_name: &str,
) -> QbeAssignName {
    let size = struct_size_bytes_by_name(ctx, struct_name);
    let cloned_ptr = alloc_struct_zeroed(func, size);
    func.add_instr(Instr::Call(
        "memcpy".to_string(),
        vec![
            (qbe::Type::Long, qbe::Value::Temporary(cloned_ptr.clone())),
            (
                qbe::Type::Long,
                qbe::Value::Temporary(source_ptr.to_string()),
            ),
            (qbe::Type::Long, qbe::Value::Const(size)),
        ],
        None,
    ));
    cloned_ptr
}

fn maybe_clone_struct_value(
    ctx: &CodegenCtx,
    func: &mut qbe::Function,
    value_var: &str,
    value_ty: &str,
) -> QbeAssignName {
    match ctx.resolved.type_definitions.get(value_ty) {
        Some(ir::TypeDef::Struct(_)) => clone_struct_bytes(ctx, func, value_var, value_ty),
        _ => value_var.to_string(),
    }
}

fn emit_struct_memcmp(
    ctx: &CodegenCtx,
    func: &mut qbe::Function,
    left_ptr: &str,
    right_ptr: &str,
    struct_name: &str,
) -> QbeAssignName {
    let size = struct_size_bytes_by_name(ctx, struct_name);
    let id = new_id(&["struct", "memcmp"]);
    func.assign_instr(
        qbe::Value::Temporary(id.clone()),
        qbe::Type::Word,
        qbe::Instr::Call(
            "memcmp".to_string(),
            vec![
                (qbe::Type::Long, qbe::Value::Temporary(left_ptr.to_string())),
                (
                    qbe::Type::Long,
                    qbe::Value::Temporary(right_ptr.to_string()),
                ),
                (qbe::Type::Long, qbe::Value::Const(size)),
            ],
            None,
        ),
    );
    id
}

fn std_bytes_struct(ctx: &CodegenCtx) -> StructDef {
    match ctx.resolved.type_definitions.get("Bytes") {
        Some(ir::TypeDef::Struct(def)) => def.clone(),
        _ => panic!("std Bytes struct is required for String lowering"),
    }
}

fn std_string_enum(ctx: &CodegenCtx) -> ir::EnumTypeDef {
    match ctx.resolved.type_definitions.get("String") {
        Some(ir::TypeDef::Enum(def)) if def.is_tagged_union => def.clone(),
        Some(ir::TypeDef::Enum(_)) => panic!("std String must be a tagged-union enum"),
        _ => panic!("std String enum is required for String lowering"),
    }
}

fn enum_variant_tag(enum_def: &ir::EnumTypeDef, variant_name: &str) -> u32 {
    enum_def
        .variants
        .iter()
        .find(|variant| variant.name == variant_name)
        .unwrap_or_else(|| panic!("missing variant {variant_name} on enum {}", enum_def.name))
        .tag
}

fn resolve_void_call_target<'a>(
    ctx: &CodegenCtx,
    expr: &'a parser::Expression,
) -> Option<(String, &'a [parser::Expression])> {
    match expr {
        parser::Expression::Call(function_name, args) => {
            let sig = ctx.resolved.function_sigs.get(function_name)?;
            if sig.return_type == "Void" {
                Some((function_name.clone(), args.as_slice()))
            } else {
                None
            }
        }
        parser::Expression::PostfixCall { callee, args } => {
            let parser::Expression::FieldAccess {
                struct_variable,
                field,
            } = callee.as_ref()
            else {
                return None;
            };
            let namespaced_call = parser::qualify_namespace_function_name(struct_variable, field);
            let sig = ctx.resolved.function_sigs.get(&namespaced_call)?;
            if sig.return_type == "Void" {
                Some((namespaced_call, args.as_slice()))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn compile_void_call_statement(
    ctx: &mut CodegenCtx,
    func: &mut qbe::Function,
    expr: &parser::Expression,
    variables: &mut Variables,
) -> bool {
    let Some((function_name, args)) = resolve_void_call_target(ctx, expr) else {
        return false;
    };

    let mut lowered_args = vec![];
    for arg in args {
        let (arg_var, arg_ty) = compile_expr(ctx, func, arg, variables);
        let lowered_var = maybe_clone_struct_value(ctx, func, &arg_var, &arg_ty);
        let arg_type_def = ctx
            .resolved
            .type_definitions
            .get(&arg_ty)
            .expect("call argument type should exist");
        lowered_args.push((
            type_to_qbe(arg_type_def),
            qbe::Value::Temporary(lowered_var),
        ));
    }

    let sig = ctx
        .resolved
        .function_sigs
        .get(&function_name)
        .expect("void call target signature should exist");
    func.add_instr(qbe::Instr::Call(
        call_target_symbol(&function_name, sig),
        lowered_args,
        None,
    ));
    true
}

fn call_target_symbol(function_name: &str, sig: &ir::FunctionSignature) -> String {
    sig.extern_symbol_name
        .clone()
        .unwrap_or_else(|| function_name.to_string())
}

fn compile_named_call(
    ctx: &mut CodegenCtx,
    func: &mut qbe::Function,
    function_name: &str,
    args: &[parser::Expression],
    variables: &mut Variables,
) -> (QbeAssignName, ir::TypeRef) {
    let id = new_id(&["call", function_name]);
    let mut arg_vars = vec![];
    for arg in args {
        let (arg_var, arg_ty) = compile_expr(ctx, func, arg, variables);
        let lowered_var = maybe_clone_struct_value(ctx, func, &arg_var, &arg_ty);
        arg_vars.push((lowered_var, arg_ty));
    }

    let sig = ctx
        .resolved
        .function_sigs
        .get(function_name)
        .unwrap()
        .clone();

    let instr = qbe::Instr::Call(
        call_target_symbol(function_name, &sig),
        arg_vars
            .iter()
            .map(|v| {
                let type_def = ctx.resolved.type_definitions.get(&v.1).unwrap();
                let qbe_type = type_to_qbe(type_def);
                (qbe_type, qbe::Value::Temporary(v.0.clone()))
            })
            .collect::<Vec<_>>(),
        None,
    );

    assert!(
        sig.return_type != "Void",
        "void-return call {} cannot be used as an expression value",
        function_name
    );
    let return_type_def = ctx
        .resolved
        .type_definitions
        .get(&sig.return_type)
        .unwrap()
        .clone();
    let tmp_id_type = type_to_qbe(&return_type_def);

    func.assign_instr(Value::Temporary(id.clone()), tmp_id_type, instr);

    (id, sig.return_type.clone())
}

fn compile_expr(
    ctx: &mut CodegenCtx,
    func: &mut qbe::Function,
    expr: &parser::Expression,
    variables: &mut Variables,
) -> (QbeAssignName, ir::TypeRef) {
    trace!(?expr, "Compiling expression");

    match expr {
        parser::Expression::Match { subject, arms } => {
            let var_types = variables
                .iter()
                .map(|(name, (_, ty))| (name.clone(), ty.clone()))
                .collect::<HashMap<_, _>>();
            let match_ty = ir::get_expression_type(
                expr,
                &var_types,
                &ctx.resolved.function_sigs,
                &ctx.resolved.type_definitions,
                &ctx.resolved.trait_method_signatures,
                &ctx.resolved.trait_impl_methods,
            )
            .unwrap_or_else(|err| {
                panic!("failed to type-check match expression in codegen: {err}")
            });
            let match_qbe_ty = type_to_qbe(
                ctx.resolved
                    .type_definitions
                    .get(&match_ty)
                    .expect("match expression type should exist"),
            );

            let result_slot = new_id(&["match", "expr", "slot"]);
            func.assign_instr(
                qbe::Value::Temporary(result_slot.clone()),
                qbe::Type::Long,
                qbe::Instr::Alloc8(8),
            );

            let (subject_var, subject_ty, enum_def, tag_var) =
                compile_match_subject(ctx, func, subject, variables, "match_expr");
            lower_match_dispatch(
                ctx,
                func,
                variables,
                &subject_var,
                &subject_ty,
                &enum_def,
                &tag_var,
                arms,
                |arm| &arm.pattern,
                "match_expr",
                true,
                |ctx, func, arm_variables, arm| {
                    let (arm_value, arm_value_ty) =
                        compile_expr(ctx, func, &arm.value, arm_variables);
                    assert_eq!(
                        arm_value_ty, match_ty,
                        "match expression arm type mismatch in codegen"
                    );
                    func.add_instr(qbe::Instr::Store(
                        match_qbe_ty.clone(),
                        qbe::Value::Temporary(result_slot.clone()),
                        qbe::Value::Temporary(arm_value),
                    ));
                    MatchArmOutcome::FallsThrough
                },
            );

            let result = new_id(&["match", "expr", "result"]);
            func.assign_instr(
                qbe::Value::Temporary(result.clone()),
                match_qbe_ty.clone(),
                qbe::Instr::Load(match_qbe_ty, qbe::Value::Temporary(result_slot)),
            );
            (result, match_ty)
        }
        parser::Expression::FieldAccess {
            struct_variable,
            field: field_name,
        } => {
            if let Some((struct_pointer_var, struct_name)) = variables.get(struct_variable.as_str())
            {
                let resolved = ctx.resolved.clone();
                let typedef = resolved.type_definitions.get(struct_name).unwrap();
                let ir::TypeDef::Struct(structdef) = typedef else {
                    panic!("Not really a struct: {struct_name}");
                };
                let field_offset = calculate_struct_field_offset(ctx, structdef, field_name);
                let field_type = if let ir::TypeDef::Struct(s) = typedef {
                    s.struct_fields
                        .iter()
                        .find(|f| f.name == *field_name)
                        .unwrap()
                        .ty
                        .clone()
                } else {
                    panic!("Expected struct type")
                };

                let id = new_id(&["field", "access"]);

                let struct_field_address_id = new_id(&["field", "address", &field_name]);
                func.assign_instr(
                    Value::Temporary(struct_field_address_id.clone()),
                    qbe::Type::Long,
                    Instr::Add(
                        Value::Temporary(struct_pointer_var.clone()),
                        Value::Const(field_offset),
                    ),
                );

                func.assign_instr(
                    Value::Temporary(id.clone()),
                    type_to_qbe(ctx.resolved.type_definitions.get(&field_type).unwrap()),
                    Instr::Load(
                        type_to_qbe(ctx.resolved.type_definitions.get(&field_type).unwrap()),
                        Value::Temporary(struct_field_address_id),
                    ),
                );

                (id, field_type)
            } else {
                let enum_def = match ctx.resolved.type_definitions.get(struct_variable) {
                    Some(ir::TypeDef::Enum(enum_def)) => enum_def,
                    _ => panic!("Unknown variable/type {}", struct_variable),
                };
                let variant = enum_def
                    .variants
                    .iter()
                    .find(|v| v.name == *field_name)
                    .unwrap();
                assert!(
                    variant.payload_ty.is_none(),
                    "payload enum variant requires constructor call"
                );
                if enum_def.is_tagged_union {
                    let enum_ptr = new_id(&["enum", "alloc"]);
                    func.assign_instr(
                        qbe::Value::Temporary(enum_ptr.clone()),
                        qbe::Type::Long,
                        qbe::Instr::Call(
                            "malloc".to_string(),
                            vec![(qbe::Type::Long, qbe::Value::Const(16))],
                            None,
                        ),
                    );
                    func.add_instr(qbe::Instr::Store(
                        qbe::Type::Word,
                        qbe::Value::Temporary(enum_ptr.clone()),
                        qbe::Value::Const(variant.tag as u64),
                    ));
                    let payload_addr = new_id(&["enum", "payload", "addr"]);
                    func.assign_instr(
                        qbe::Value::Temporary(payload_addr.clone()),
                        qbe::Type::Long,
                        qbe::Instr::Add(
                            qbe::Value::Temporary(enum_ptr.clone()),
                            qbe::Value::Const(8),
                        ),
                    );
                    func.add_instr(qbe::Instr::Store(
                        qbe::Type::Long,
                        qbe::Value::Temporary(payload_addr),
                        qbe::Value::Const(0),
                    ));
                    (enum_ptr, enum_def.name.clone())
                } else {
                    let id = new_id(&["enum", "variant", struct_variable, field_name]);
                    func.assign_instr(
                        qbe::Value::Temporary(id.clone()),
                        qbe::Type::Word,
                        qbe::Instr::Copy(qbe::Value::Const(variant.tag as u64)),
                    );
                    (id, enum_def.name.clone())
                }
            }
        }
        parser::Expression::PostfixCall { callee, args } => match callee.as_ref() {
            parser::Expression::FieldAccess {
                struct_variable,
                field,
            } => {
                if let Some(ir::TypeDef::Enum(enum_def)) =
                    ctx.resolved.type_definitions.get(struct_variable)
                {
                    if let Some(variant) = enum_def.variants.iter().find(|v| v.name == *field) {
                        variant
                            .payload_ty
                            .as_ref()
                            .expect("tag-only enum variant is not callable");
                        let enum_name = enum_def.name.clone();
                        let variant_tag = variant.tag;

                        assert_eq!(
                            args.len(),
                            1,
                            "enum payload constructors currently support a single argument"
                        );
                        let (arg_var, arg_ty) = compile_expr(ctx, func, &args[0], variables);
                        let enum_ptr = new_id(&["enum", "alloc"]);
                        func.assign_instr(
                            qbe::Value::Temporary(enum_ptr.clone()),
                            qbe::Type::Long,
                            qbe::Instr::Call(
                                "malloc".to_string(),
                                vec![(qbe::Type::Long, qbe::Value::Const(16))],
                                None,
                            ),
                        );

                        func.add_instr(qbe::Instr::Store(
                            qbe::Type::Word,
                            qbe::Value::Temporary(enum_ptr.clone()),
                            qbe::Value::Const(variant_tag as u64),
                        ));

                        let payload_addr = new_id(&["enum", "payload", "addr"]);
                        func.assign_instr(
                            qbe::Value::Temporary(payload_addr.clone()),
                            qbe::Type::Long,
                            qbe::Instr::Add(
                                qbe::Value::Temporary(enum_ptr.clone()),
                                qbe::Value::Const(8),
                            ),
                        );
                        let payload_qbe_ty = type_ref_to_qbe(ctx, &arg_ty);
                        func.add_instr(qbe::Instr::Store(
                            payload_qbe_ty,
                            qbe::Value::Temporary(payload_addr),
                            qbe::Value::Temporary(arg_var),
                        ));

                        return (enum_ptr, enum_name);
                    }
                }

                if ctx
                    .resolved
                    .trait_method_signatures
                    .contains_key(&trait_method_key(struct_variable, field))
                {
                    assert!(
                        !args.is_empty(),
                        "trait call {}.{} must pass receiver argument",
                        struct_variable,
                        field
                    );
                    let var_types = variables
                        .iter()
                        .map(|(name, (_, ty))| (name.clone(), ty.clone()))
                        .collect::<HashMap<_, _>>();
                    let self_type = ir::get_expression_type(
                        &args[0],
                        &var_types,
                        &ctx.resolved.function_sigs,
                        &ctx.resolved.type_definitions,
                        &ctx.resolved.trait_method_signatures,
                        &ctx.resolved.trait_impl_methods,
                    )
                    .expect("failed to resolve trait call receiver type");
                    let impl_key = trait_impl_method_key(struct_variable, &self_type, field);
                    let target = ctx
                        .resolved
                        .trait_impl_methods
                        .get(&impl_key)
                        .unwrap_or_else(|| {
                            panic!(
                                "missing impl for trait call {}.{} with receiver type {}",
                                struct_variable, field, self_type
                            )
                        })
                        .clone();
                    return compile_named_call(ctx, func, &target, args, variables);
                }

                let namespaced_call =
                    parser::qualify_namespace_function_name(struct_variable, field);
                if ctx.resolved.function_sigs.contains_key(&namespaced_call) {
                    return compile_named_call(ctx, func, &namespaced_call, args, variables);
                }

                panic!("unsupported postfix call target")
            }
            _ => panic!("unsupported postfix call target"),
        },
        parser::Expression::StructValue {
            struct_name,
            field_values,
        } => {
            let resolved = ctx.resolved.clone();
            let typedef = resolved.type_definitions.get(struct_name).unwrap();
            let ir::TypeDef::Struct(structdef) = typedef else {
                panic!("Not really a struct: {struct_name}");
            };
            let id = alloc_struct_zeroed(func, struct_size_bytes(ctx, structdef));

            for (field_name, field_value) in field_values {
                let (field_var, _) = compile_expr(ctx, func, field_value, variables);
                let field = structdef
                    .struct_fields
                    .iter()
                    .find(|f| &f.name == field_name)
                    .unwrap();
                let field_type = ctx
                    .resolved
                    .type_definitions
                    .get(&field.ty)
                    .unwrap()
                    .clone();
                let field_offset = calculate_struct_field_offset(ctx, &structdef, &field.name);
                let field_dest_id = new_id(&["field", "offset", &field.name]);
                func.assign_instr(
                    Value::Temporary(field_dest_id.clone()),
                    qbe::Type::Long,
                    Instr::Add(Value::Temporary(id.clone()), Value::Const(field_offset)),
                );
                func.add_instr(Instr::Store(
                    type_to_qbe(&field_type),
                    Value::Temporary(field_dest_id),
                    Value::Temporary(field_var.clone()),
                ));
            }

            (id, struct_name.to_string())
        }
        parser::Expression::Literal(parser::Literal::Int(value)) => {
            let id = new_id(&["literal", "int"]);
            func.assign_instr(
                Value::Temporary(id.clone()),
                Type::Word,
                qbe::Instr::Copy(qbe::Value::Const(*value as u64)),
            );

            (id, "I32".to_string())
        }
        parser::Expression::Literal(parser::Literal::Float32(value)) => {
            let id = new_id(&["literal", "fp32"]);
            func.assign_instr(
                Value::Temporary(id.clone()),
                Type::Single,
                qbe::Instr::Copy(qbe::Value::SingleConst(value.clone())),
            );
            (id, "FP32".to_string())
        }
        parser::Expression::Literal(parser::Literal::Float64(value)) => {
            let id = new_id(&["literal", "fp64"]);
            func.assign_instr(
                Value::Temporary(id.clone()),
                Type::Double,
                qbe::Instr::Copy(qbe::Value::DoubleConst(value.clone())),
            );
            (id, "FP64".to_string())
        }
        parser::Expression::Literal(parser::Literal::String(value)) => {
            let literal_ptr = new_id(&["literal", "string", "ptr"]);
            let const_name = new_id(&[]);
            ctx.module.add_data(qbe::DataDef::new(
                Linkage::private(),
                const_name.clone(),
                None,
                vec![
                    (qbe::Type::Byte, DataItem::Str(value.clone())),
                    (qbe::Type::Byte, DataItem::Const(0)),
                ],
            ));
            func.assign_instr(
                Value::Temporary(literal_ptr.clone()),
                Type::Long,
                qbe::Instr::Copy(qbe::Value::Global(const_name)),
            );
            let literal_len = new_id(&["literal", "string", "len"]);
            func.assign_instr(
                Value::Temporary(literal_len.clone()),
                Type::Word,
                qbe::Instr::Copy(qbe::Value::Const(value.len() as u64)),
            );

            let bytes_struct = std_bytes_struct(ctx);
            let bytes_ptr_offset = calculate_struct_field_offset(ctx, &bytes_struct, "ptr");
            let bytes_len_offset = calculate_struct_field_offset(ctx, &bytes_struct, "len");
            let bytes_ptr = new_id(&["literal", "string", "bytes", "alloc"]);
            func.assign_instr(
                Value::Temporary(bytes_ptr.clone()),
                qbe::Type::Long,
                qbe::Instr::Call(
                    "malloc".to_string(),
                    vec![(
                        qbe::Type::Long,
                        qbe::Value::Const(struct_size_bytes(ctx, &bytes_struct)),
                    )],
                    None,
                ),
            );

            let bytes_ptr_addr = new_id(&["literal", "string", "bytes", "ptr", "addr"]);
            func.assign_instr(
                Value::Temporary(bytes_ptr_addr.clone()),
                qbe::Type::Long,
                qbe::Instr::Add(
                    qbe::Value::Temporary(bytes_ptr.clone()),
                    qbe::Value::Const(bytes_ptr_offset),
                ),
            );
            func.add_instr(qbe::Instr::Store(
                qbe::Type::Long,
                qbe::Value::Temporary(bytes_ptr_addr),
                qbe::Value::Temporary(literal_ptr),
            ));

            let bytes_len_addr = new_id(&["literal", "string", "bytes", "len", "addr"]);
            func.assign_instr(
                qbe::Value::Temporary(bytes_len_addr.clone()),
                qbe::Type::Long,
                qbe::Instr::Add(
                    qbe::Value::Temporary(bytes_ptr.clone()),
                    qbe::Value::Const(bytes_len_offset),
                ),
            );
            func.add_instr(qbe::Instr::Store(
                qbe::Type::Word,
                qbe::Value::Temporary(bytes_len_addr),
                qbe::Value::Temporary(literal_len),
            ));

            let string_enum = std_string_enum(ctx);
            let literal_variant_tag = enum_variant_tag(&string_enum, "Literal");
            let string_ptr = new_id(&["literal", "string", "enum", "alloc"]);
            func.assign_instr(
                qbe::Value::Temporary(string_ptr.clone()),
                qbe::Type::Long,
                qbe::Instr::Call(
                    "malloc".to_string(),
                    vec![(qbe::Type::Long, qbe::Value::Const(TAGGED_UNION_SIZE_BYTES))],
                    None,
                ),
            );
            func.add_instr(qbe::Instr::Store(
                qbe::Type::Word,
                qbe::Value::Temporary(string_ptr.clone()),
                qbe::Value::Const(literal_variant_tag as u64),
            ));

            let payload_addr = new_id(&["literal", "string", "enum", "payload", "addr"]);
            func.assign_instr(
                qbe::Value::Temporary(payload_addr.clone()),
                qbe::Type::Long,
                qbe::Instr::Add(
                    qbe::Value::Temporary(string_ptr.clone()),
                    qbe::Value::Const(TAGGED_UNION_PAYLOAD_OFFSET_BYTES),
                ),
            );
            func.add_instr(qbe::Instr::Store(
                qbe::Type::Long,
                qbe::Value::Temporary(payload_addr),
                qbe::Value::Temporary(bytes_ptr),
            ));

            (string_ptr, "String".to_string())
        }
        parser::Expression::Literal(parser::Literal::Bool(value)) => {
            let id = new_id(&["literal", "bool"]);
            func.assign_instr(
                Value::Temporary(id.clone()),
                Type::Word,
                qbe::Instr::Copy(qbe::Value::Const(if *value { 1 } else { 0 })),
            );
            (id, "Bool".to_string())
        }
        parser::Expression::Variable(name) => {
            return variables.get(name).unwrap().clone();
        }
        parser::Expression::UnaryOp(op, expr) => {
            let id = new_id(&["unary_op"]);
            let (expr_var, _expr_ty) = compile_expr(ctx, func, expr, variables);

            match op {
                UnaryOp::Not => {
                    func.assign_instr(
                        qbe::Value::Temporary(id.clone()),
                        qbe::Type::Word,
                        qbe::Instr::Cmp(
                            qbe::Type::Word,
                            qbe::Cmp::Eq,
                            qbe::Value::Temporary(expr_var),
                            qbe::Value::Const(0),
                        ),
                    );
                }
            }

            (id, "Bool".to_string())
        }
        parser::Expression::Call(name, args) => {
            compile_named_call(ctx, func, name, args, variables)
        }
        parser::Expression::BinOp(op, left, right) => {
            let id = new_id(&["bin_op"]);
            let (left_var, left_ty) = compile_expr(ctx, func, left, variables);
            let (right_var, _right_ty) = compile_expr(ctx, func, right, variables);
            if matches!(op, Op::Eq | Op::Neq)
                && matches!(
                    ctx.resolved.type_definitions.get(&left_ty),
                    Some(ir::TypeDef::Struct(_))
                )
            {
                let memcmp_result = emit_struct_memcmp(ctx, func, &left_var, &right_var, &left_ty);
                let cmp_kind = if matches!(op, Op::Eq) {
                    qbe::Cmp::Eq
                } else {
                    qbe::Cmp::Ne
                };
                func.assign_instr(
                    qbe::Value::Temporary(id.clone()),
                    qbe::Type::Word,
                    qbe::Instr::Cmp(
                        qbe::Type::Word,
                        cmp_kind,
                        qbe::Value::Temporary(memcmp_result),
                        qbe::Value::Const(0),
                    ),
                );
                return (id, "Bool".to_string());
            }
            let operand_qbe_ty = type_ref_to_qbe(ctx, &left_ty);
            let use_unsigned_int_cmp = left_ty == "U8";
            let use_ordered_float_cmp =
                matches!(operand_qbe_ty, qbe::Type::Single | qbe::Type::Double);

            let instr = match (op, &operand_qbe_ty) {
                (Op::Eq, _) => qbe::Instr::Cmp(
                    operand_qbe_ty.clone(),
                    qbe::Cmp::Eq,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Neq, _) => qbe::Instr::Cmp(
                    operand_qbe_ty.clone(),
                    qbe::Cmp::Ne,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Lt, _) if use_ordered_float_cmp => qbe::Instr::Cmp(
                    operand_qbe_ty.clone(),
                    qbe::Cmp::Lt,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Gt, _) if use_ordered_float_cmp => qbe::Instr::Cmp(
                    operand_qbe_ty.clone(),
                    qbe::Cmp::Gt,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Le, _) if use_ordered_float_cmp => qbe::Instr::Cmp(
                    operand_qbe_ty.clone(),
                    qbe::Cmp::Le,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Ge, _) if use_ordered_float_cmp => qbe::Instr::Cmp(
                    operand_qbe_ty.clone(),
                    qbe::Cmp::Ge,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Lt, _) if use_unsigned_int_cmp => qbe::Instr::Cmp(
                    operand_qbe_ty.clone(),
                    qbe::Cmp::Ult,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Gt, _) if use_unsigned_int_cmp => qbe::Instr::Cmp(
                    operand_qbe_ty.clone(),
                    qbe::Cmp::Ugt,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Le, _) if use_unsigned_int_cmp => qbe::Instr::Cmp(
                    operand_qbe_ty.clone(),
                    qbe::Cmp::Ule,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Ge, _) if use_unsigned_int_cmp => qbe::Instr::Cmp(
                    operand_qbe_ty.clone(),
                    qbe::Cmp::Uge,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Lt, _) => qbe::Instr::Cmp(
                    operand_qbe_ty.clone(),
                    qbe::Cmp::Slt,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Gt, _) => qbe::Instr::Cmp(
                    operand_qbe_ty.clone(),
                    qbe::Cmp::Sgt,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Le, _) => qbe::Instr::Cmp(
                    operand_qbe_ty.clone(),
                    qbe::Cmp::Sle,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Ge, _) => qbe::Instr::Cmp(
                    operand_qbe_ty.clone(),
                    qbe::Cmp::Sge,
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Add, _) => qbe::Instr::Add(
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Sub, _) => qbe::Instr::Sub(
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Mul, _) => qbe::Instr::Mul(
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Div, _) if use_unsigned_int_cmp => qbe::Instr::Udiv(
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Div, _) => qbe::Instr::Div(
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::And, _) => qbe::Instr::And(
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
                (Op::Or, _) => qbe::Instr::Or(
                    qbe::Value::Temporary(left_var),
                    qbe::Value::Temporary(right_var),
                ),
            };

            let result_qbe_ty = match op {
                Op::Eq | Op::Neq | Op::Lt | Op::Gt | Op::Le | Op::Ge => qbe::Type::Word,
                Op::Add | Op::Sub | Op::Mul | Op::Div => operand_qbe_ty,
                Op::And | Op::Or => qbe::Type::Word,
            };
            func.assign_instr(qbe::Value::Temporary(id.clone()), result_qbe_ty, instr);

            let out_ty = match op {
                Op::And | Op::Or => "Bool".to_string(),
                Op::Eq | Op::Neq | Op::Lt | Op::Gt | Op::Le | Op::Ge => "Bool".to_string(),
                Op::Add | Op::Sub | Op::Mul | Op::Div => left_ty,
            };

            (id, out_ty)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{compile, ir, parser::parse, tokenizer::tokenize, Build};
    use std::{
        fs,
        path::{Path, PathBuf},
        process::{Command, Stdio},
        thread::sleep,
        time::{Duration, Instant},
    };

    use super::compile as compile_qbe;
    const EXECUTION_TIMEOUT: Duration = Duration::from_secs(5);
    const EXECUTION_SNAPSHOT_PREFIX: &str = "oac__qbe_backend__tests__execution_tests__";
    const SNAPSHOT_EXTENSION: &str = ".snap";

    fn execution_snapshot_files() -> Vec<PathBuf> {
        let mut files = fs::read_dir("src/snapshots")
            .expect("read snapshots directory")
            .filter_map(|entry| {
                let path = entry.ok()?.path();
                let file_name = path.file_name()?.to_string_lossy();
                if file_name.starts_with(EXECUTION_SNAPSHOT_PREFIX)
                    && file_name.ends_with(SNAPSHOT_EXTENSION)
                {
                    Some(path)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        files.sort();
        files
    }

    fn fixture_name_for_snapshot(snapshot_path: &Path) -> Option<String> {
        let file_name = snapshot_path.file_name()?.to_string_lossy();
        if !file_name.starts_with(EXECUTION_SNAPSHOT_PREFIX)
            || !file_name.ends_with(SNAPSHOT_EXTENSION)
        {
            return None;
        }
        let stem = file_name
            .strip_prefix(EXECUTION_SNAPSHOT_PREFIX)?
            .strip_suffix(SNAPSHOT_EXTENSION)?;
        Some(stem.to_string())
    }

    fn run_executable_with_timeout(workdir: &Path) -> Result<String, String> {
        let mut child = Command::new("./target/oac/app")
            .current_dir(workdir)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|err| format!("failed to spawn executable: {err}"))?;

        let started = Instant::now();
        loop {
            match child.try_wait() {
                Ok(Some(_)) => {
                    let output = child
                        .wait_with_output()
                        .map_err(|err| format!("failed to collect executable output: {err}"))?;

                    if output.status.code().is_none() {
                        return Err(format!(
                            "executable terminated by signal\\nstdout:\\n{}\\nstderr:\\n{}",
                            String::from_utf8_lossy(&output.stdout),
                            String::from_utf8_lossy(&output.stderr)
                        ));
                    }

                    return String::from_utf8(output.stdout)
                        .map_err(|err| format!("executable stdout was not valid UTF-8: {err}"));
                }
                Ok(None) => {
                    if started.elapsed() > EXECUTION_TIMEOUT {
                        let _ = child.kill();
                        let _ = child.wait();
                        return Err(format!(
                            "execution timed out after {} seconds",
                            EXECUTION_TIMEOUT.as_secs()
                        ));
                    }
                    sleep(Duration::from_millis(25));
                }
                Err(err) => {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(format!("failed while waiting for executable: {err}"));
                }
            }
        }
    }

    fn compile_source_to_qbe_ir(source: &str) -> String {
        let tokens = tokenize(source.to_string()).expect("tokenize source");
        let program = parse(tokens).expect("parse source");
        let ir = ir::resolve(program).expect("resolve source");
        let qbe_module = compile_qbe(ir);
        format!("{qbe_module}")
    }

    #[test]
    fn qbe_codegen_supports_namespaced_function_calls() {
        let source = r#"
struct Option {
	value: I32,
}

namespace Option {
	fun is_some(v: Option) -> I32 {
		return v.value
	}
}

fun main() -> I32 {
	v = Option struct { value: 7 }
	return Option.is_some(v)
}
"#
        .to_string();

        let qbe_ir = compile_source_to_qbe_ir(&source);
        assert!(
            qbe_ir.contains("call $Option__is_some"),
            "expected namespaced function call in qbe output, got:\n{qbe_ir}"
        );
    }

    #[test]
    fn qbe_codegen_supports_char_literals() {
        let source = r#"
fun main() -> I32 {
	ch = 'x'
	return Char.code(ch)
}
"#
        .to_string();

        let qbe_ir = compile_source_to_qbe_ir(&source);
        assert!(
            qbe_ir.contains("call $Char__from_code"),
            "expected Char literal lowering call in qbe output, got:\n{qbe_ir}"
        );
    }

    #[test]
    fn qbe_codegen_supports_void_extern_call_statement() {
        let source = r#"
fun main() -> I32 {
	Clib.free(i32_to_i64(0))
	return 0
}
"#
        .to_string();

        let qbe_ir = compile_source_to_qbe_ir(&source);
        assert!(
            qbe_ir.contains("call $free"),
            "expected void extern call in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            !qbe_ir.contains("call $Clib__free"),
            "namespaced std clib calls should lower to libc symbol names, got:\n{qbe_ir}"
        );
    }

    #[test]
    fn qbe_codegen_structs_use_copy_barriers_and_memcmp_equality() {
        let source = r#"
struct Box {
	value: I32,
}

fun id(v: Box) -> Box {
	return v
}

fun consume(v: Box) -> I32 {
	return v.value
}

fun main() -> I32 {
	a = Box struct { value: 7 }
	b = a
	c = id(b)
	if a == c {
		return consume(c)
	}
	return 0
}
"#
        .to_string();

        let qbe_ir = compile_source_to_qbe_ir(&source);
        assert!(
            qbe_ir.contains("call $memcmp"),
            "expected struct equality lowering via memcmp, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.matches("call $memcpy").count() >= 4,
            "expected struct copy barriers to emit memcpy calls, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.matches("call $calloc").count() >= 3,
            "expected struct allocations/clones to emit calloc calls, got:\n{qbe_ir}"
        );
    }

    #[test]
    fn qbe_codegen_i32_to_i64_uses_signed_extension() {
        let source = r#"
fun main() -> I32 {
	x = i32_to_i64(300)
	return 0
}
"#
        .to_string();

        let qbe_ir = compile_source_to_qbe_ir(&source);
        assert!(
            qbe_ir.contains("function l $i32_to_i64"),
            "expected i32_to_i64 helper in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("extsw %a"),
            "expected i32_to_i64 to use signed extension, got:\n{qbe_ir}"
        );
        assert!(
            !qbe_ir.contains("extub %a"),
            "did not expect byte extension in i32_to_i64 helper, got:\n{qbe_ir}"
        );
    }

    #[test]
    fn qbe_codegen_supports_fp32_literals_and_compares() {
        let source = r#"
fun main() -> I32 {
	a = 1.25
	b = 2.5
	c = a + b
	if c > b {
		return 1
	}
	return 0
}
"#
        .to_string();

        let qbe_ir = compile_source_to_qbe_ir(&source);
        assert!(
            qbe_ir.contains("s_1.25"),
            "expected fp32 constant in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("=s add"),
            "expected fp32 add assignment in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("cgts"),
            "expected fp32 ordered comparison in qbe output, got:\n{qbe_ir}"
        );
    }

    #[test]
    fn qbe_codegen_supports_fp64_literals_and_compares() {
        let source = r#"
fun main() -> I32 {
	a = 1.25f64
	b = 2.5f64
	c = a + b
	if c > b {
		return 1
	}
	return 0
}
"#
        .to_string();

        let qbe_ir = compile_source_to_qbe_ir(&source);
        assert!(
            qbe_ir.contains("d_1.25"),
            "expected fp64 constant in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("=d add"),
            "expected fp64 add assignment in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("cgtd"),
            "expected fp64 ordered comparison in qbe output, got:\n{qbe_ir}"
        );
    }

    #[test]
    fn qbe_codegen_supports_u8_unsigned_ops() {
        let source = r#"
fun is_lt(a: U8, b: U8) -> Bool {
	return a < b
}

fun divide(a: U8, b: U8) -> U8 {
	return a / b
}

fun main() -> I32 {
	return 0
}
"#
        .to_string();

        let qbe_ir = compile_source_to_qbe_ir(&source);
        assert!(
            qbe_ir.contains("cultw"),
            "expected unsigned U8 comparison in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("udiv"),
            "expected unsigned U8 division in qbe output, got:\n{qbe_ir}"
        );
    }

    #[test]
    fn qbe_codegen_supports_pointer_load_and_store_builtins() {
        let source = r#"
fun main(argc: I32, argv: PtrInt) -> I32 {
	b = load_u8(argv)
	w = load_i32(argv)
	l = load_i64(argv)
	flag = load_bool(argv)
	store_u8(argv, b)
	store_i32(argv, w)
	store_i64(argv, l)
	store_bool(argv, flag)
	if flag {
		return w
	}
	return argc
}
"#
        .to_string();

        let qbe_ir = compile_source_to_qbe_ir(&source);
        assert!(
            qbe_ir.contains("function w $load_u8"),
            "expected load_u8 builtin definition in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("function $store_u8"),
            "expected store_u8 builtin definition in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("call $load_u8"),
            "expected call to load_u8 in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("function w $load_i32"),
            "expected load_i32 builtin definition in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("call $load_i32"),
            "expected call to load_i32 in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("function l $load_i64"),
            "expected load_i64 builtin definition in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("call $load_i64"),
            "expected call to load_i64 in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("function w $load_bool"),
            "expected load_bool builtin definition in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("call $load_bool"),
            "expected call to load_bool in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("call $store_u8"),
            "expected call to store_u8 in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("function $store_i32"),
            "expected store_i32 builtin definition in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("call $store_i32"),
            "expected call to store_i32 in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("function $store_i64"),
            "expected store_i64 builtin definition in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("call $store_i64"),
            "expected call to store_i64 in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("function $store_bool"),
            "expected store_bool builtin definition in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("call $store_bool"),
            "expected call to store_bool in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("loadw %addr"),
            "expected load_i32/load_bool lowering to loadw in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("loadl %addr"),
            "expected load_i64 lowering to loadl in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("loadub %addr"),
            "expected load_u8 lowering to loadub in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("storeb %value, %addr"),
            "expected store_u8 lowering to storeb in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("storew %value, %addr"),
            "expected store_i32/store_bool lowering to storew in qbe output, got:\n{qbe_ir}"
        );
        assert!(
            qbe_ir.contains("storel %value, %addr"),
            "expected store_i64 lowering to storel in qbe output, got:\n{qbe_ir}"
        );
    }

    #[test]
    fn execution_tests() {
        let test_files = fs::read_dir("execution_tests").unwrap();

        for path in test_files {
            println!("Testing {}", path.as_ref().unwrap().path().display());

            let path = path.unwrap().path();
            let tmp = tempfile::tempdir().unwrap();

            match compile(
                &tmp.path(),
                Build {
                    source: path.to_string_lossy().to_string(),
                    arch: None,
                },
            ) {
                Ok(()) => (),
                Err(err) => {
                    insta::assert_snapshot!(
                        path.display().to_string(),
                        format!("COMPILATION ERROR\n\n{err}")
                    );
                    continue;
                }
            };

            match run_executable_with_timeout(tmp.path()) {
                Ok(output) => insta::assert_snapshot!(path.display().to_string(), output),
                Err(err) => {
                    insta::assert_snapshot!(
                        path.display().to_string(),
                        format!("RUNTIME ERROR\n\n{err}")
                    );
                }
            }
        }
    }

    #[test]
    fn execution_snapshot_hygiene_contract() {
        let pending = fs::read_dir("src/snapshots")
            .expect("read snapshots directory")
            .filter_map(|entry| {
                let path = entry.ok()?.path();
                let file_name = path.file_name()?.to_string_lossy();
                if file_name.ends_with(".snap.new") {
                    Some(file_name.to_string())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        assert!(
            pending.is_empty(),
            "committed .snap.new files are not allowed: {pending:?}"
        );

        let mut missing_fixtures = Vec::new();
        let mut duplicated_prefix = Vec::new();
        for snapshot_path in execution_snapshot_files() {
            let fixture_name =
                fixture_name_for_snapshot(&snapshot_path).expect("valid execution snapshot path");
            let fixture_path = Path::new("execution_tests").join(&fixture_name);
            if !fixture_path.exists() {
                missing_fixtures.push(fixture_name);
            }

            let snapshot = fs::read_to_string(&snapshot_path)
                .unwrap_or_else(|_| panic!("read snapshot {}", snapshot_path.display()));
            if snapshot.contains("Error: error[") {
                duplicated_prefix.push(snapshot_path.display().to_string());
            }
        }

        assert!(
            missing_fixtures.is_empty(),
            "execution snapshots without matching fixtures: {missing_fixtures:?}"
        );
        assert!(
            duplicated_prefix.is_empty(),
            "diagnostics with duplicated error prefix found in snapshots: {duplicated_prefix:?}"
        );
    }
}
