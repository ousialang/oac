use crate::builtins::BuiltInType;
use crate::ir::{EnumTypeDef, ResolvedProgram, TypeDef};
use crate::parser::StructDef;

pub(crate) const TAGGED_UNION_PAYLOAD_OFFSET_BYTES: u64 = 8;
pub(crate) const TAGGED_UNION_SIZE_BYTES: u64 = 16;

pub(crate) fn value_slot_size(program: &ResolvedProgram, ty: &str) -> u64 {
    match program.type_definitions.get(ty) {
        Some(TypeDef::BuiltIn(BuiltInType::Bool))
        | Some(TypeDef::BuiltIn(BuiltInType::U8))
        | Some(TypeDef::BuiltIn(BuiltInType::I32))
        | Some(TypeDef::BuiltIn(BuiltInType::FP32)) => 4,
        Some(TypeDef::BuiltIn(BuiltInType::I64))
        | Some(TypeDef::BuiltIn(BuiltInType::FP64))
        | Some(TypeDef::Struct(_)) => 8,
        Some(TypeDef::Enum(enum_def)) => {
            if enum_def.is_tagged_union {
                8
            } else {
                4
            }
        }
        Some(TypeDef::BuiltIn(BuiltInType::Void)) => {
            panic!("Void cannot be used in value-layout positions")
        }
        Some(TypeDef::BuiltIn(BuiltInType::Semantic)) => {
            panic!("semantic-only builtin types cannot be used in value-layout positions")
        }
        None => panic!("unknown type {ty} for runtime layout"),
    }
}

pub(crate) fn struct_field_offset(
    program: &ResolvedProgram,
    struct_def: &StructDef,
    field_name: &str,
) -> u64 {
    let mut offset = 0;
    for field in &struct_def.struct_fields {
        if field.name == field_name {
            return offset;
        }
        offset += value_slot_size(program, &field.ty);
    }

    panic!(
        "field {} not found in struct {}",
        field_name, struct_def.name
    );
}

pub(crate) fn struct_size_bytes(program: &ResolvedProgram, struct_def: &StructDef) -> u64 {
    struct_def
        .struct_fields
        .iter()
        .map(|field| value_slot_size(program, &field.ty))
        .sum()
}

pub(crate) fn struct_size_bytes_by_name(program: &ResolvedProgram, struct_name: &str) -> u64 {
    let type_def = program
        .type_definitions
        .get(struct_name)
        .unwrap_or_else(|| panic!("unknown struct type {struct_name}"));
    let TypeDef::Struct(struct_def) = type_def else {
        panic!("type {struct_name} is not a struct");
    };
    struct_size_bytes(program, struct_def)
}

pub(crate) fn std_bytes_struct(program: &ResolvedProgram) -> StructDef {
    match program.type_definitions.get("Bytes") {
        Some(TypeDef::Struct(def)) => def.clone(),
        _ => panic!("std Bytes struct is required for String lowering"),
    }
}

pub(crate) fn std_string_enum(program: &ResolvedProgram) -> EnumTypeDef {
    match program.type_definitions.get("String") {
        Some(TypeDef::Enum(def)) if def.is_tagged_union => def.clone(),
        Some(TypeDef::Enum(_)) => panic!("std String must be a tagged-union enum"),
        _ => panic!("std String enum is required for String lowering"),
    }
}

pub(crate) fn enum_variant_tag(enum_def: &EnumTypeDef, variant_name: &str) -> u32 {
    enum_def
        .variants
        .iter()
        .find(|variant| variant.name == variant_name)
        .unwrap_or_else(|| panic!("missing variant {variant_name} on enum {}", enum_def.name))
        .tag
}
