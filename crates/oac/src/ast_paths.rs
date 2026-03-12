#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(dead_code)]
pub(crate) enum AstPathStyle {
    Ir,
    StructInvariants,
}

pub(crate) fn separator(style: AstPathStyle) -> &'static str {
    match style {
        AstPathStyle::Ir => "/",
        AstPathStyle::StructInvariants => ".",
    }
}

pub(crate) fn join_path(prefix: &str, segment: &str, style: AstPathStyle) -> String {
    if prefix.is_empty() {
        segment.to_string()
    } else {
        format!("{prefix}{}{segment}", separator(style))
    }
}

pub(crate) fn expression_statement_segment(style: AstPathStyle) -> &'static str {
    match style {
        AstPathStyle::Ir => "expr",
        AstPathStyle::StructInvariants => "expr.expr",
    }
}

pub(crate) fn if_then_statement_segment(style: AstPathStyle, index: usize) -> String {
    match style {
        AstPathStyle::Ir => format!("if.body.{index}"),
        AstPathStyle::StructInvariants => format!("if.then.{index}"),
    }
}

pub(crate) fn if_else_statement_segment(_style: AstPathStyle, index: usize) -> String {
    format!("if.else.{index}")
}

pub(crate) fn while_body_statement_segment(_style: AstPathStyle, index: usize) -> String {
    format!("while.body.{index}")
}

pub(crate) fn match_arm_statement_segment(
    _style: AstPathStyle,
    arm_index: usize,
    statement_index: usize,
) -> String {
    format!("match.arm.{arm_index}.{statement_index}")
}

pub(crate) fn match_arm_expression_segment(_style: AstPathStyle, arm_index: usize) -> String {
    format!("match.arm.{arm_index}")
}

pub(crate) fn bin_left_segment(style: AstPathStyle) -> &'static str {
    match style {
        AstPathStyle::Ir => "bin.left",
        AstPathStyle::StructInvariants => "bin.lhs",
    }
}

pub(crate) fn bin_right_segment(style: AstPathStyle) -> &'static str {
    match style {
        AstPathStyle::Ir => "bin.right",
        AstPathStyle::StructInvariants => "bin.rhs",
    }
}

pub(crate) fn unary_segment(style: AstPathStyle) -> &'static str {
    match style {
        AstPathStyle::Ir => "unary",
        AstPathStyle::StructInvariants => "unary.expr",
    }
}

pub(crate) fn struct_field_segment(style: AstPathStyle, index: usize, field_name: &str) -> String {
    match style {
        AstPathStyle::Ir => format!("struct.field.{index}"),
        AstPathStyle::StructInvariants => format!("struct.field.{field_name}"),
    }
}

pub(crate) fn local_statement_key(index: usize) -> String {
    format!("stmt:{index}")
}

pub(crate) fn local_precondition_key(index: usize) -> String {
    format!("pre:{index}")
}

pub(crate) fn marker_path_id(path: &str) -> String {
    let sanitized = path
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
        .collect::<String>();
    const MAX_INLINE_LEN: usize = 32;
    const HASHED_PREFIX_LEN: usize = 14;
    if sanitized.len() <= MAX_INLINE_LEN {
        return sanitized;
    }

    let mut hash = 0xcbf29ce484222325u64;
    for byte in path.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }

    format!("{}_h{hash:016x}", &sanitized[..HASHED_PREFIX_LEN])
}
