use std::collections::{BTreeSet, HashMap};

use thiserror::Error;

/// Options for CHC/fixedpoint QBE-to-SMT encoding.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct EncodeOptions {
    /// Add `argc >= 0` constraint for the first function argument in the initial state.
    pub assume_main_argc_non_negative: bool,
}

impl Default for EncodeOptions {
    fn default() -> Self {
        Self {
            assume_main_argc_non_negative: false,
        }
    }
}

/// Errors produced by the parser/encoder.
#[derive(Debug, Error)]
pub enum QbeSmtError {
    #[error("line {line}: {message}")]
    Parse { line: usize, message: String },
    #[error("unknown label @{label}")]
    UnknownLabel { label: String },
    #[error("duplicate block label @{label}")]
    DuplicateLabel { label: String },
    #[error("no instructions found in the function body")]
    EmptyFunction,
    #[error("unsupported QBE operation for strict proving: {message}")]
    Unsupported { message: String },
}

/// Encode one QBE function body into SMT-LIB text.
///
/// This encoder aims to support most integer-centric QBE IR used by Ousia:
/// arithmetic/logic, comparisons, calls, loads/stores, alloc*, extensions,
/// branches, and returns.
pub fn qbe_to_smt(source: &str, options: &EncodeOptions) -> Result<String, QbeSmtError> {
    let function = parse_function(source)?;
    encode_function(&function, options)
}

#[derive(Debug, Clone)]
struct Function {
    args: Vec<FunctionArg>,
    blocks: Vec<Block>,
}

#[derive(Debug, Clone)]
struct FunctionArg {
    name: String,
    ty: AssignType,
}

#[derive(Debug, Clone)]
struct Block {
    label: String,
    instructions: Vec<Instruction>,
}

#[derive(Debug, Clone)]
enum Instruction {
    Binary {
        dest: String,
        ty: AssignType,
        op: BinaryOp,
        lhs: Value,
        rhs: Value,
    },
    Copy {
        dest: String,
        ty: AssignType,
        value: Value,
    },
    Cmp {
        dest: String,
        ty: AssignType,
        kind: CmpKind,
        cmp_ty: AssignType,
        lhs: Value,
        rhs: Value,
    },
    Unary {
        dest: String,
        ty: AssignType,
        op: UnaryOp,
        value: Value,
    },
    Load {
        dest: String,
        ty: AssignType,
        load_ty: QbeType,
        address: Value,
    },
    Alloc {
        dest: String,
        ty: AssignType,
        align: u32,
        size: u64,
    },
    Call {
        dest: Option<String>,
        ty: Option<AssignType>,
        function: String,
        args: Vec<Value>,
    },
    Store {
        store_ty: QbeType,
        value: Value,
        address: Value,
    },
    Blit {
        src: Value,
        dst: Value,
        len: u64,
    },
    Phi {
        dest: String,
        ty: AssignType,
        _left_label: String,
        _left_value: Value,
        _right_label: String,
        _right_value: Value,
    },
    UnsupportedAssign {
        dest: String,
        ty: AssignType,
        _text: String,
    },
    UnsupportedVolatile {
        _text: String,
    },
    Nop,
    Jnz {
        cond: Value,
        if_true: String,
        if_false: String,
    },
    Jmp {
        target: String,
    },
    Ret {
        value: Option<Value>,
    },
    Hlt,
}

impl Instruction {
    fn dest(&self) -> Option<&str> {
        match self {
            Instruction::Binary { dest, .. }
            | Instruction::Copy { dest, .. }
            | Instruction::Cmp { dest, .. }
            | Instruction::Unary { dest, .. }
            | Instruction::Load { dest, .. }
            | Instruction::Alloc { dest, .. }
            | Instruction::Phi { dest, .. }
            | Instruction::UnsupportedAssign { dest, .. } => Some(dest.as_str()),
            Instruction::Call {
                dest: Some(dest), ..
            } => Some(dest.as_str()),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
enum Value {
    Temp(String),
    Global(String),
    Const(u64),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum AssignType {
    Word,
    Long,
    Single,
    Double,
}

impl AssignType {
    fn bits(self) -> u32 {
        match self {
            AssignType::Word | AssignType::Single => 32,
            AssignType::Long | AssignType::Double => 64,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum QbeType {
    Byte,
    SignedByte,
    UnsignedByte,
    Halfword,
    SignedHalfword,
    UnsignedHalfword,
    Word,
    Long,
    Single,
    Double,
    Aggregate,
    Zero,
}

impl QbeType {
    fn from_token(token: &str) -> Option<Self> {
        match token {
            "b" => Some(Self::Byte),
            "sb" => Some(Self::SignedByte),
            "ub" => Some(Self::UnsignedByte),
            "h" => Some(Self::Halfword),
            "sh" => Some(Self::SignedHalfword),
            "uh" => Some(Self::UnsignedHalfword),
            "w" => Some(Self::Word),
            "l" => Some(Self::Long),
            "s" => Some(Self::Single),
            "d" => Some(Self::Double),
            "z" => Some(Self::Zero),
            _ if token.starts_with(':') => Some(Self::Aggregate),
            _ => None,
        }
    }

    fn into_base_assign(self) -> AssignType {
        match self {
            QbeType::Byte
            | QbeType::SignedByte
            | QbeType::UnsignedByte
            | QbeType::Halfword
            | QbeType::SignedHalfword
            | QbeType::UnsignedHalfword
            | QbeType::Word
            | QbeType::Zero => AssignType::Word,
            QbeType::Long | QbeType::Aggregate => AssignType::Long,
            QbeType::Single => AssignType::Single,
            QbeType::Double => AssignType::Double,
        }
    }

    fn load_store_width_bits(self) -> Option<u32> {
        match self {
            QbeType::Byte | QbeType::SignedByte | QbeType::UnsignedByte | QbeType::Zero => Some(8),
            QbeType::Halfword | QbeType::SignedHalfword | QbeType::UnsignedHalfword => Some(16),
            QbeType::Word | QbeType::Single => Some(32),
            QbeType::Long | QbeType::Double => Some(64),
            QbeType::Aggregate => None,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Udiv,
    Rem,
    Urem,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Sar,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum UnaryOp {
    Cast,
    Extsw,
    Extuw,
    Extsh,
    Extuh,
    Extsb,
    Extub,
    Unsupported(&'static str),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum CmpKind {
    Eq,
    Ne,
    Slt,
    Sle,
    Sgt,
    Sge,
    Ult,
    Ule,
    Ugt,
    Uge,
    O,
    Uo,
}

const BLIT_INLINE_LIMIT: u64 = 64;
const INITIAL_HEAP_BASE: u64 = 0x0010_0000;
const GLOBAL_BASE: u64 = 0x4000_0000;
const GLOBAL_STRIDE: u64 = 0x1000;

fn parse_function(source: &str) -> Result<Function, QbeSmtError> {
    let lines: Vec<&str> = source.lines().collect();
    let mut idx = 0usize;

    while idx < lines.len() && normalize_line(lines[idx]).is_empty() {
        idx += 1;
    }

    if idx >= lines.len() {
        return Err(QbeSmtError::Parse {
            line: 1,
            message: "expected function header".to_string(),
        });
    }

    let (args, header_has_open_brace) = parse_function_header(lines[idx], idx + 1)?;
    idx += 1;

    if !header_has_open_brace {
        while idx < lines.len() && normalize_line(lines[idx]).is_empty() {
            idx += 1;
        }
        if idx >= lines.len() || normalize_line(lines[idx]) != "{" {
            return Err(QbeSmtError::Parse {
                line: idx.saturating_add(1),
                message: "expected `{` after function header".to_string(),
            });
        }
        idx += 1;
    }

    let mut blocks = Vec::new();
    let mut current_block: Option<Block> = None;
    let mut found_closing_brace = false;

    while idx < lines.len() {
        let raw = lines[idx];
        let line_no = idx + 1;
        let line = normalize_line(raw);
        idx += 1;

        if line.is_empty() {
            continue;
        }

        if line == "}" {
            if let Some(block) = current_block.take() {
                blocks.push(block);
            }
            found_closing_brace = true;
            break;
        }

        if let Some(rest) = line.strip_prefix('@') {
            let label = parse_label(rest, line_no)?;
            if let Some(block) = current_block.take() {
                blocks.push(block);
            }
            current_block = Some(Block {
                label,
                instructions: Vec::new(),
            });
            continue;
        }

        let block = current_block.as_mut().ok_or(QbeSmtError::Parse {
            line: line_no,
            message: "instruction outside of a block; expected `@label`".to_string(),
        })?;
        let instruction = parse_instruction(&line, line_no)?;
        block.instructions.push(instruction);
    }

    while idx < lines.len() {
        if !normalize_line(lines[idx]).is_empty() {
            return Err(QbeSmtError::Parse {
                line: idx + 1,
                message: "only a single function is supported in this slice".to_string(),
            });
        }
        idx += 1;
    }

    if !found_closing_brace {
        return Err(QbeSmtError::Parse {
            line: lines.len(),
            message: "missing closing `}` for function".to_string(),
        });
    }

    Ok(Function { args, blocks })
}

fn parse_function_header(
    line: &str,
    line_no: usize,
) -> Result<(Vec<FunctionArg>, bool), QbeSmtError> {
    let normalized = normalize_line(line);
    if !normalized.contains("function") || !normalized.contains('$') || !normalized.contains('(') {
        return Err(QbeSmtError::Parse {
            line: line_no,
            message: "invalid function header".to_string(),
        });
    }

    let open_paren = normalized.find('(').ok_or(QbeSmtError::Parse {
        line: line_no,
        message: "missing `(` in function header".to_string(),
    })?;
    let close_paren = normalized.rfind(')').ok_or(QbeSmtError::Parse {
        line: line_no,
        message: "missing `)` in function header".to_string(),
    })?;
    if close_paren < open_paren {
        return Err(QbeSmtError::Parse {
            line: line_no,
            message: "malformed function arguments".to_string(),
        });
    }

    let args_str = &normalized[open_paren + 1..close_paren];
    let mut args = Vec::new();
    if !args_str.trim().is_empty() {
        for arg in args_str.split(',') {
            let arg = arg.trim();
            if arg.is_empty() {
                continue;
            }

            let (ty_token, value_token) = split_once_whitespace(arg).ok_or(QbeSmtError::Parse {
                line: line_no,
                message: format!("function argument `{arg}` must be `<type> %name`"),
            })?;
            let ty = parse_assign_type(ty_token).ok_or(QbeSmtError::Parse {
                line: line_no,
                message: format!("unknown argument type token `{ty_token}`"),
            })?;
            let name = value_token
                .trim()
                .strip_prefix('%')
                .ok_or(QbeSmtError::Parse {
                    line: line_no,
                    message: format!("argument `{arg}` must use a `%` temporary"),
                })?
                .trim();
            if name.is_empty() {
                return Err(QbeSmtError::Parse {
                    line: line_no,
                    message: "empty function argument temporary".to_string(),
                });
            }
            args.push(FunctionArg {
                name: name.to_string(),
                ty,
            });
        }
    }

    Ok((args, normalized.contains('{')))
}

fn parse_label(after_at: &str, line_no: usize) -> Result<String, QbeSmtError> {
    let label = after_at
        .split_whitespace()
        .next()
        .unwrap_or_default()
        .trim();
    if label.is_empty() {
        return Err(QbeSmtError::Parse {
            line: line_no,
            message: "empty block label".to_string(),
        });
    }
    Ok(label.to_string())
}

fn parse_instruction(line: &str, line_no: usize) -> Result<Instruction, QbeSmtError> {
    if let Some(rest) = line.strip_prefix('%') {
        return parse_assignment(rest, line_no);
    }

    if let Some(rest) = line.strip_prefix("jnz ") {
        let parts: Vec<&str> = rest.split(',').map(|it| it.trim()).collect();
        if parts.len() != 3 {
            return Err(QbeSmtError::Parse {
                line: line_no,
                message: "expected `jnz cond, @true, @false`".to_string(),
            });
        }
        let cond = parse_value(parts[0], line_no)?;
        let if_true = parts[1].trim_start_matches('@').to_string();
        let if_false = parts[2].trim_start_matches('@').to_string();
        if if_true.is_empty() || if_false.is_empty() {
            return Err(QbeSmtError::Parse {
                line: line_no,
                message: "jnz targets must be labels".to_string(),
            });
        }
        return Ok(Instruction::Jnz {
            cond,
            if_true,
            if_false,
        });
    }

    if let Some(rest) = line.strip_prefix("jmp ") {
        let target = rest.trim().trim_start_matches('@').to_string();
        if target.is_empty() {
            return Err(QbeSmtError::Parse {
                line: line_no,
                message: "jmp target must be a label".to_string(),
            });
        }
        return Ok(Instruction::Jmp { target });
    }

    if let Some(rest) = line.strip_prefix("ret") {
        let rest = rest.trim();
        if rest.is_empty() {
            return Ok(Instruction::Ret { value: None });
        }
        return Ok(Instruction::Ret {
            value: Some(parse_value(rest, line_no)?),
        });
    }

    if let Some(rest) = line.strip_prefix("call ") {
        let (function, args) = parse_call(rest, line_no)?;
        return Ok(Instruction::Call {
            dest: None,
            ty: None,
            function,
            args,
        });
    }

    if let Some(rest) = line.strip_prefix("blit ") {
        let parts: Vec<&str> = rest.split(',').map(|it| it.trim()).collect();
        if parts.len() != 3 {
            return Err(QbeSmtError::Parse {
                line: line_no,
                message: "expected `blit src, dst, len`".to_string(),
            });
        }
        let src = parse_value(parts[0], line_no)?;
        let dst = parse_value(parts[1], line_no)?;
        let len = parse_u64_literal(parts[2], line_no)?;
        return Ok(Instruction::Blit { src, dst, len });
    }

    if let Some((store_ty, rest)) = parse_store_head(line) {
        let parts: Vec<&str> = rest.split(',').map(|it| it.trim()).collect();
        if parts.len() != 2 {
            return Err(QbeSmtError::Parse {
                line: line_no,
                message: format!(
                    "expected `store{}` value, address",
                    store_type_suffix(store_ty)
                ),
            });
        }
        return Ok(Instruction::Store {
            store_ty,
            value: parse_value(parts[0], line_no)?,
            address: parse_value(parts[1], line_no)?,
        });
    }

    if line.starts_with("dbgfile ") || line.starts_with("dbgloc ") {
        return Ok(Instruction::Nop);
    }

    if line == "hlt" {
        return Ok(Instruction::Hlt);
    }

    Ok(Instruction::UnsupportedVolatile {
        _text: line.to_string(),
    })
}

fn parse_assignment(line_after_percent: &str, line_no: usize) -> Result<Instruction, QbeSmtError> {
    let (dest, rhs) = line_after_percent
        .split_once('=')
        .ok_or(QbeSmtError::Parse {
            line: line_no,
            message: "expected assignment in `%tmp =w op ...` form".to_string(),
        })?;
    let dest = dest.trim().to_string();
    if dest.is_empty() {
        return Err(QbeSmtError::Parse {
            line: line_no,
            message: "empty destination temporary".to_string(),
        });
    }

    let rhs = rhs.trim();
    if rhs.is_empty() {
        return Err(QbeSmtError::Parse {
            line: line_no,
            message: "missing assignment right-hand side".to_string(),
        });
    }

    let mut rhs_parts = rhs.splitn(2, char::is_whitespace);
    let first = rhs_parts.next().unwrap_or_default();
    let remainder = rhs_parts.next().unwrap_or_default().trim();

    let (ty, op_and_args) = if let Some(assign_ty) = parse_assign_type(first) {
        (assign_ty, remainder)
    } else {
        (AssignType::Long, rhs)
    };

    if op_and_args.is_empty() {
        return Err(QbeSmtError::Parse {
            line: line_no,
            message: "missing assignment operation".to_string(),
        });
    }

    if let Some(rest) = op_and_args.strip_prefix("copy ") {
        return Ok(Instruction::Copy {
            dest,
            ty,
            value: parse_value(rest.trim(), line_no)?,
        });
    }

    if let Some(rest) = op_and_args.strip_prefix("call ") {
        let (function, args) = parse_call(rest, line_no)?;
        return Ok(Instruction::Call {
            dest: Some(dest),
            ty: Some(ty),
            function,
            args,
        });
    }

    if let Some((load_ty, value_token)) = parse_load_op(op_and_args) {
        return Ok(Instruction::Load {
            dest,
            ty,
            load_ty,
            address: parse_value(value_token, line_no)?,
        });
    }

    if let Some((align, size_token)) = parse_alloc_op(op_and_args) {
        return Ok(Instruction::Alloc {
            dest,
            ty,
            align,
            size: parse_u64_literal(size_token, line_no)?,
        });
    }

    if let Some((unary, value_token)) = parse_unary_op(op_and_args) {
        return Ok(Instruction::Unary {
            dest,
            ty,
            op: unary,
            value: parse_value(value_token, line_no)?,
        });
    }

    if let Some((binary, rest)) = parse_binary_op(op_and_args) {
        let parts: Vec<&str> = rest.split(',').map(|it| it.trim()).collect();
        if parts.len() != 2 {
            return Err(QbeSmtError::Parse {
                line: line_no,
                message: format!("expected `{}` lhs, rhs", op_name(binary)),
            });
        }
        return Ok(Instruction::Binary {
            dest,
            ty,
            op: binary,
            lhs: parse_value(parts[0], line_no)?,
            rhs: parse_value(parts[1], line_no)?,
        });
    }

    let mut op_split = op_and_args.splitn(2, char::is_whitespace);
    let op = op_split.next().unwrap_or_default();
    let args = op_split.next().unwrap_or_default().trim();

    if let Some((kind, cmp_ty)) = parse_cmp_kind(op) {
        let parts: Vec<&str> = args.split(',').map(|it| it.trim()).collect();
        if parts.len() != 2 {
            return Err(QbeSmtError::Parse {
                line: line_no,
                message: format!("expected `{op} lhs, rhs`"),
            });
        }
        return Ok(Instruction::Cmp {
            dest,
            ty,
            kind,
            cmp_ty,
            lhs: parse_value(parts[0], line_no)?,
            rhs: parse_value(parts[1], line_no)?,
        });
    }

    if let Some(rest) = op_and_args.strip_prefix("phi ") {
        let (left, right) = rest.split_once(',').ok_or(QbeSmtError::Parse {
            line: line_no,
            message: "expected `phi @a v1, @b v2`".to_string(),
        })?;
        let (left_label, left_value_token) = parse_phi_side(left.trim(), line_no)?;
        let (right_label, right_value_token) = parse_phi_side(right.trim(), line_no)?;
        return Ok(Instruction::Phi {
            dest,
            ty,
            _left_label: left_label,
            _left_value: parse_value(left_value_token, line_no)?,
            _right_label: right_label,
            _right_value: parse_value(right_value_token, line_no)?,
        });
    }

    Ok(Instruction::UnsupportedAssign {
        dest,
        ty,
        _text: op_and_args.to_string(),
    })
}

fn parse_call(rest: &str, line_no: usize) -> Result<(String, Vec<Value>), QbeSmtError> {
    let rest = rest.trim();
    let open = rest.find('(').ok_or(QbeSmtError::Parse {
        line: line_no,
        message: "call must contain `(`".to_string(),
    })?;
    let close = rest.rfind(')').ok_or(QbeSmtError::Parse {
        line: line_no,
        message: "call must contain `)`".to_string(),
    })?;
    if close <= open {
        return Err(QbeSmtError::Parse {
            line: line_no,
            message: "malformed call argument list".to_string(),
        });
    }

    let fn_name = rest[..open].trim();
    let fn_name = fn_name
        .strip_prefix('$')
        .ok_or(QbeSmtError::Parse {
            line: line_no,
            message: format!("call target `{fn_name}` must be `$name`"),
        })?
        .trim();

    if fn_name.is_empty() {
        return Err(QbeSmtError::Parse {
            line: line_no,
            message: "empty call target".to_string(),
        });
    }

    let args_text = &rest[open + 1..close];
    let mut args = Vec::new();
    if !args_text.trim().is_empty() {
        for raw in args_text.split(',') {
            let raw = raw.trim();
            if raw.is_empty() || raw == "..." {
                continue;
            }

            if let Some((maybe_ty, value_token)) = split_once_whitespace(raw) {
                if QbeType::from_token(maybe_ty).is_some() {
                    args.push(parse_value(value_token.trim(), line_no)?);
                    continue;
                }
            }

            args.push(parse_value(raw, line_no)?);
        }
    }

    Ok((fn_name.to_string(), args))
}

fn parse_phi_side(side: &str, line_no: usize) -> Result<(String, &str), QbeSmtError> {
    let (label_token, value_token) = split_once_whitespace(side).ok_or(QbeSmtError::Parse {
        line: line_no,
        message: "expected `@label value` in phi arm".to_string(),
    })?;
    let label = label_token
        .trim()
        .strip_prefix('@')
        .ok_or(QbeSmtError::Parse {
            line: line_no,
            message: "phi arm label must start with `@`".to_string(),
        })?
        .trim();
    if label.is_empty() {
        return Err(QbeSmtError::Parse {
            line: line_no,
            message: "empty phi arm label".to_string(),
        });
    }
    Ok((label.to_string(), value_token.trim()))
}

fn parse_value(value: &str, line_no: usize) -> Result<Value, QbeSmtError> {
    let value = value.trim();
    if let Some(temp) = value.strip_prefix('%') {
        if temp.is_empty() {
            return Err(QbeSmtError::Parse {
                line: line_no,
                message: "empty temporary name".to_string(),
            });
        }
        return Ok(Value::Temp(temp.to_string()));
    }

    if let Some(global) = value.strip_prefix('$') {
        if global.is_empty() {
            return Err(QbeSmtError::Parse {
                line: line_no,
                message: "empty global name".to_string(),
            });
        }
        return Ok(Value::Global(global.to_string()));
    }

    Ok(Value::Const(parse_u64_literal(value, line_no)?))
}

fn parse_u64_literal(value: &str, line_no: usize) -> Result<u64, QbeSmtError> {
    let value = value.trim();

    if let Ok(parsed) = value.parse::<u64>() {
        return Ok(parsed);
    }

    if let Ok(parsed) = value.parse::<i64>() {
        return Ok(parsed as u64);
    }

    Err(QbeSmtError::Parse {
        line: line_no,
        message: format!("unsupported integer literal `{value}`"),
    })
}

fn parse_assign_type(token: &str) -> Option<AssignType> {
    let qbe_ty = QbeType::from_token(token)?;
    Some(qbe_ty.into_base_assign())
}

fn parse_store_head(line: &str) -> Option<(QbeType, &str)> {
    let mut split = line.splitn(2, char::is_whitespace);
    let head = split.next()?.trim();
    let rest = split.next().unwrap_or_default().trim();
    let ty_token = head.strip_prefix("store")?;
    let store_ty = QbeType::from_token(ty_token)?;
    Some((store_ty, rest))
}

fn parse_load_op(op_and_args: &str) -> Option<(QbeType, &str)> {
    let mut split = op_and_args.splitn(2, char::is_whitespace);
    let op = split.next()?.trim();
    let value = split.next().unwrap_or_default().trim();
    let ty_token = op.strip_prefix("load")?;
    let load_ty = QbeType::from_token(ty_token)?;
    Some((load_ty, value))
}

fn parse_alloc_op(op_and_args: &str) -> Option<(u32, &str)> {
    let mut split = op_and_args.splitn(2, char::is_whitespace);
    let op = split.next()?.trim();
    let size_token = split.next().unwrap_or_default().trim();
    match op {
        "alloc4" => Some((4, size_token)),
        "alloc8" => Some((8, size_token)),
        "alloc16" => Some((16, size_token)),
        _ => None,
    }
}

fn parse_unary_op(op_and_args: &str) -> Option<(UnaryOp, &str)> {
    let mut split = op_and_args.splitn(2, char::is_whitespace);
    let op = split.next()?.trim();
    let value = split.next().unwrap_or_default().trim();
    let unary = match op {
        "cast" => UnaryOp::Cast,
        "extsw" => UnaryOp::Extsw,
        "extuw" => UnaryOp::Extuw,
        "extsh" => UnaryOp::Extsh,
        "extuh" => UnaryOp::Extuh,
        "extsb" => UnaryOp::Extsb,
        "extub" => UnaryOp::Extub,
        "exts" => UnaryOp::Unsupported("exts"),
        "truncd" => UnaryOp::Unsupported("truncd"),
        "stosi" => UnaryOp::Unsupported("stosi"),
        "stoui" => UnaryOp::Unsupported("stoui"),
        "dtosi" => UnaryOp::Unsupported("dtosi"),
        "dtoui" => UnaryOp::Unsupported("dtoui"),
        "swtof" => UnaryOp::Unsupported("swtof"),
        "uwtof" => UnaryOp::Unsupported("uwtof"),
        "sltof" => UnaryOp::Unsupported("sltof"),
        "ultof" => UnaryOp::Unsupported("ultof"),
        "vastart" => UnaryOp::Unsupported("vastart"),
        _ => return None,
    };
    Some((unary, value))
}

fn parse_binary_op(op_and_args: &str) -> Option<(BinaryOp, &str)> {
    let mut split = op_and_args.splitn(2, char::is_whitespace);
    let op = split.next()?.trim();
    let rest = split.next().unwrap_or_default().trim();

    let parsed = match op {
        "add" => BinaryOp::Add,
        "sub" => BinaryOp::Sub,
        "mul" => BinaryOp::Mul,
        "div" => BinaryOp::Div,
        "udiv" => BinaryOp::Udiv,
        "rem" => BinaryOp::Rem,
        "urem" => BinaryOp::Urem,
        "and" => BinaryOp::And,
        "or" => BinaryOp::Or,
        "xor" => BinaryOp::Xor,
        "shl" => BinaryOp::Shl,
        "shr" => BinaryOp::Shr,
        "sar" => BinaryOp::Sar,
        _ => return None,
    };

    Some((parsed, rest))
}

fn parse_cmp_kind(op: &str) -> Option<(CmpKind, AssignType)> {
    if !op.starts_with('c') {
        return None;
    }

    let body = &op[1..];
    let (cmp_body, cmp_ty) = if let Some(prefix) = body.strip_suffix('w') {
        (prefix, AssignType::Word)
    } else if let Some(prefix) = body.strip_suffix('l') {
        (prefix, AssignType::Long)
    } else if let Some(prefix) = body.strip_suffix('s') {
        (prefix, AssignType::Single)
    } else if let Some(prefix) = body.strip_suffix('d') {
        (prefix, AssignType::Double)
    } else {
        return None;
    };

    let kind = match cmp_body {
        "eq" => CmpKind::Eq,
        "ne" => CmpKind::Ne,
        "slt" => CmpKind::Slt,
        "sle" => CmpKind::Sle,
        "sgt" => CmpKind::Sgt,
        "sge" => CmpKind::Sge,
        "ult" => CmpKind::Ult,
        "ule" => CmpKind::Ule,
        "ugt" => CmpKind::Ugt,
        "uge" => CmpKind::Uge,
        "o" => CmpKind::O,
        "uo" => CmpKind::Uo,
        _ => return None,
    };

    Some((kind, cmp_ty))
}

fn op_name(op: BinaryOp) -> &'static str {
    match op {
        BinaryOp::Add => "add",
        BinaryOp::Sub => "sub",
        BinaryOp::Mul => "mul",
        BinaryOp::Div => "div",
        BinaryOp::Udiv => "udiv",
        BinaryOp::Rem => "rem",
        BinaryOp::Urem => "urem",
        BinaryOp::And => "and",
        BinaryOp::Or => "or",
        BinaryOp::Xor => "xor",
        BinaryOp::Shl => "shl",
        BinaryOp::Shr => "shr",
        BinaryOp::Sar => "sar",
    }
}

fn store_type_suffix(ty: QbeType) -> &'static str {
    match ty {
        QbeType::Byte => "b",
        QbeType::SignedByte => "sb",
        QbeType::UnsignedByte => "ub",
        QbeType::Halfword => "h",
        QbeType::SignedHalfword => "sh",
        QbeType::UnsignedHalfword => "uh",
        QbeType::Word => "w",
        QbeType::Long => "l",
        QbeType::Single => "s",
        QbeType::Double => "d",
        QbeType::Aggregate => ":agg",
        QbeType::Zero => "z",
    }
}

fn split_once_whitespace(input: &str) -> Option<(&str, &str)> {
    let mut idx = None;
    for (i, ch) in input.char_indices() {
        if ch.is_whitespace() {
            idx = Some(i);
            break;
        }
    }
    let idx = idx?;
    let left = &input[..idx];
    let right = input[idx..].trim_start();
    if left.is_empty() || right.is_empty() {
        return None;
    }
    Some((left, right))
}

fn normalize_line(line: &str) -> String {
    line.split('#')
        .next()
        .unwrap_or_default()
        .trim()
        .to_string()
}

fn encode_function(function: &Function, options: &EncodeOptions) -> Result<String, QbeSmtError> {
    let mut flat = Vec::new();
    let mut label_to_pc = HashMap::<String, usize>::new();
    for block in &function.blocks {
        if label_to_pc.contains_key(&block.label) {
            return Err(QbeSmtError::DuplicateLabel {
                label: block.label.clone(),
            });
        }
        label_to_pc.insert(block.label.clone(), flat.len());
        for instruction in &block.instructions {
            flat.push(instruction.clone());
        }
    }

    if flat.is_empty() {
        return Err(QbeSmtError::EmptyFunction);
    }

    for arg in &function.args {
        if matches!(arg.ty, AssignType::Single | AssignType::Double) {
            return Err(QbeSmtError::Unsupported {
                message: format!(
                    "unsupported floating-point function argument `%{}` in CHC encoding",
                    arg.name
                ),
            });
        }
    }

    for (pc, instruction) in flat.iter().enumerate() {
        validate_instruction_supported(instruction, pc)?;
    }

    let mut regs = BTreeSet::<String>::new();
    for arg in &function.args {
        regs.insert(arg.name.clone());
    }
    for instruction in &flat {
        collect_regs(instruction, &mut regs);
    }

    let reg_list: Vec<String> = regs.into_iter().collect();
    let mut reg_slots = HashMap::<String, u32>::new();
    for (i, name) in reg_list.iter().enumerate() {
        reg_slots.insert(name.clone(), i as u32);
    }

    let mut globals = BTreeSet::<String>::new();
    for instruction in &flat {
        collect_globals(instruction, &mut globals);
    }
    for arg in &function.args {
        globals.remove(&arg.name);
    }

    let global_map = globals
        .iter()
        .enumerate()
        .map(|(idx, name)| {
            (
                name.clone(),
                GLOBAL_BASE.wrapping_add((idx as u64).wrapping_mul(GLOBAL_STRIDE)),
            )
        })
        .collect::<HashMap<_, _>>();

    let halt_relation = "halt_state";

    let mut smt = String::new();
    smt.push_str("(set-logic HORN)\n");
    smt.push_str("(set-option :fp.engine spacer)\n");
    smt.push_str("(set-info :source |qbe-smt chc fixedpoint model|)\n\n");

    for pc in 0..flat.len() {
        smt.push_str(&format!(
            "(declare-rel {} ({} {} {} {}))\n",
            pc_relation_name(pc),
            REG_STATE_SORT,
            MEM_STATE_SORT,
            BV64_SORT,
            BV64_SORT
        ));
    }
    smt.push_str(&format!(
        "(declare-rel {halt_relation} ({} {} {} {}))\n",
        REG_STATE_SORT, MEM_STATE_SORT, BV64_SORT, BV64_SORT
    ));
    smt.push_str("(declare-rel bad ())\n\n");

    smt.push_str(&format!("(declare-var regs {})\n", REG_STATE_SORT));
    smt.push_str(&format!("(declare-var mem {})\n", MEM_STATE_SORT));
    smt.push_str(&format!("(declare-var heap {})\n", BV64_SORT));
    smt.push_str(&format!("(declare-var exit {})\n", BV64_SORT));
    smt.push_str(&format!("(declare-var regs_next {})\n", REG_STATE_SORT));
    smt.push_str(&format!("(declare-var mem_next {})\n", MEM_STATE_SORT));
    smt.push_str(&format!("(declare-var heap_next {})\n", BV64_SORT));
    smt.push_str(&format!("(declare-var exit_next {})\n", BV64_SORT));
    smt.push('\n');

    let args: BTreeSet<&str> = function.args.iter().map(|arg| arg.name.as_str()).collect();
    let mut init_terms = vec![
        format!("(= exit {})", bv_const_u64(0, 64)),
        format!("(= heap {})", bv_const_u64(INITIAL_HEAP_BASE, 64)),
    ];
    for reg_name in &reg_list {
        if !args.contains(reg_name.as_str()) {
            let slot = *reg_slots.get(reg_name).expect("reg slot is present");
            init_terms.push(format!(
                "(= (select regs {}) {})",
                reg_slot_const(slot),
                bv_const_u64(0, 64)
            ));
        }
    }

    if options.assume_main_argc_non_negative {
        if let Some(first_arg) = function.args.first() {
            let slot = *reg_slots
                .get(&first_arg.name)
                .expect("first arg register exists");
            init_terms.push(format!(
                "(bvsge (select regs {}) {})",
                reg_slot_const(slot),
                bv_const_u64(0, 64)
            ));
        }
    }

    smt.push_str(&format!(
        "(rule (=> {} {}))\n\n",
        and_terms(init_terms),
        relation_app(&pc_relation_name(0), "regs", "mem", "heap", "exit")
    ));

    for (pc, instruction) in flat.iter().enumerate() {
        let from_rel = pc_relation_name(pc);

        let regs_next_expr =
            regs_update_expr(instruction, "regs", "mem", "heap", &reg_slots, &global_map);
        let mem_next_expr = memory_update_expr(instruction, "mem", "regs", &reg_slots, &global_map);
        let heap_next_expr = heap_update_expr(instruction, "heap", "regs", &reg_slots, &global_map);
        let exit_next_expr = exit_update_expr(instruction, "exit", "regs", &reg_slots, &global_map);

        let transition = TransitionExprs {
            regs_next: regs_next_expr,
            mem_next: mem_next_expr,
            heap_next: heap_next_expr,
            exit_next: exit_next_expr,
        };

        match instruction {
            Instruction::Jmp { target } => {
                let target_pc =
                    *label_to_pc
                        .get(target)
                        .ok_or_else(|| QbeSmtError::UnknownLabel {
                            label: target.clone(),
                        })?;
                emit_transition_rule(
                    &mut smt,
                    &from_rel,
                    &pc_relation_name(target_pc),
                    None,
                    &transition,
                );
            }
            Instruction::Jnz {
                cond,
                if_true,
                if_false,
            } => {
                let true_pc =
                    *label_to_pc
                        .get(if_true)
                        .ok_or_else(|| QbeSmtError::UnknownLabel {
                            label: if_true.clone(),
                        })?;
                let false_pc =
                    *label_to_pc
                        .get(if_false)
                        .ok_or_else(|| QbeSmtError::UnknownLabel {
                            label: if_false.clone(),
                        })?;

                let cond_expr = value_to_smt(cond, "regs", &reg_slots, &global_map);
                emit_transition_rule(
                    &mut smt,
                    &from_rel,
                    &pc_relation_name(true_pc),
                    Some(format!("(distinct {} {})", cond_expr, bv_const_u64(0, 64))),
                    &transition,
                );
                emit_transition_rule(
                    &mut smt,
                    &from_rel,
                    &pc_relation_name(false_pc),
                    Some(format!("(= {} {})", cond_expr, bv_const_u64(0, 64))),
                    &transition,
                );
            }
            Instruction::Ret { .. } | Instruction::Hlt => {
                emit_transition_rule(&mut smt, &from_rel, halt_relation, None, &transition);
            }
            _ => {
                if pc + 1 < flat.len() {
                    emit_transition_rule(
                        &mut smt,
                        &from_rel,
                        &pc_relation_name(pc + 1),
                        None,
                        &transition,
                    );
                } else {
                    emit_transition_rule(&mut smt, &from_rel, halt_relation, None, &transition);
                }
            }
        }
    }

    smt.push('\n');
    smt.push_str(&format!(
        "(rule (=> (and {} (= exit {})) bad))\n",
        relation_app(halt_relation, "regs", "mem", "heap", "exit"),
        bv_const_u64(1, 64)
    ));
    smt.push_str("(query bad)\n");

    Ok(smt)
}

const REG_STATE_SORT: &str = "(Array (_ BitVec 32) (_ BitVec 64))";
const MEM_STATE_SORT: &str = "(Array (_ BitVec 64) (_ BitVec 8))";
const BV64_SORT: &str = "(_ BitVec 64)";

struct TransitionExprs {
    regs_next: String,
    mem_next: String,
    heap_next: String,
    exit_next: String,
}

fn pc_relation_name(pc: usize) -> String {
    format!("pc_{}", pc)
}

fn relation_app(relation: &str, regs: &str, mem: &str, heap: &str, exit: &str) -> String {
    format!("({relation} {regs} {mem} {heap} {exit})")
}

fn and_terms(terms: Vec<String>) -> String {
    if terms.is_empty() {
        "true".to_string()
    } else if terms.len() == 1 {
        terms[0].clone()
    } else {
        format!("(and {})", terms.join(" "))
    }
}

fn emit_transition_rule(
    smt: &mut String,
    from_relation: &str,
    to_relation: &str,
    guard: Option<String>,
    next: &TransitionExprs,
) {
    let mut body_terms = vec![relation_app(from_relation, "regs", "mem", "heap", "exit")];
    if let Some(guard) = guard {
        body_terms.push(guard);
    }
    body_terms.push(format!("(= regs_next {})", next.regs_next));
    body_terms.push(format!("(= mem_next {})", next.mem_next));
    body_terms.push(format!("(= heap_next {})", next.heap_next));
    body_terms.push(format!("(= exit_next {})", next.exit_next));

    let body = and_terms(body_terms);
    let head = relation_app(
        to_relation,
        "regs_next",
        "mem_next",
        "heap_next",
        "exit_next",
    );

    smt.push_str(&format!("(rule (=> {body} {head}))\n"));
}

fn validate_instruction_supported(instruction: &Instruction, pc: usize) -> Result<(), QbeSmtError> {
    match instruction {
        Instruction::Binary { ty, .. } | Instruction::Copy { ty, .. } => {
            if matches!(ty, AssignType::Single | AssignType::Double) {
                return Err(QbeSmtError::Unsupported {
                    message: format!("pc {pc}: floating-point assignments are unsupported"),
                });
            }
        }
        Instruction::Cmp {
            ty, kind, cmp_ty, ..
        } => {
            if matches!(kind, CmpKind::O | CmpKind::Uo)
                || matches!(cmp_ty, AssignType::Single | AssignType::Double)
                || matches!(ty, AssignType::Single | AssignType::Double)
            {
                return Err(QbeSmtError::Unsupported {
                    message: format!("pc {pc}: unsupported compare operation"),
                });
            }
        }
        Instruction::Unary { ty, op, .. } => {
            if matches!(ty, AssignType::Single | AssignType::Double) {
                return Err(QbeSmtError::Unsupported {
                    message: format!("pc {pc}: floating-point unary assignments are unsupported"),
                });
            }
            if let UnaryOp::Unsupported(name) = op {
                return Err(QbeSmtError::Unsupported {
                    message: format!("pc {pc}: unsupported unary operation {name}"),
                });
            }
        }
        Instruction::Load { ty, load_ty, .. } => {
            if matches!(ty, AssignType::Single | AssignType::Double)
                || matches!(
                    load_ty,
                    QbeType::Single | QbeType::Double | QbeType::Aggregate
                )
            {
                return Err(QbeSmtError::Unsupported {
                    message: format!("pc {pc}: unsupported load operation"),
                });
            }
        }
        Instruction::Store { store_ty, .. } => {
            if store_ty.load_store_width_bits().is_none()
                || matches!(
                    store_ty,
                    QbeType::Aggregate | QbeType::Single | QbeType::Double
                )
            {
                return Err(QbeSmtError::Unsupported {
                    message: format!("pc {pc}: unsupported store operation"),
                });
            }
        }
        Instruction::Call { function, .. } => {
            if !is_malloc_call(function) {
                return Err(QbeSmtError::Unsupported {
                    message: format!("pc {pc}: unsupported call target ${function}"),
                });
            }
        }
        Instruction::Blit { len, .. } => {
            if *len > BLIT_INLINE_LIMIT {
                return Err(QbeSmtError::Unsupported {
                    message: format!(
                        "pc {pc}: blit len {len} exceeds inline limit {BLIT_INLINE_LIMIT}"
                    ),
                });
            }
        }
        Instruction::Phi { ty, .. } => {
            return Err(QbeSmtError::Unsupported {
                message: format!("pc {pc}: phi is unsupported for assignment type {:?}", ty),
            });
        }
        Instruction::UnsupportedAssign { ty, .. } => {
            return Err(QbeSmtError::Unsupported {
                message: format!(
                    "pc {pc}: unsupported assignment operation for assignment type {:?}",
                    ty
                ),
            });
        }
        Instruction::UnsupportedVolatile { .. } => {
            return Err(QbeSmtError::Unsupported {
                message: format!("pc {pc}: unsupported volatile/side-effect instruction"),
            });
        }
        Instruction::Alloc { .. }
        | Instruction::Nop
        | Instruction::Jnz { .. }
        | Instruction::Jmp { .. }
        | Instruction::Ret { .. }
        | Instruction::Hlt => {}
    }

    Ok(())
}

fn regs_update_expr(
    instruction: &Instruction,
    regs_curr: &str,
    mem_curr: &str,
    heap_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> String {
    let Some(dest) = instruction.dest() else {
        return regs_curr.to_string();
    };

    let slot = *reg_slots
        .get(dest)
        .expect("destination register slot is present");

    let value_expr = match instruction {
        Instruction::Binary {
            ty, op, lhs, rhs, ..
        } => {
            let lhs_expr = value_to_smt(lhs, regs_curr, reg_slots, global_map);
            let rhs_expr = value_to_smt(rhs, regs_curr, reg_slots, global_map);
            binary_expr(*op, *ty, &lhs_expr, &rhs_expr)
        }
        Instruction::Copy { ty, value, .. } => {
            let value_expr = value_to_smt(value, regs_curr, reg_slots, global_map);
            normalize_to_assign_type(&value_expr, *ty)
        }
        Instruction::Cmp {
            ty,
            kind,
            cmp_ty,
            lhs,
            rhs,
            ..
        } => {
            let pred = cmp_to_smt(*kind, *cmp_ty, lhs, rhs, regs_curr, reg_slots, global_map);
            normalize_to_assign_type(
                &format!(
                    "(ite {pred} {} {})",
                    bv_const_u64(1, 64),
                    bv_const_u64(0, 64)
                ),
                *ty,
            )
        }
        Instruction::Unary { ty, op, value, .. } => {
            let value_expr = value_to_smt(value, regs_curr, reg_slots, global_map);
            match op {
                UnaryOp::Cast => normalize_to_assign_type(&value_expr, *ty),
                UnaryOp::Extsw => sign_extend_from_expr(&value_expr, 32),
                UnaryOp::Extuw => zero_extend_from_expr(&value_expr, 32),
                UnaryOp::Extsh => sign_extend_from_expr(&value_expr, 16),
                UnaryOp::Extuh => zero_extend_from_expr(&value_expr, 16),
                UnaryOp::Extsb => sign_extend_from_expr(&value_expr, 8),
                UnaryOp::Extub => zero_extend_from_expr(&value_expr, 8),
                UnaryOp::Unsupported(_) => unreachable!("unsupported unary op should be rejected"),
            }
        }
        Instruction::Load {
            ty,
            load_ty,
            address,
            ..
        } => {
            let address_expr = value_to_smt(address, regs_curr, reg_slots, global_map);
            let loaded = load_memory_expr(mem_curr, &address_expr, *load_ty);
            normalize_to_assign_type(&loaded, *ty)
        }
        Instruction::Alloc { ty, .. } => normalize_to_assign_type(heap_curr, *ty),
        Instruction::Call {
            ty,
            function,
            args: _,
            ..
        } => {
            if is_malloc_call(function) {
                match ty {
                    Some(assign_ty) => normalize_to_assign_type(heap_curr, *assign_ty),
                    None => heap_curr.to_string(),
                }
            } else {
                unreachable!("unsupported calls should be rejected")
            }
        }
        Instruction::Phi { .. }
        | Instruction::UnsupportedAssign { .. }
        | Instruction::UnsupportedVolatile { .. } => {
            unreachable!("unsupported instruction should be rejected before transition generation")
        }
        _ => reg_read_expr(dest, regs_curr, reg_slots),
    };

    format!("(store {regs_curr} {} {value_expr})", reg_slot_const(slot))
}

fn memory_update_expr(
    instruction: &Instruction,
    mem_curr: &str,
    regs_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> String {
    match instruction {
        Instruction::Store {
            store_ty,
            value,
            address,
        } => {
            let width = store_ty
                .load_store_width_bits()
                .expect("unsupported store types should be rejected");
            let value_expr = value_to_smt(value, regs_curr, reg_slots, global_map);
            let address_expr = value_to_smt(address, regs_curr, reg_slots, global_map);
            store_memory_expr(mem_curr, &address_expr, &value_expr, width)
        }
        Instruction::Blit { src, dst, len } => {
            let src_expr = value_to_smt(src, regs_curr, reg_slots, global_map);
            let dst_expr = value_to_smt(dst, regs_curr, reg_slots, global_map);
            inline_blit_expr(mem_curr, &src_expr, &dst_expr, *len)
        }
        _ => mem_curr.to_string(),
    }
}

fn heap_update_expr(
    instruction: &Instruction,
    heap_curr: &str,
    regs_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> String {
    match instruction {
        Instruction::Alloc { size, align, .. } => {
            let align = *align as u64;
            let aligned_size = if *size == 0 {
                align.max(1)
            } else {
                let rem = *size % align.max(1);
                if rem == 0 {
                    *size
                } else {
                    *size + (align.max(1) - rem)
                }
            };
            format!("(bvadd {heap_curr} {})", bv_const_u64(aligned_size, 64))
        }
        Instruction::Call { function, args, .. } => {
            if is_malloc_call(function) {
                if let Some(size_arg) = args.first() {
                    let size_expr = value_to_smt(size_arg, regs_curr, reg_slots, global_map);
                    let non_zero_size = format!(
                        "(ite (= {size_expr} {}) {} {size_expr})",
                        bv_const_u64(0, 64),
                        bv_const_u64(1, 64)
                    );
                    return format!("(bvadd {heap_curr} {non_zero_size})");
                }
                return format!("(bvadd {heap_curr} {})", bv_const_u64(8, 64));
            }
            unreachable!("unsupported calls should be rejected")
        }
        _ => heap_curr.to_string(),
    }
}

fn exit_update_expr(
    instruction: &Instruction,
    exit_curr: &str,
    regs_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> String {
    match instruction {
        Instruction::Ret { value: Some(value) } => {
            value_to_smt(value, regs_curr, reg_slots, global_map)
        }
        Instruction::Ret { value: None } => bv_const_u64(0, 64),
        _ => exit_curr.to_string(),
    }
}

fn binary_expr(op: BinaryOp, ty: AssignType, lhs: &str, rhs: &str) -> String {
    let width = ty.bits();

    if width == 64 {
        match op {
            BinaryOp::Add => format!("(bvadd {lhs} {rhs})"),
            BinaryOp::Sub => format!("(bvsub {lhs} {rhs})"),
            BinaryOp::Mul => format!("(bvmul {lhs} {rhs})"),
            BinaryOp::Div => format!("(bvsdiv {lhs} {rhs})"),
            BinaryOp::Udiv => format!("(bvudiv {lhs} {rhs})"),
            BinaryOp::Rem => format!("(bvsrem {lhs} {rhs})"),
            BinaryOp::Urem => format!("(bvurem {lhs} {rhs})"),
            BinaryOp::And => format!("(bvand {lhs} {rhs})"),
            BinaryOp::Or => format!("(bvor {lhs} {rhs})"),
            BinaryOp::Xor => format!("(bvxor {lhs} {rhs})"),
            BinaryOp::Shl => format!("(bvshl {lhs} {rhs})"),
            BinaryOp::Shr => format!("(bvlshr {lhs} {rhs})"),
            BinaryOp::Sar => format!("(bvashr {lhs} {rhs})"),
        }
    } else {
        let lhs32 = extract_low_bits(lhs, 32);
        let rhs32 = extract_low_bits(rhs, 32);
        let expr32 = match op {
            BinaryOp::Add => format!("(bvadd {lhs32} {rhs32})"),
            BinaryOp::Sub => format!("(bvsub {lhs32} {rhs32})"),
            BinaryOp::Mul => format!("(bvmul {lhs32} {rhs32})"),
            BinaryOp::Div => format!("(bvsdiv {lhs32} {rhs32})"),
            BinaryOp::Udiv => format!("(bvudiv {lhs32} {rhs32})"),
            BinaryOp::Rem => format!("(bvsrem {lhs32} {rhs32})"),
            BinaryOp::Urem => format!("(bvurem {lhs32} {rhs32})"),
            BinaryOp::And => format!("(bvand {lhs32} {rhs32})"),
            BinaryOp::Or => format!("(bvor {lhs32} {rhs32})"),
            BinaryOp::Xor => format!("(bvxor {lhs32} {rhs32})"),
            BinaryOp::Shl => format!("(bvshl {lhs32} {rhs32})"),
            BinaryOp::Shr => format!("(bvlshr {lhs32} {rhs32})"),
            BinaryOp::Sar => format!("(bvashr {lhs32} {rhs32})"),
        };
        sign_extend_known_width(&expr32, 32, 64)
    }
}

fn cmp_to_smt(
    kind: CmpKind,
    cmp_ty: AssignType,
    lhs: &Value,
    rhs: &Value,
    regs_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> String {
    let lhs = value_to_smt(lhs, regs_curr, reg_slots, global_map);
    let rhs = value_to_smt(rhs, regs_curr, reg_slots, global_map);

    if cmp_ty.bits() == 32 {
        let lhs = extract_low_bits(&lhs, 32);
        let rhs = extract_low_bits(&rhs, 32);
        match kind {
            CmpKind::Eq => format!("(= {lhs} {rhs})"),
            CmpKind::Ne => format!("(distinct {lhs} {rhs})"),
            CmpKind::Slt => format!("(bvslt {lhs} {rhs})"),
            CmpKind::Sle => format!("(bvsle {lhs} {rhs})"),
            CmpKind::Sgt => format!("(bvsgt {lhs} {rhs})"),
            CmpKind::Sge => format!("(bvsge {lhs} {rhs})"),
            CmpKind::Ult => format!("(bvult {lhs} {rhs})"),
            CmpKind::Ule => format!("(bvule {lhs} {rhs})"),
            CmpKind::Ugt => format!("(bvugt {lhs} {rhs})"),
            CmpKind::Uge => format!("(bvuge {lhs} {rhs})"),
            CmpKind::O | CmpKind::Uo => unreachable!("unsupported compares should be rejected"),
        }
    } else {
        match kind {
            CmpKind::Eq => format!("(= {lhs} {rhs})"),
            CmpKind::Ne => format!("(distinct {lhs} {rhs})"),
            CmpKind::Slt => format!("(bvslt {lhs} {rhs})"),
            CmpKind::Sle => format!("(bvsle {lhs} {rhs})"),
            CmpKind::Sgt => format!("(bvsgt {lhs} {rhs})"),
            CmpKind::Sge => format!("(bvsge {lhs} {rhs})"),
            CmpKind::Ult => format!("(bvult {lhs} {rhs})"),
            CmpKind::Ule => format!("(bvule {lhs} {rhs})"),
            CmpKind::Ugt => format!("(bvugt {lhs} {rhs})"),
            CmpKind::Uge => format!("(bvuge {lhs} {rhs})"),
            CmpKind::O | CmpKind::Uo => unreachable!("unsupported compares should be rejected"),
        }
    }
}

fn load_memory_expr(mem_expr: &str, address_expr: &str, load_ty: QbeType) -> String {
    let width = load_ty
        .load_store_width_bits()
        .expect("unsupported load types should be rejected");

    let loaded = load_raw_bits(mem_expr, address_expr, width);
    match load_ty {
        QbeType::SignedByte => sign_extend_known_width(&loaded, 8, 64),
        QbeType::SignedHalfword => sign_extend_known_width(&loaded, 16, 64),
        QbeType::Word => sign_extend_known_width(&loaded, 32, 64),
        QbeType::Byte | QbeType::UnsignedByte | QbeType::Zero => {
            zero_extend_known_width(&loaded, 8, 64)
        }
        QbeType::Halfword | QbeType::UnsignedHalfword => zero_extend_known_width(&loaded, 16, 64),
        QbeType::Long => loaded,
        QbeType::Single | QbeType::Double | QbeType::Aggregate => {
            unreachable!("unsupported loads should be rejected")
        }
    }
}

fn load_raw_bits(mem_expr: &str, address_expr: &str, width_bits: u32) -> String {
    let bytes = width_bits / 8;
    if bytes == 1 {
        return format!("(select {mem_expr} {address_expr})");
    }

    let mut parts = Vec::new();
    for i in 0..bytes {
        let addr_i = format!("(bvadd {address_expr} {})", bv_const_u64(i as u64, 64));
        parts.push(format!("(select {mem_expr} {addr_i})"));
    }

    let mut iter = parts.into_iter().rev();
    let mut out = iter.next().unwrap_or_else(|| "(_ bv0 8)".to_string());
    for part in iter {
        out = format!("(concat {out} {part})");
    }
    out
}

fn store_memory_expr(
    mem_expr: &str,
    address_expr: &str,
    value_expr: &str,
    width_bits: u32,
) -> String {
    let bytes = width_bits / 8;
    let mut acc = mem_expr.to_string();

    for i in 0..bytes {
        let lo = i * 8;
        let hi = lo + 7;
        let byte_expr = if width_bits == 8 {
            extract_low_bits(value_expr, 8)
        } else {
            format!("((_ extract {hi} {lo}) {value_expr})")
        };
        let addr_i = format!("(bvadd {address_expr} {})", bv_const_u64(i as u64, 64));
        acc = format!("(store {acc} {addr_i} {byte_expr})");
    }

    acc
}

fn inline_blit_expr(mem_expr: &str, src_expr: &str, dst_expr: &str, len: u64) -> String {
    let mut acc = mem_expr.to_string();
    for i in 0..len {
        let src_i = format!("(bvadd {src_expr} {})", bv_const_u64(i, 64));
        let dst_i = format!("(bvadd {dst_expr} {})", bv_const_u64(i, 64));
        let byte_i = format!("(select {mem_expr} {src_i})");
        acc = format!("(store {acc} {dst_i} {byte_i})");
    }
    acc
}

fn normalize_to_assign_type(expr: &str, ty: AssignType) -> String {
    match ty {
        AssignType::Word => sign_extend_from_expr(expr, 32),
        AssignType::Long => expr.to_string(),
        AssignType::Single | AssignType::Double => {
            unreachable!("floating-point assignments should be rejected")
        }
    }
}

fn extract_low_bits(expr: &str, bits: u32) -> String {
    if bits == 64 {
        expr.to_string()
    } else {
        format!("((_ extract {} 0) {expr})", bits - 1)
    }
}

fn sign_extend_from_expr(expr64: &str, from_bits: u32) -> String {
    let low = extract_low_bits(expr64, from_bits);
    sign_extend_known_width(&low, from_bits, 64)
}

fn zero_extend_from_expr(expr64: &str, from_bits: u32) -> String {
    let low = extract_low_bits(expr64, from_bits);
    zero_extend_known_width(&low, from_bits, 64)
}

fn sign_extend_known_width(expr: &str, from_bits: u32, to_bits: u32) -> String {
    if from_bits == to_bits {
        expr.to_string()
    } else {
        format!("((_ sign_extend {}) {expr})", to_bits - from_bits)
    }
}

fn zero_extend_known_width(expr: &str, from_bits: u32, to_bits: u32) -> String {
    if from_bits == to_bits {
        expr.to_string()
    } else {
        format!("((_ zero_extend {}) {expr})", to_bits - from_bits)
    }
}

fn collect_regs(instruction: &Instruction, regs: &mut BTreeSet<String>) {
    if let Some(dest) = instruction.dest() {
        regs.insert(dest.to_string());
    }

    match instruction {
        Instruction::Binary { lhs, rhs, .. } => {
            collect_value_regs(lhs, regs);
            collect_value_regs(rhs, regs);
        }
        Instruction::Copy { value, .. }
        | Instruction::Unary { value, .. }
        | Instruction::Load { address: value, .. }
        | Instruction::Jnz { cond: value, .. }
        | Instruction::Ret {
            value: Some(value), ..
        } => collect_value_regs(value, regs),
        Instruction::Cmp { lhs, rhs, .. } => {
            collect_value_regs(lhs, regs);
            collect_value_regs(rhs, regs);
        }
        Instruction::Call { args, .. } => {
            for arg in args {
                collect_value_regs(arg, regs);
            }
        }
        Instruction::Store { value, address, .. } => {
            collect_value_regs(value, regs);
            collect_value_regs(address, regs);
        }
        Instruction::Blit { src, dst, .. } => {
            collect_value_regs(src, regs);
            collect_value_regs(dst, regs);
        }
        Instruction::Phi {
            _left_value,
            _right_value,
            ..
        } => {
            collect_value_regs(_left_value, regs);
            collect_value_regs(_right_value, regs);
        }
        _ => {}
    }
}

fn collect_globals(instruction: &Instruction, globals: &mut BTreeSet<String>) {
    match instruction {
        Instruction::Binary { lhs, rhs, .. } => {
            collect_value_globals(lhs, globals);
            collect_value_globals(rhs, globals);
        }
        Instruction::Copy { value, .. }
        | Instruction::Unary { value, .. }
        | Instruction::Load { address: value, .. }
        | Instruction::Jnz { cond: value, .. }
        | Instruction::Ret {
            value: Some(value), ..
        } => collect_value_globals(value, globals),
        Instruction::Cmp { lhs, rhs, .. } => {
            collect_value_globals(lhs, globals);
            collect_value_globals(rhs, globals);
        }
        Instruction::Call { args, .. } => {
            for arg in args {
                collect_value_globals(arg, globals);
            }
        }
        Instruction::Store { value, address, .. } => {
            collect_value_globals(value, globals);
            collect_value_globals(address, globals);
        }
        Instruction::Blit { src, dst, .. } => {
            collect_value_globals(src, globals);
            collect_value_globals(dst, globals);
        }
        Instruction::Phi {
            _left_value,
            _right_value,
            ..
        } => {
            collect_value_globals(_left_value, globals);
            collect_value_globals(_right_value, globals);
        }
        _ => {}
    }
}

fn collect_value_regs(value: &Value, regs: &mut BTreeSet<String>) {
    if let Value::Temp(name) = value {
        regs.insert(name.clone());
    }
}

fn collect_value_globals(value: &Value, globals: &mut BTreeSet<String>) {
    if let Value::Global(name) = value {
        globals.insert(name.clone());
    }
}

fn value_to_smt(
    value: &Value,
    regs_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> String {
    match value {
        Value::Temp(name) => reg_read_expr(name, regs_curr, reg_slots),
        Value::Global(name) => {
            let addr = *global_map.get(name).unwrap_or(&GLOBAL_BASE);
            bv_const_u64(addr, 64)
        }
        Value::Const(value) => bv_const_u64(*value, 64),
    }
}

fn reg_read_expr(name: &str, regs_curr: &str, reg_slots: &HashMap<String, u32>) -> String {
    let slot = *reg_slots.get(name).expect("register must be known");
    format!("(select {regs_curr} {})", reg_slot_const(slot))
}

fn reg_slot_const(slot: u32) -> String {
    format!("(_ bv{} 32)", slot)
}

fn bv_const_u64(value: u64, width: u32) -> String {
    if width == 64 {
        format!("(_ bv{} 64)", value)
    } else {
        let mask = if width == 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        };
        format!("(_ bv{} {})", value & mask, width)
    }
}

fn is_malloc_call(function: &str) -> bool {
    function == "malloc"
}

#[cfg(test)]
mod tests {
    use super::{qbe_to_smt, EncodeOptions};

    #[test]
    fn emits_horn_script_with_bad_query() {
        let qbe = r#"
            export function w $main(w %x) {
                @start
                    %y =w add %x, 1
                    ret %y
            }
        "#;

        let smt = qbe_to_smt(
            qbe,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(set-logic HORN)"));
        assert!(smt.contains("(set-option :fp.engine spacer)"));
        assert!(smt.contains("(declare-rel pc_0"));
        assert!(smt.contains("(declare-rel halt_state"));
        assert!(smt.contains("(declare-rel bad ())"));
        assert!(smt.contains("(query bad)"));
        assert!(smt.contains("(= exit (_ bv1 64))"));
    }

    #[test]
    fn emits_branch_rules_for_jnz() {
        let qbe = r#"
            function w $main(w %x) {
                @entry
                    jnz %x, @then, @else
                @then
                    ret 1
                @else
                    ret 0
            }
        "#;

        let smt = qbe_to_smt(
            qbe,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(distinct (select regs (_ bv0 32)) (_ bv0 64))"));
        assert!(smt.contains("(pc_1 regs_next mem_next heap_next exit_next)"));
        assert!(smt.contains("(pc_2 regs_next mem_next heap_next exit_next)"));
    }

    #[test]
    fn emits_recursive_rule_for_loop_backedge() {
        let qbe = r#"
            function w $main(w %x) {
                @entry
                    jmp @loop
                @loop
                    %x =w sub %x, 1
                    jnz %x, @loop, @done
                @done
                    ret 0
            }
        "#;

        let smt = qbe_to_smt(
            qbe,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(pc_2 regs mem heap exit)"));
        assert!(smt.contains("(pc_1 regs_next mem_next heap_next exit_next)"));
    }

    #[test]
    fn models_alloc_store_and_load() {
        let qbe = r#"
            function w $main(w %x) {
                @entry
                    %p =l alloc8 8
                    storew %x, %p
                    %y =w loadw %p
                    ret %y
            }
        "#;

        let smt = qbe_to_smt(
            qbe,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(store mem"));
        assert!(smt.contains("(select mem"));
        assert!(smt.contains("(bvadd heap"));
    }

    #[test]
    fn emits_non_negative_argc_constraint_when_enabled() {
        let qbe = r#"
            function w $main(w %argc, l %argv) {
                @entry
                    ret %argc
            }
        "#;

        let smt = qbe_to_smt(
            qbe,
            &EncodeOptions {
                assume_main_argc_non_negative: true,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(bvsge (select regs (_ bv0 32)) (_ bv0 64))"));
    }

    #[test]
    fn rejects_missing_labels() {
        let qbe = r#"
            function w $main(w %x) {
                @entry
                    jmp @missing
            }
        "#;

        let err = qbe_to_smt(
            qbe,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
            },
        )
        .expect_err("should fail");
        assert!(err.to_string().contains("unknown label @missing"));
    }

    #[test]
    fn rejects_unsupported_calls() {
        let qbe = r#"
            function w $main(w %x) {
                @entry
                    %y =w call $foo(w %x)
                    ret %y
            }
        "#;

        let err = qbe_to_smt(
            qbe,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
            },
        )
        .expect_err("unsupported call should fail");
        assert!(err.to_string().contains("unsupported call target $foo"));
    }

    #[test]
    fn rejects_unknown_assignment_operations() {
        let qbe = r#"
            function w $main() {
                @entry
                    %x =w totally_unknown 2, 3
                    ret %x
            }
        "#;

        let err = qbe_to_smt(
            qbe,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
            },
        )
        .expect_err("unsupported op should fail");

        assert!(err.to_string().contains("unsupported assignment operation"));
    }
}
