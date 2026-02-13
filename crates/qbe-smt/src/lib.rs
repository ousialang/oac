use std::collections::{BTreeSet, HashMap};

use thiserror::Error;

/// Options for bounded QBE-to-SMT encoding.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct EncodeOptions {
    /// Number of transition steps to unroll.
    pub max_steps: usize,
    /// Emit `(get-model)` after `(check-sat)`.
    pub emit_model: bool,
}

impl Default for EncodeOptions {
    fn default() -> Self {
        Self {
            max_steps: 16,
            emit_model: false,
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
}

/// Encode a thin subset of QBE source into SMT-LIB text.
///
/// Current supported subset:
/// - single `function` definition
/// - block labels (`@label`)
/// - `%tmp =w add lhs, rhs`
/// - `%tmp =w copy value`
/// - `jnz cond, @true, @false`
/// - `jmp @target`
/// - `ret` / `ret value`
pub fn qbe_to_smt(source: &str, options: &EncodeOptions) -> Result<String, QbeSmtError> {
    let function = parse_function(source)?;
    encode_function(&function, options)
}

#[derive(Debug, Clone)]
struct Function {
    args: Vec<String>,
    blocks: Vec<Block>,
}

#[derive(Debug, Clone)]
struct Block {
    label: String,
    instructions: Vec<Instruction>,
}

#[derive(Debug, Clone)]
enum Instruction {
    Add {
        dest: String,
        lhs: Value,
        rhs: Value,
    },
    Copy {
        dest: String,
        value: Value,
    },
    Cmp {
        dest: String,
        kind: CmpKind,
        lhs: Value,
        rhs: Value,
    },
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
}

#[derive(Debug, Clone)]
enum Value {
    Temp(String),
    Const(i64),
}

#[derive(Debug, Clone, Copy)]
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
}

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

fn parse_function_header(line: &str, line_no: usize) -> Result<(Vec<String>, bool), QbeSmtError> {
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
            let arg_trimmed = arg.trim();
            let percent = arg_trimmed.rfind('%').ok_or(QbeSmtError::Parse {
                line: line_no,
                message: format!("argument `{arg_trimmed}` must contain a temporary name"),
            })?;
            args.push(arg_trimmed[percent + 1..].trim().to_string());
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

    Err(QbeSmtError::Parse {
        line: line_no,
        message: format!("unsupported instruction `{line}`"),
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
    let mut rhs_parts = rhs.splitn(2, char::is_whitespace);
    let first = rhs_parts.next().unwrap_or_default();
    let remainder = rhs_parts.next().unwrap_or_default().trim();
    let op_and_args = if is_qbe_type_token(first) {
        remainder
    } else {
        rhs
    };

    if let Some(rest) = op_and_args.strip_prefix("add ") {
        let parts: Vec<&str> = rest.split(',').map(|it| it.trim()).collect();
        if parts.len() != 2 {
            return Err(QbeSmtError::Parse {
                line: line_no,
                message: "expected `add lhs, rhs`".to_string(),
            });
        }
        return Ok(Instruction::Add {
            dest,
            lhs: parse_value(parts[0], line_no)?,
            rhs: parse_value(parts[1], line_no)?,
        });
    }

    if let Some(rest) = op_and_args.strip_prefix("copy ") {
        return Ok(Instruction::Copy {
            dest,
            value: parse_value(rest.trim(), line_no)?,
        });
    }

    let mut op_split = op_and_args.splitn(2, char::is_whitespace);
    let op = op_split.next().unwrap_or_default();
    let args = op_split.next().unwrap_or_default().trim();
    if let Some(kind) = parse_cmp_kind(op) {
        let parts: Vec<&str> = args.split(',').map(|it| it.trim()).collect();
        if parts.len() != 2 {
            return Err(QbeSmtError::Parse {
                line: line_no,
                message: format!("expected `{op} lhs, rhs`"),
            });
        }
        return Ok(Instruction::Cmp {
            dest,
            kind,
            lhs: parse_value(parts[0], line_no)?,
            rhs: parse_value(parts[1], line_no)?,
        });
    }

    Err(QbeSmtError::Parse {
        line: line_no,
        message: format!("unsupported assignment op in `{line_after_percent}`"),
    })
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

    let parsed = value.parse::<i64>().map_err(|_| QbeSmtError::Parse {
        line: line_no,
        message: format!("unsupported value `{value}`; expected `%tmp` or integer constant"),
    })?;
    Ok(Value::Const(parsed))
}

fn is_qbe_type_token(token: &str) -> bool {
    matches!(
        token,
        "w" | "l" | "b" | "h" | "s" | "d" | "ub" | "sb" | "uh" | "sh"
    )
}

fn parse_cmp_kind(op: &str) -> Option<CmpKind> {
    if !op.starts_with('c') {
        return None;
    }

    // QBE compare op format: c{cmp}{type}, for example `ceqw` / `csltw`.
    let body = &op[1..];
    let cmp = if let Some(prefix) = body.strip_suffix('w') {
        prefix
    } else if let Some(prefix) = body.strip_suffix('l') {
        prefix
    } else if let Some(prefix) = body.strip_suffix('s') {
        prefix
    } else if let Some(prefix) = body.strip_suffix('d') {
        prefix
    } else {
        body
    };

    match cmp {
        "eq" => Some(CmpKind::Eq),
        "ne" => Some(CmpKind::Ne),
        "slt" => Some(CmpKind::Slt),
        "sle" => Some(CmpKind::Sle),
        "sgt" => Some(CmpKind::Sgt),
        "sge" => Some(CmpKind::Sge),
        "ult" => Some(CmpKind::Ult),
        "ule" => Some(CmpKind::Ule),
        "ugt" => Some(CmpKind::Ugt),
        "uge" => Some(CmpKind::Uge),
        _ => None,
    }
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

    let halt_pc = flat.len();
    let mut regs = BTreeSet::<String>::new();
    for arg in &function.args {
        regs.insert(arg.clone());
    }
    for instruction in &flat {
        collect_regs(instruction, &mut regs);
    }

    let reg_list: Vec<String> = regs.into_iter().collect();
    let mut reg_ids = HashMap::<String, String>::new();
    for (i, name) in reg_list.iter().enumerate() {
        reg_ids.insert(name.clone(), format!("r{}_{}", i, sanitize(name)));
    }

    let mut smt = String::new();
    smt.push_str("(set-logic QF_BV)\n");
    smt.push_str("(set-info :source |qbe-smt thin slice|)\n\n");

    for step in 0..=options.max_steps {
        smt.push_str(&format!("(declare-fun pc_{} () (_ BitVec 32))\n", step));
        for name in &reg_list {
            let reg_id = reg_ids.get(name).expect("reg id is present");
            smt.push_str(&format!(
                "(declare-fun {}_{} () (_ BitVec 64))\n",
                reg_id, step
            ));
        }
    }
    smt.push('\n');

    for step in 0..=options.max_steps {
        let mut pcs = Vec::new();
        for pc in 0..=halt_pc {
            pcs.push(format!("(= pc_{} {})", step, pc_const(pc as u64)));
        }
        smt.push_str(&format!("(assert (or {}))\n", pcs.join(" ")));
    }
    smt.push('\n');

    smt.push_str(&format!("(assert (= pc_0 {}))\n", pc_const(0)));
    let args: BTreeSet<&str> = function.args.iter().map(String::as_str).collect();
    for reg_name in &reg_list {
        if !args.contains(reg_name.as_str()) {
            let reg_id = reg_ids.get(reg_name).expect("reg id is present");
            smt.push_str(&format!("(assert (= {}_0 {}))\n", reg_id, bv_const(0, 64)));
        }
    }
    smt.push('\n');

    for step in 0..options.max_steps {
        for (pc, instruction) in flat.iter().enumerate() {
            let guard = format!("(= pc_{} {})", step, pc_const(pc as u64));
            let next_pc = match instruction {
                Instruction::Add { .. } | Instruction::Copy { .. } | Instruction::Cmp { .. } => {
                    if pc + 1 < flat.len() {
                        pc_const((pc + 1) as u64)
                    } else {
                        pc_const(halt_pc as u64)
                    }
                }
                Instruction::Jmp { target } => {
                    let target_pc =
                        *label_to_pc
                            .get(target)
                            .ok_or_else(|| QbeSmtError::UnknownLabel {
                                label: target.clone(),
                            })?;
                    pc_const(target_pc as u64)
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
                    format!(
                        "(ite (distinct {} {}) {} {})",
                        value_to_smt(cond, step, &reg_ids),
                        bv_const(0, 64),
                        pc_const(true_pc as u64),
                        pc_const(false_pc as u64)
                    )
                }
                Instruction::Ret { .. } => pc_const(halt_pc as u64),
            };

            smt.push_str(&format!(
                "(assert (=> {} (= pc_{} {})))\n",
                guard,
                step + 1,
                next_pc
            ));

            for reg_name in &reg_list {
                let reg_id = reg_ids.get(reg_name).expect("reg id is present");
                let reg_next = format!("{}_{}", reg_id, step + 1);
                let reg_curr = format!("{}_{}", reg_id, step);
                let reg_expr = match instruction {
                    Instruction::Add { dest, lhs, rhs } if dest == reg_name => format!(
                        "(bvadd {} {})",
                        value_to_smt(lhs, step, &reg_ids),
                        value_to_smt(rhs, step, &reg_ids)
                    ),
                    Instruction::Copy { dest, value } if dest == reg_name => {
                        value_to_smt(value, step, &reg_ids)
                    }
                    Instruction::Cmp {
                        dest,
                        kind,
                        lhs,
                        rhs,
                    } if dest == reg_name => {
                        let pred = cmp_to_smt(*kind, lhs, rhs, step, &reg_ids);
                        format!("(ite {pred} {} {})", bv_const(1, 64), bv_const(0, 64))
                    }
                    _ => reg_curr,
                };
                smt.push_str(&format!(
                    "(assert (=> {} (= {} {})))\n",
                    guard, reg_next, reg_expr
                ));
            }
        }

        let halt_guard = format!("(= pc_{} {})", step, pc_const(halt_pc as u64));
        smt.push_str(&format!(
            "(assert (=> {} (= pc_{} {})))\n",
            halt_guard,
            step + 1,
            pc_const(halt_pc as u64)
        ));
        for reg_name in &reg_list {
            let reg_id = reg_ids.get(reg_name).expect("reg id is present");
            smt.push_str(&format!(
                "(assert (=> {} (= {}_{} {}_{})))\n",
                halt_guard,
                reg_id,
                step + 1,
                reg_id,
                step
            ));
        }
        smt.push('\n');
    }

    let mut reached_halt = Vec::new();
    for step in 0..=options.max_steps {
        reached_halt.push(format!("(= pc_{} {})", step, pc_const(halt_pc as u64)));
    }
    smt.push_str(&format!("(assert (or {}))\n", reached_halt.join(" ")));
    smt.push_str("(check-sat)\n");
    if options.emit_model {
        smt.push_str("(get-model)\n");
    }

    Ok(smt)
}

fn collect_regs(instruction: &Instruction, regs: &mut BTreeSet<String>) {
    match instruction {
        Instruction::Add { dest, lhs, rhs } => {
            regs.insert(dest.clone());
            collect_value_regs(lhs, regs);
            collect_value_regs(rhs, regs);
        }
        Instruction::Copy { dest, value } => {
            regs.insert(dest.clone());
            collect_value_regs(value, regs);
        }
        Instruction::Cmp { dest, lhs, rhs, .. } => {
            regs.insert(dest.clone());
            collect_value_regs(lhs, regs);
            collect_value_regs(rhs, regs);
        }
        Instruction::Jnz { cond, .. } => collect_value_regs(cond, regs),
        Instruction::Jmp { .. } => {}
        Instruction::Ret { value } => {
            if let Some(value) = value {
                collect_value_regs(value, regs);
            }
        }
    }
}

fn collect_value_regs(value: &Value, regs: &mut BTreeSet<String>) {
    if let Value::Temp(name) = value {
        regs.insert(name.clone());
    }
}

fn sanitize(name: &str) -> String {
    let mut out = String::new();
    for (idx, ch) in name.chars().enumerate() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            if idx == 0 && ch.is_ascii_digit() {
                out.push('_');
            }
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() {
        "_tmp".to_string()
    } else {
        out
    }
}

fn value_to_smt(value: &Value, step: usize, reg_ids: &HashMap<String, String>) -> String {
    match value {
        Value::Temp(name) => {
            let reg_id = reg_ids.get(name).expect("register must be known");
            format!("{}_{}", reg_id, step)
        }
        Value::Const(value) => bv_const(*value, 64),
    }
}

fn cmp_to_smt(
    kind: CmpKind,
    lhs: &Value,
    rhs: &Value,
    step: usize,
    reg_ids: &HashMap<String, String>,
) -> String {
    let lhs = value_to_smt(lhs, step, reg_ids);
    let rhs = value_to_smt(rhs, step, reg_ids);

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
    }
}

fn pc_const(value: u64) -> String {
    format!("(_ bv{} 32)", value)
}

fn bv_const(value: i64, width: u32) -> String {
    let modulus = 1u128 << width;
    let wrapped = if value >= 0 {
        (value as u128) % modulus
    } else {
        let magnitude = ((-value) as u128) % modulus;
        if magnitude == 0 {
            0
        } else {
            modulus - magnitude
        }
    };
    format!("(_ bv{} {})", wrapped, width)
}

#[cfg(test)]
mod tests {
    use super::{qbe_to_smt, EncodeOptions};

    #[test]
    fn emits_smt_for_add_and_ret() {
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
                max_steps: 2,
                emit_model: false,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(set-logic QF_BV)"));
        assert!(smt.contains("(declare-fun pc_0 () (_ BitVec 32))"));
        assert!(smt.contains("(assert (= pc_0 (_ bv0 32)))"));
        assert!(smt.contains("(bvadd r0_x_0 (_ bv1 64))"));
        assert!(smt.contains("(assert (=> (= pc_1 (_ bv1 32)) (= pc_2 (_ bv2 32))))"));
        assert!(smt.contains("(check-sat)"));
    }

    #[test]
    fn emits_ite_for_jnz() {
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
                max_steps: 2,
                emit_model: false,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(ite (distinct r0_x_0 (_ bv0 64)) (_ bv1 32) (_ bv2 32))"));
    }

    #[test]
    fn rejects_unsupported_instruction() {
        let qbe = r#"
            function w $main() {
                @entry
                    %x =w mul 2, 3
                    ret %x
            }
        "#;

        let err = qbe_to_smt(
            qbe,
            &EncodeOptions {
                max_steps: 2,
                emit_model: false,
            },
        )
        .expect_err("should fail");
        assert!(err.to_string().contains("unsupported assignment op"));
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
                max_steps: 2,
                emit_model: false,
            },
        )
        .expect_err("should fail");
        assert!(err.to_string().contains("unknown label @missing"));
    }

    #[test]
    fn emits_cmp_assignment() {
        let qbe = r#"
            function w $main(w %x) {
                @entry
                    %c =w csltw %x, 5
                    ret %c
            }
        "#;

        let smt = qbe_to_smt(
            qbe,
            &EncodeOptions {
                max_steps: 2,
                emit_model: false,
            },
        )
        .expect("encodes");
        assert!(smt.contains("(ite (bvslt "));
        assert!(smt.contains("(_ bv5 64)) (_ bv1 64) (_ bv0 64))"));
    }
}
