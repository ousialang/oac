use std::collections::{BTreeSet, HashMap};

use qbe::{
    Block, BlockItem, Cmp as QbeCmp, Function as QbeFunction, Instr as QbeInstr,
    Statement as QbeStatement, Type as QbeType, Value as QbeValue,
};

use crate::QbeSmtError;

/// High-level loop classification result.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LoopProof {
    pub header_label: String,
    pub status: LoopProofStatus,
    pub reason: String,
}

/// Status of a loop termination proof attempt.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum LoopProofStatus {
    /// A non-terminating execution has been proven for the loop.
    NonTerminating,
    /// The current prover could not classify the loop.
    Unknown,
}

#[derive(Debug, Clone)]
struct LoopGuard {
    var: String,
    kind: QbeCmp,
    bits: u32,
    constant: u64,
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum IdentityExpr {
    Var,
    Const(u64),
    Unknown,
}

pub(crate) fn classify_simple_loops_in_function(
    function: &QbeFunction,
) -> Result<Vec<LoopProof>, QbeSmtError> {
    validate_function(function)?;

    let mut by_label = HashMap::<String, &Block>::new();
    for block in &function.blocks {
        by_label.insert(block.label.clone(), block);
    }

    let predecessors = build_block_predecessors(function);
    let mut proofs = Vec::new();

    for header in &function.blocks {
        let Some(QbeInstr::Jnz(cond, if_true, _if_false)) = block_terminator_instr(header) else {
            continue;
        };

        let Some(body) = by_label.get(if_true) else {
            continue;
        };

        let Some(QbeInstr::Jmp(target)) = block_terminator_instr(body) else {
            continue;
        };
        if target != &header.label {
            continue;
        }

        let guard = match extract_loop_guard(header, cond) {
            Some(guard) => guard,
            None => {
                proofs.push(LoopProof {
                    header_label: header.label.clone(),
                    status: LoopProofStatus::Unknown,
                    reason: "unsupported loop guard (expected a compare temporary used by jnz)"
                        .to_string(),
                });
                continue;
            }
        };

        if !body_preserves_guard_var(body, &guard.var) {
            proofs.push(LoopProof {
                header_label: header.label.clone(),
                status: LoopProofStatus::Unknown,
                reason: format!(
                    "loop body update for `%{}` is not proven as identity",
                    guard.var
                ),
            });
            continue;
        }

        let mut entry_has_guard_true = false;
        for predecessor_label in predecessors
            .get(&header.label)
            .into_iter()
            .flatten()
            .filter(|label| *label != &body.label)
        {
            let Some(predecessor) = by_label.get(predecessor_label) else {
                continue;
            };
            let Some(entry_value) = block_exit_constant_for_var(predecessor, &guard.var) else {
                continue;
            };
            if eval_guard_with_const(&guard, entry_value).unwrap_or(false) {
                entry_has_guard_true = true;
                break;
            }
        }

        if entry_has_guard_true {
            proofs.push(LoopProof {
                header_label: header.label.clone(),
                status: LoopProofStatus::NonTerminating,
                reason: format!(
                    "guard over `%{}` is initially true and body preserves it (`x' = x`)",
                    guard.var
                ),
            });
        } else {
            proofs.push(LoopProof {
                header_label: header.label.clone(),
                status: LoopProofStatus::Unknown,
                reason: format!(
                    "no predecessor to `@{}` establishes a constant `%{}` satisfying the guard",
                    header.label, guard.var
                ),
            });
        }
    }

    Ok(proofs)
}

fn validate_function(function: &QbeFunction) -> Result<(), QbeSmtError> {
    let mut labels = BTreeSet::new();
    let mut saw_statement = false;

    for block in &function.blocks {
        if !labels.insert(block.label.clone()) {
            return Err(QbeSmtError::DuplicateLabel {
                label: block.label.clone(),
            });
        }

        for item in &block.items {
            if let BlockItem::Statement(statement) = item {
                saw_statement = true;
                validate_statement(statement)?;
            }
        }
    }

    if !saw_statement {
        return Err(QbeSmtError::EmptyFunction);
    }

    Ok(())
}

fn validate_statement(statement: &QbeStatement) -> Result<(), QbeSmtError> {
    if let QbeStatement::Assign(dest, _, _) = statement {
        if !matches!(dest, QbeValue::Temporary(_)) {
            return Err(QbeSmtError::Unsupported {
                message: format!(
                    "loop classification requires temporary assignment destinations, got `{dest}`"
                ),
            });
        }
    }
    Ok(())
}

fn block_statements(block: &Block) -> Vec<&QbeStatement> {
    block
        .items
        .iter()
        .filter_map(|item| match item {
            BlockItem::Statement(statement) => Some(statement),
            BlockItem::Comment(_) => None,
        })
        .collect()
}

fn block_terminator_instr(block: &Block) -> Option<&QbeInstr> {
    let statements = block_statements(block);
    match statements.last() {
        Some(QbeStatement::Assign(_, _, instr)) | Some(QbeStatement::Volatile(instr)) => {
            Some(instr)
        }
        None => None,
    }
}

fn build_block_predecessors(function: &QbeFunction) -> HashMap<String, Vec<String>> {
    let mut predecessors = HashMap::<String, BTreeSet<String>>::new();
    for block in &function.blocks {
        predecessors.entry(block.label.clone()).or_default();
    }

    for (index, block) in function.blocks.iter().enumerate() {
        let mut successors = BTreeSet::new();
        match block_terminator_instr(block) {
            Some(QbeInstr::Jmp(target)) => {
                successors.insert(target.clone());
            }
            Some(QbeInstr::Jnz(_, if_true, if_false)) => {
                successors.insert(if_true.clone());
                successors.insert(if_false.clone());
            }
            Some(QbeInstr::Ret(_)) | Some(QbeInstr::Hlt) => {}
            _ => {
                if let Some(next_block) = function.blocks.get(index + 1) {
                    successors.insert(next_block.label.clone());
                }
            }
        }

        for successor in successors {
            predecessors
                .entry(successor)
                .or_default()
                .insert(block.label.clone());
        }
    }

    predecessors
        .into_iter()
        .map(|(label, preds)| (label, preds.into_iter().collect()))
        .collect()
}

fn extract_loop_guard(header: &Block, cond: &QbeValue) -> Option<LoopGuard> {
    let QbeValue::Temporary(cond_temp) = cond else {
        return None;
    };

    let mut visited = BTreeSet::<String>::new();
    extract_loop_guard_from_temp(header, cond_temp, &mut visited)
}

fn extract_loop_guard_from_temp(
    header: &Block,
    temp: &str,
    visited: &mut BTreeSet<String>,
) -> Option<LoopGuard> {
    if !visited.insert(temp.to_string()) {
        return None;
    }

    let (def_ty, def_instr) = find_temp_definition_in_block(header, temp)?;
    match def_instr {
        QbeInstr::Cmp(cmp_ty, kind, lhs, rhs) => {
            let bits = assign_bits_from_type(cmp_ty)?;
            guard_from_cmp(header, *kind, bits, lhs, rhs)
        }
        QbeInstr::Copy(QbeValue::Temporary(next_temp)) => {
            extract_loop_guard_from_temp(header, next_temp, visited)
        }
        _ => {
            let _ = def_ty; // keep intent explicit for now
            None
        }
    }
}

fn find_temp_definition_in_block<'a>(
    block: &'a Block,
    temp: &str,
) -> Option<(&'a QbeType, &'a QbeInstr)> {
    let statements = block_statements(block);
    let body_end = statements.len().saturating_sub(1);

    statements
        .iter()
        .take(body_end)
        .rev()
        .find_map(|statement| match statement {
            QbeStatement::Assign(QbeValue::Temporary(name), ty, instr) if name == temp => {
                Some((ty, instr))
            }
            _ => None,
        })
}

fn guard_from_cmp(
    header: &Block,
    kind: QbeCmp,
    bits: u32,
    lhs: &QbeValue,
    rhs: &QbeValue,
) -> Option<LoopGuard> {
    let mut visited = BTreeSet::<String>::new();
    let lhs = resolve_guard_operand(header, lhs, &mut visited)?;
    let rhs = resolve_guard_operand(header, rhs, &mut visited)?;

    match (lhs, rhs) {
        (GuardOperand::Var(var), GuardOperand::Const(constant)) => Some(LoopGuard {
            var,
            kind,
            bits,
            constant,
        }),
        (GuardOperand::Const(constant), GuardOperand::Var(var)) => Some(LoopGuard {
            var,
            kind: invert_cmp_operands(kind)?,
            bits,
            constant,
        }),
        _ => None,
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum GuardOperand {
    Var(String),
    Const(u64),
}

fn resolve_guard_operand(
    header: &Block,
    value: &QbeValue,
    visited: &mut BTreeSet<String>,
) -> Option<GuardOperand> {
    match value {
        QbeValue::Const(value) => Some(GuardOperand::Const(*value)),
        QbeValue::SingleConst(_) => None,
        QbeValue::DoubleConst(_) => None,
        QbeValue::Global(_) => None,
        QbeValue::Temporary(name) => {
            if !visited.insert(name.clone()) {
                return None;
            }

            let Some((_ty, def)) = find_temp_definition_in_block(header, name) else {
                return Some(GuardOperand::Var(name.clone()));
            };

            match def {
                QbeInstr::Copy(value) => resolve_guard_operand(header, value, visited),
                QbeInstr::Add(lhs, rhs) | QbeInstr::Sub(lhs, rhs) => {
                    let lhs = resolve_guard_operand(header, lhs, visited)?;
                    let rhs = resolve_guard_operand(header, rhs, visited)?;
                    match (lhs, rhs) {
                        (GuardOperand::Const(lhs), GuardOperand::Const(rhs)) => {
                            let bits = 64;
                            let value = match def {
                                QbeInstr::Add(..) => wrapping_add_width(lhs, rhs, bits),
                                QbeInstr::Sub(..) => wrapping_sub_width(lhs, rhs, bits),
                                _ => unreachable!(),
                            };
                            Some(GuardOperand::Const(value))
                        }
                        _ => None,
                    }
                }
                QbeInstr::Call(function, args, _) if args.len() >= 2 => {
                    let lhs = resolve_guard_operand(header, &args[0].1, visited)?;
                    let rhs = resolve_guard_operand(header, &args[1].1, visited)?;
                    match (function.as_str(), lhs, rhs) {
                        ("add", GuardOperand::Const(lhs), GuardOperand::Const(rhs)) => {
                            Some(GuardOperand::Const(lhs.wrapping_add(rhs)))
                        }
                        ("sub", GuardOperand::Const(lhs), GuardOperand::Const(rhs)) => {
                            Some(GuardOperand::Const(lhs.wrapping_sub(rhs)))
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        }
    }
}

fn invert_cmp_operands(kind: QbeCmp) -> Option<QbeCmp> {
    match kind {
        QbeCmp::Eq => Some(QbeCmp::Eq),
        QbeCmp::Ne => Some(QbeCmp::Ne),
        QbeCmp::Lt | QbeCmp::Le | QbeCmp::Gt | QbeCmp::Ge => None,
        QbeCmp::Slt => Some(QbeCmp::Sgt),
        QbeCmp::Sle => Some(QbeCmp::Sge),
        QbeCmp::Sgt => Some(QbeCmp::Slt),
        QbeCmp::Sge => Some(QbeCmp::Sle),
        QbeCmp::Ult => Some(QbeCmp::Ugt),
        QbeCmp::Ule => Some(QbeCmp::Uge),
        QbeCmp::Ugt => Some(QbeCmp::Ult),
        QbeCmp::Uge => Some(QbeCmp::Ule),
        QbeCmp::O | QbeCmp::Uo => None,
    }
}

fn body_preserves_guard_var(body: &Block, guard_var: &str) -> bool {
    let mut env = HashMap::<String, IdentityExpr>::new();
    env.insert(guard_var.to_string(), IdentityExpr::Var);

    let statements = block_statements(body);
    let body_end = statements.len().saturating_sub(1);

    for statement in statements.iter().take(body_end) {
        let QbeStatement::Assign(QbeValue::Temporary(dest), ty, instr) = statement else {
            continue;
        };
        let expr = eval_instruction_identity(instr, ty, &env, guard_var);
        env.insert(dest.clone(), expr);
    }

    matches!(
        env.get(guard_var).cloned().unwrap_or(IdentityExpr::Var),
        IdentityExpr::Var
    )
}

fn eval_instruction_identity(
    instr: &QbeInstr,
    ty: &QbeType,
    env: &HashMap<String, IdentityExpr>,
    guard_var: &str,
) -> IdentityExpr {
    match instr {
        QbeInstr::Copy(value) => eval_identity_value(value, env, guard_var),
        QbeInstr::Add(lhs, rhs) | QbeInstr::Sub(lhs, rhs) => {
            eval_identity_binary(instr, ty, lhs, rhs, env, guard_var)
        }
        QbeInstr::Call(function, args, _) => eval_identity_call(function, args, env, guard_var),
        _ => IdentityExpr::Unknown,
    }
}

fn eval_identity_binary(
    instr: &QbeInstr,
    ty: &QbeType,
    lhs: &QbeValue,
    rhs: &QbeValue,
    env: &HashMap<String, IdentityExpr>,
    guard_var: &str,
) -> IdentityExpr {
    let lhs_expr = eval_identity_value(lhs, env, guard_var);
    let rhs_expr = eval_identity_value(rhs, env, guard_var);
    let bits = assign_bits_from_type(ty).unwrap_or(64);

    match instr {
        QbeInstr::Add(..) => match (lhs_expr, rhs_expr) {
            (IdentityExpr::Var, IdentityExpr::Const(0))
            | (IdentityExpr::Const(0), IdentityExpr::Var) => IdentityExpr::Var,
            (IdentityExpr::Const(lhs), IdentityExpr::Const(rhs)) => {
                IdentityExpr::Const(wrapping_add_width(lhs, rhs, bits))
            }
            _ => IdentityExpr::Unknown,
        },
        QbeInstr::Sub(..) => match (lhs_expr, rhs_expr) {
            (IdentityExpr::Var, IdentityExpr::Const(0)) => IdentityExpr::Var,
            (IdentityExpr::Const(lhs), IdentityExpr::Const(rhs)) => {
                IdentityExpr::Const(wrapping_sub_width(lhs, rhs, bits))
            }
            _ => IdentityExpr::Unknown,
        },
        _ => IdentityExpr::Unknown,
    }
}

fn eval_identity_call(
    function: &str,
    args: &[(QbeType, QbeValue)],
    env: &HashMap<String, IdentityExpr>,
    guard_var: &str,
) -> IdentityExpr {
    match function {
        "sub" if args.len() >= 2 => {
            let lhs = eval_identity_value(&args[0].1, env, guard_var);
            let rhs = eval_identity_value(&args[1].1, env, guard_var);
            match (lhs, rhs) {
                (IdentityExpr::Var, IdentityExpr::Const(0)) => IdentityExpr::Var,
                (IdentityExpr::Const(a), IdentityExpr::Const(b)) => {
                    IdentityExpr::Const(a.wrapping_sub(b))
                }
                _ => IdentityExpr::Unknown,
            }
        }
        "add" if args.len() >= 2 => {
            let lhs = eval_identity_value(&args[0].1, env, guard_var);
            let rhs = eval_identity_value(&args[1].1, env, guard_var);
            match (lhs, rhs) {
                (IdentityExpr::Var, IdentityExpr::Const(0))
                | (IdentityExpr::Const(0), IdentityExpr::Var) => IdentityExpr::Var,
                (IdentityExpr::Const(a), IdentityExpr::Const(b)) => {
                    IdentityExpr::Const(a.wrapping_add(b))
                }
                _ => IdentityExpr::Unknown,
            }
        }
        _ => IdentityExpr::Unknown,
    }
}

fn eval_identity_value(
    value: &QbeValue,
    env: &HashMap<String, IdentityExpr>,
    guard_var: &str,
) -> IdentityExpr {
    match value {
        QbeValue::Temporary(name) => env.get(name).cloned().unwrap_or_else(|| {
            if name == guard_var {
                IdentityExpr::Var
            } else {
                IdentityExpr::Unknown
            }
        }),
        QbeValue::Const(value) => IdentityExpr::Const(*value),
        QbeValue::SingleConst(_) => IdentityExpr::Unknown,
        QbeValue::DoubleConst(_) => IdentityExpr::Unknown,
        QbeValue::Global(_) => IdentityExpr::Unknown,
    }
}

fn block_exit_constant_for_var(block: &Block, variable: &str) -> Option<u64> {
    let mut env = HashMap::<String, Option<u64>>::new();

    for statement in block_statements(block) {
        let QbeStatement::Assign(QbeValue::Temporary(dest), ty, instr) = statement else {
            continue;
        };
        let value = eval_instruction_constant(instr, ty, &env);
        env.insert(dest.clone(), value);
    }

    env.get(variable).copied().flatten()
}

fn eval_instruction_constant(
    instr: &QbeInstr,
    ty: &QbeType,
    env: &HashMap<String, Option<u64>>,
) -> Option<u64> {
    match instr {
        QbeInstr::Copy(value) => eval_constant_value(value, env),
        QbeInstr::Add(lhs, rhs) | QbeInstr::Sub(lhs, rhs) => {
            let lhs = eval_constant_value(lhs, env)?;
            let rhs = eval_constant_value(rhs, env)?;
            let bits = assign_bits_from_type(ty)?;
            match instr {
                QbeInstr::Add(..) => Some(wrapping_add_width(lhs, rhs, bits)),
                QbeInstr::Sub(..) => Some(wrapping_sub_width(lhs, rhs, bits)),
                _ => unreachable!(),
            }
        }
        QbeInstr::Call(function, args, _) => {
            if args.len() < 2 {
                return None;
            }
            let lhs = eval_constant_value(&args[0].1, env)?;
            let rhs = eval_constant_value(&args[1].1, env)?;
            match function.as_str() {
                "add" => Some(lhs.wrapping_add(rhs)),
                "sub" => Some(lhs.wrapping_sub(rhs)),
                _ => None,
            }
        }
        _ => None,
    }
}

fn eval_constant_value(value: &QbeValue, env: &HashMap<String, Option<u64>>) -> Option<u64> {
    match value {
        QbeValue::Temporary(name) => env.get(name).copied().flatten(),
        QbeValue::Const(value) => Some(*value),
        QbeValue::SingleConst(_) => None,
        QbeValue::DoubleConst(_) => None,
        QbeValue::Global(_) => None,
    }
}

fn eval_guard_with_const(guard: &LoopGuard, value: u64) -> Option<bool> {
    let lhs = truncate_to_bits(value, guard.bits);
    let rhs = truncate_to_bits(guard.constant, guard.bits);
    let lhs_signed = signed_from_bits(lhs, guard.bits)?;
    let rhs_signed = signed_from_bits(rhs, guard.bits)?;

    let result = match guard.kind {
        QbeCmp::Eq => lhs == rhs,
        QbeCmp::Ne => lhs != rhs,
        QbeCmp::Lt | QbeCmp::Le | QbeCmp::Gt | QbeCmp::Ge => return None,
        QbeCmp::Slt => lhs_signed < rhs_signed,
        QbeCmp::Sle => lhs_signed <= rhs_signed,
        QbeCmp::Sgt => lhs_signed > rhs_signed,
        QbeCmp::Sge => lhs_signed >= rhs_signed,
        QbeCmp::Ult => lhs < rhs,
        QbeCmp::Ule => lhs <= rhs,
        QbeCmp::Ugt => lhs > rhs,
        QbeCmp::Uge => lhs >= rhs,
        QbeCmp::O | QbeCmp::Uo => return None,
    };

    Some(result)
}

fn assign_bits_from_type(ty: &QbeType) -> Option<u32> {
    match ty {
        QbeType::Byte
        | QbeType::SignedByte
        | QbeType::UnsignedByte
        | QbeType::Halfword
        | QbeType::SignedHalfword
        | QbeType::UnsignedHalfword
        | QbeType::Word
        | QbeType::Single
        | QbeType::Zero => Some(32),
        QbeType::Long | QbeType::Double | QbeType::Aggregate(_) => Some(64),
    }
}

fn truncate_to_bits(value: u64, bits: u32) -> u64 {
    if bits >= 64 {
        value
    } else {
        value & ((1u64 << bits) - 1)
    }
}

fn signed_from_bits(value: u64, bits: u32) -> Option<i64> {
    let truncated = truncate_to_bits(value, bits);
    match bits {
        32 => Some((truncated as u32 as i32) as i64),
        64 => Some(truncated as i64),
        _ => None,
    }
}

fn wrapping_add_width(lhs: u64, rhs: u64, bits: u32) -> u64 {
    truncate_to_bits(lhs.wrapping_add(rhs), bits)
}

fn wrapping_sub_width(lhs: u64, rhs: u64, bits: u32) -> u64 {
    truncate_to_bits(lhs.wrapping_sub(rhs), bits)
}
