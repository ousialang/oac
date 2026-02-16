use std::collections::{BTreeSet, HashMap};

use qbe::{
    BlockItem, Cmp as QbeCmp, Function as QbeFunction, Instr as QbeInstr,
    Statement as QbeStatement, Type as QbeType, Value as QbeValue,
};

use crate::{
    EncodeOptions, QbeSmtError, BLIT_INLINE_LIMIT, GLOBAL_BASE, GLOBAL_STRIDE, INITIAL_HEAP_BASE,
};

pub(crate) fn encode_function(
    function: &QbeFunction,
    options: &EncodeOptions,
) -> Result<String, QbeSmtError> {
    let args = collect_function_args(function)?;

    let mut flat = Vec::<QbeStatement>::new();
    let mut label_to_pc = HashMap::<String, usize>::new();
    for block in &function.blocks {
        if label_to_pc.contains_key(&block.label) {
            return Err(QbeSmtError::DuplicateLabel {
                label: block.label.clone(),
            });
        }
        label_to_pc.insert(block.label.clone(), flat.len());
        for item in &block.items {
            if let BlockItem::Statement(statement) = item {
                flat.push(statement.clone());
            }
        }
    }

    if flat.is_empty() {
        return Err(QbeSmtError::EmptyFunction);
    }

    for (pc, statement) in flat.iter().enumerate() {
        validate_statement_supported(statement, pc)?;
    }

    let mut regs = BTreeSet::<String>::new();
    for arg in &args {
        regs.insert(arg.name.clone());
    }
    for statement in &flat {
        collect_regs_statement(statement, &mut regs);
    }

    let reg_list: Vec<String> = regs.into_iter().collect();
    let mut reg_slots = HashMap::<String, u32>::new();
    for (i, name) in reg_list.iter().enumerate() {
        reg_slots.insert(name.clone(), i as u32);
    }

    let mut globals = BTreeSet::<String>::new();
    for statement in &flat {
        collect_globals_statement(statement, &mut globals);
    }
    for arg in &args {
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

    let arg_names: BTreeSet<&str> = args.iter().map(|arg| arg.name.as_str()).collect();
    let mut init_terms = vec![
        format!("(= exit {})", bv_const_u64(0, 64)),
        format!("(= heap {})", bv_const_u64(INITIAL_HEAP_BASE, 64)),
    ];
    for reg_name in &reg_list {
        if !arg_names.contains(reg_name.as_str()) {
            let slot = *reg_slots.get(reg_name).expect("reg slot is present");
            init_terms.push(format!(
                "(= (select regs {}) {})",
                reg_slot_const(slot),
                bv_const_u64(0, 64)
            ));
        }
    }

    if options.assume_main_argc_non_negative {
        if let Some(first_arg) = args.first() {
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

    for (pc, statement) in flat.iter().enumerate() {
        let from_rel = pc_relation_name(pc);

        let transition = TransitionExprs {
            regs_next: regs_update_expr(statement, "regs", "mem", "heap", &reg_slots, &global_map),
            mem_next: memory_update_expr(statement, "mem", "regs", &reg_slots, &global_map),
            heap_next: heap_update_expr(statement, "heap", "regs", &reg_slots, &global_map),
            exit_next: exit_update_expr(statement, "exit", "regs", &reg_slots, &global_map),
        };

        match statement {
            QbeStatement::Volatile(QbeInstr::Jmp(target)) => {
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
            QbeStatement::Volatile(QbeInstr::Jnz(cond, if_true, if_false)) => {
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
            QbeStatement::Volatile(QbeInstr::Ret(_)) | QbeStatement::Volatile(QbeInstr::Hlt) => {
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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

#[derive(Debug)]
struct FunctionArg {
    name: String,
}

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

fn collect_function_args(function: &QbeFunction) -> Result<Vec<FunctionArg>, QbeSmtError> {
    let mut out = Vec::with_capacity(function.arguments.len());
    for (ty, value) in &function.arguments {
        let QbeValue::Temporary(name) = value else {
            return Err(QbeSmtError::Unsupported {
                message: format!(
                    "function argument value `{value}` must be a temporary for CHC encoding"
                ),
            });
        };

        let assign_ty = assign_type_from_qbe(ty);
        if matches!(assign_ty, AssignType::Single | AssignType::Double) {
            return Err(QbeSmtError::Unsupported {
                message: format!(
                    "unsupported floating-point function argument `%{}` in CHC encoding",
                    name
                ),
            });
        }

        out.push(FunctionArg { name: name.clone() });
    }

    Ok(out)
}

fn validate_statement_supported(statement: &QbeStatement, pc: usize) -> Result<(), QbeSmtError> {
    match statement {
        QbeStatement::Assign(dest, ty, instr) => {
            if !matches!(dest, QbeValue::Temporary(_)) {
                return Err(QbeSmtError::Unsupported {
                    message: format!(
                        "pc {pc}: assignment destination `{dest}` must be a temporary"
                    ),
                });
            }

            let assign_ty = assign_type_from_qbe(ty);

            match instr {
                QbeInstr::Add(..)
                | QbeInstr::Sub(..)
                | QbeInstr::Mul(..)
                | QbeInstr::Div(..)
                | QbeInstr::Udiv(..)
                | QbeInstr::Rem(..)
                | QbeInstr::Urem(..)
                | QbeInstr::And(..)
                | QbeInstr::Or(..)
                | QbeInstr::Shl(..)
                | QbeInstr::Shr(..)
                | QbeInstr::Sar(..)
                | QbeInstr::Copy(..) => {
                    if matches!(assign_ty, AssignType::Single | AssignType::Double) {
                        return Err(QbeSmtError::Unsupported {
                            message: format!("pc {pc}: floating-point assignments are unsupported"),
                        });
                    }
                }
                QbeInstr::Cmp(cmp_ty, kind, ..) => {
                    let cmp_assign_ty = assign_type_from_qbe(cmp_ty);
                    if matches!(kind, QbeCmp::O | QbeCmp::Uo)
                        || matches!(assign_ty, AssignType::Single | AssignType::Double)
                        || matches!(cmp_assign_ty, AssignType::Single | AssignType::Double)
                    {
                        return Err(QbeSmtError::Unsupported {
                            message: format!("pc {pc}: unsupported compare operation"),
                        });
                    }
                }
                QbeInstr::Cast(..)
                | QbeInstr::Extsw(..)
                | QbeInstr::Extuw(..)
                | QbeInstr::Extsh(..)
                | QbeInstr::Extuh(..)
                | QbeInstr::Extsb(..)
                | QbeInstr::Extub(..) => {
                    if matches!(assign_ty, AssignType::Single | AssignType::Double) {
                        return Err(QbeSmtError::Unsupported {
                            message: format!(
                                "pc {pc}: floating-point unary assignments are unsupported"
                            ),
                        });
                    }
                }
                QbeInstr::Exts(..) => {
                    return Err(QbeSmtError::Unsupported {
                        message: format!("pc {pc}: unsupported unary operation exts"),
                    })
                }
                QbeInstr::Truncd(..) => {
                    return Err(QbeSmtError::Unsupported {
                        message: format!("pc {pc}: unsupported unary operation truncd"),
                    })
                }
                QbeInstr::Load(load_ty, ..) => {
                    let load_ty = load_store_type_from_qbe(load_ty);
                    if matches!(assign_ty, AssignType::Single | AssignType::Double)
                        || matches!(load_ty, LoadStoreType::Single | LoadStoreType::Double)
                        || load_store_width_bits(load_ty).is_none()
                    {
                        return Err(QbeSmtError::Unsupported {
                            message: format!("pc {pc}: unsupported load operation"),
                        });
                    }
                }
                QbeInstr::Store(..) => {
                    return Err(QbeSmtError::Unsupported {
                        message: format!(
                            "pc {pc}: unsupported assignment operation for assignment type {:?}",
                            assign_ty
                        ),
                    })
                }
                QbeInstr::Blit(..)
                | QbeInstr::Jnz(..)
                | QbeInstr::Jmp(..)
                | QbeInstr::Ret(..)
                | QbeInstr::Hlt
                | QbeInstr::DbgFile(..)
                | QbeInstr::DbgLoc(..)
                | QbeInstr::Vastart(..)
                | QbeInstr::Vaarg(..)
                | QbeInstr::Stosi(..)
                | QbeInstr::Stoui(..)
                | QbeInstr::Dtosi(..)
                | QbeInstr::Dtoui(..)
                | QbeInstr::Swtof(..)
                | QbeInstr::Uwtof(..)
                | QbeInstr::Sltof(..)
                | QbeInstr::Ultof(..) => {
                    return Err(QbeSmtError::Unsupported {
                        message: format!(
                            "pc {pc}: unsupported assignment operation for assignment type {:?}",
                            assign_ty
                        ),
                    })
                }
                QbeInstr::Alloc4(..) | QbeInstr::Alloc8(..) => {}
                QbeInstr::Alloc16(size) => {
                    if u64::try_from(*size).is_err() {
                        return Err(QbeSmtError::Unsupported {
                            message: format!(
                                "pc {pc}: alloc16 size {size} exceeds u64 modeling range"
                            ),
                        });
                    }
                }
                QbeInstr::Call(function, _, variadic_index) => {
                    if variadic_index.is_some() {
                        return Err(QbeSmtError::Unsupported {
                            message: format!(
                                "pc {pc}: variadic call target ${function} is unsupported"
                            ),
                        });
                    }
                    if !is_malloc_call(function) {
                        return Err(QbeSmtError::Unsupported {
                            message: format!("pc {pc}: unsupported call target ${function}"),
                        });
                    }
                }
                QbeInstr::Phi(..) => {
                    return Err(QbeSmtError::Unsupported {
                        message: format!(
                            "pc {pc}: phi is unsupported for assignment type {:?}",
                            assign_ty
                        ),
                    })
                }
            }
        }
        QbeStatement::Volatile(instr) => match instr {
            QbeInstr::Jmp(..)
            | QbeInstr::Jnz(..)
            | QbeInstr::Ret(..)
            | QbeInstr::Hlt
            | QbeInstr::DbgFile(..)
            | QbeInstr::DbgLoc(..) => {}
            QbeInstr::Store(store_ty, ..) => {
                let store_ty = load_store_type_from_qbe(store_ty);
                if load_store_width_bits(store_ty).is_none()
                    || matches!(store_ty, LoadStoreType::Single | LoadStoreType::Double)
                {
                    return Err(QbeSmtError::Unsupported {
                        message: format!("pc {pc}: unsupported store operation"),
                    });
                }
            }
            QbeInstr::Blit(_, _, len) => {
                if *len > BLIT_INLINE_LIMIT {
                    return Err(QbeSmtError::Unsupported {
                        message: format!(
                            "pc {pc}: blit len {len} exceeds inline limit {BLIT_INLINE_LIMIT}"
                        ),
                    });
                }
            }
            QbeInstr::Call(function, _, variadic_index) => {
                if variadic_index.is_some() {
                    return Err(QbeSmtError::Unsupported {
                        message: format!(
                            "pc {pc}: variadic call target ${function} is unsupported"
                        ),
                    });
                }
                if !is_malloc_call(function) {
                    return Err(QbeSmtError::Unsupported {
                        message: format!("pc {pc}: unsupported call target ${function}"),
                    });
                }
            }
            _ => {
                return Err(QbeSmtError::Unsupported {
                    message: format!("pc {pc}: unsupported volatile/side-effect instruction"),
                })
            }
        },
    }

    Ok(())
}

fn regs_update_expr(
    statement: &QbeStatement,
    regs_curr: &str,
    mem_curr: &str,
    heap_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> String {
    let QbeStatement::Assign(dest, ty, instr) = statement else {
        return regs_curr.to_string();
    };

    let dest_name = temp_name(dest).expect("validated assignment destination is temporary");
    let slot = *reg_slots
        .get(dest_name)
        .expect("destination register slot is present");
    let assign_ty = assign_type_from_qbe(ty);

    let value_expr = match instr {
        QbeInstr::Add(lhs, rhs)
        | QbeInstr::Sub(lhs, rhs)
        | QbeInstr::Mul(lhs, rhs)
        | QbeInstr::Div(lhs, rhs)
        | QbeInstr::Udiv(lhs, rhs)
        | QbeInstr::Rem(lhs, rhs)
        | QbeInstr::Urem(lhs, rhs)
        | QbeInstr::And(lhs, rhs)
        | QbeInstr::Or(lhs, rhs)
        | QbeInstr::Shl(lhs, rhs)
        | QbeInstr::Shr(lhs, rhs)
        | QbeInstr::Sar(lhs, rhs) => {
            let lhs_expr = value_to_smt(lhs, regs_curr, reg_slots, global_map);
            let rhs_expr = value_to_smt(rhs, regs_curr, reg_slots, global_map);
            binary_expr(instr, assign_ty, &lhs_expr, &rhs_expr)
        }
        QbeInstr::Copy(value) => {
            let value_expr = value_to_smt(value, regs_curr, reg_slots, global_map);
            normalize_to_assign_type(&value_expr, assign_ty)
        }
        QbeInstr::Cmp(cmp_ty, kind, lhs, rhs) => {
            let pred = cmp_to_smt(
                *kind,
                assign_type_from_qbe(cmp_ty),
                lhs,
                rhs,
                regs_curr,
                reg_slots,
                global_map,
            );
            normalize_to_assign_type(
                &format!(
                    "(ite {pred} {} {})",
                    bv_const_u64(1, 64),
                    bv_const_u64(0, 64)
                ),
                assign_ty,
            )
        }
        QbeInstr::Cast(value) => {
            let value_expr = value_to_smt(value, regs_curr, reg_slots, global_map);
            normalize_to_assign_type(&value_expr, assign_ty)
        }
        QbeInstr::Extsw(value) => {
            let value_expr = value_to_smt(value, regs_curr, reg_slots, global_map);
            sign_extend_from_expr(&value_expr, 32)
        }
        QbeInstr::Extuw(value) => {
            let value_expr = value_to_smt(value, regs_curr, reg_slots, global_map);
            zero_extend_from_expr(&value_expr, 32)
        }
        QbeInstr::Extsh(value) => {
            let value_expr = value_to_smt(value, regs_curr, reg_slots, global_map);
            sign_extend_from_expr(&value_expr, 16)
        }
        QbeInstr::Extuh(value) => {
            let value_expr = value_to_smt(value, regs_curr, reg_slots, global_map);
            zero_extend_from_expr(&value_expr, 16)
        }
        QbeInstr::Extsb(value) => {
            let value_expr = value_to_smt(value, regs_curr, reg_slots, global_map);
            sign_extend_from_expr(&value_expr, 8)
        }
        QbeInstr::Extub(value) => {
            let value_expr = value_to_smt(value, regs_curr, reg_slots, global_map);
            zero_extend_from_expr(&value_expr, 8)
        }
        QbeInstr::Load(load_ty, address) => {
            let address_expr = value_to_smt(address, regs_curr, reg_slots, global_map);
            let loaded =
                load_memory_expr(mem_curr, &address_expr, load_store_type_from_qbe(load_ty));
            normalize_to_assign_type(&loaded, assign_ty)
        }
        QbeInstr::Alloc4(..) | QbeInstr::Alloc8(..) | QbeInstr::Alloc16(..) => {
            normalize_to_assign_type(heap_curr, assign_ty)
        }
        QbeInstr::Call(function, ..) => {
            if is_malloc_call(function) {
                normalize_to_assign_type(heap_curr, assign_ty)
            } else {
                unreachable!("unsupported calls should be rejected")
            }
        }
        _ => {
            unreachable!("unsupported instructions should be rejected before transition generation")
        }
    };

    format!("(store {regs_curr} {} {value_expr})", reg_slot_const(slot))
}

fn memory_update_expr(
    statement: &QbeStatement,
    mem_curr: &str,
    regs_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> String {
    match statement {
        QbeStatement::Volatile(QbeInstr::Store(store_ty, address, value)) => {
            let store_ty = load_store_type_from_qbe(store_ty);
            let width = load_store_width_bits(store_ty)
                .expect("unsupported store types should be rejected before transition generation");
            let value_expr = value_to_smt(value, regs_curr, reg_slots, global_map);
            let address_expr = value_to_smt(address, regs_curr, reg_slots, global_map);
            store_memory_expr(mem_curr, &address_expr, &value_expr, width)
        }
        QbeStatement::Volatile(QbeInstr::Blit(src, dst, len)) => {
            let src_expr = value_to_smt(src, regs_curr, reg_slots, global_map);
            let dst_expr = value_to_smt(dst, regs_curr, reg_slots, global_map);
            inline_blit_expr(mem_curr, &src_expr, &dst_expr, *len)
        }
        _ => mem_curr.to_string(),
    }
}

fn heap_update_expr(
    statement: &QbeStatement,
    heap_curr: &str,
    regs_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> String {
    match statement {
        QbeStatement::Assign(_, _, QbeInstr::Alloc4(size)) => {
            aligned_heap_increment_expr(heap_curr, *size as u64, 4)
        }
        QbeStatement::Assign(_, _, QbeInstr::Alloc8(size)) => {
            aligned_heap_increment_expr(heap_curr, *size, 8)
        }
        QbeStatement::Assign(_, _, QbeInstr::Alloc16(size)) => aligned_heap_increment_expr(
            heap_curr,
            u64::try_from(*size).expect("validated alloc16"),
            16,
        ),
        QbeStatement::Assign(_, _, QbeInstr::Call(function, args, _))
        | QbeStatement::Volatile(QbeInstr::Call(function, args, _)) => {
            if is_malloc_call(function) {
                if let Some((_, size_arg)) = args.first() {
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

fn aligned_heap_increment_expr(heap_curr: &str, size: u64, align: u64) -> String {
    let aligned_size = if size == 0 {
        align.max(1)
    } else {
        let rem = size % align.max(1);
        if rem == 0 {
            size
        } else {
            size + (align.max(1) - rem)
        }
    };
    format!("(bvadd {heap_curr} {})", bv_const_u64(aligned_size, 64))
}

fn exit_update_expr(
    statement: &QbeStatement,
    exit_curr: &str,
    regs_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> String {
    match statement {
        QbeStatement::Volatile(QbeInstr::Ret(Some(value))) => {
            value_to_smt(value, regs_curr, reg_slots, global_map)
        }
        QbeStatement::Volatile(QbeInstr::Ret(None)) => bv_const_u64(0, 64),
        _ => exit_curr.to_string(),
    }
}

fn binary_expr(instr: &QbeInstr, ty: AssignType, lhs: &str, rhs: &str) -> String {
    let width = ty.bits();

    let expr_for_width = |lhs_expr: &str, rhs_expr: &str| match instr {
        QbeInstr::Add(..) => format!("(bvadd {lhs_expr} {rhs_expr})"),
        QbeInstr::Sub(..) => format!("(bvsub {lhs_expr} {rhs_expr})"),
        QbeInstr::Mul(..) => format!("(bvmul {lhs_expr} {rhs_expr})"),
        QbeInstr::Div(..) => format!("(bvsdiv {lhs_expr} {rhs_expr})"),
        QbeInstr::Udiv(..) => format!("(bvudiv {lhs_expr} {rhs_expr})"),
        QbeInstr::Rem(..) => format!("(bvsrem {lhs_expr} {rhs_expr})"),
        QbeInstr::Urem(..) => format!("(bvurem {lhs_expr} {rhs_expr})"),
        QbeInstr::And(..) => format!("(bvand {lhs_expr} {rhs_expr})"),
        QbeInstr::Or(..) => format!("(bvor {lhs_expr} {rhs_expr})"),
        QbeInstr::Shl(..) => format!("(bvshl {lhs_expr} {rhs_expr})"),
        QbeInstr::Shr(..) => format!("(bvlshr {lhs_expr} {rhs_expr})"),
        QbeInstr::Sar(..) => format!("(bvashr {lhs_expr} {rhs_expr})"),
        _ => unreachable!("binary_expr called with non-binary instruction"),
    };

    if width == 64 {
        expr_for_width(lhs, rhs)
    } else {
        let lhs32 = extract_low_bits(lhs, 32);
        let rhs32 = extract_low_bits(rhs, 32);
        let expr32 = expr_for_width(&lhs32, &rhs32);
        sign_extend_known_width(&expr32, 32, 64)
    }
}

fn cmp_to_smt(
    kind: QbeCmp,
    cmp_ty: AssignType,
    lhs: &QbeValue,
    rhs: &QbeValue,
    regs_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> String {
    let lhs = value_to_smt(lhs, regs_curr, reg_slots, global_map);
    let rhs = value_to_smt(rhs, regs_curr, reg_slots, global_map);

    if cmp_ty.bits() == 32 {
        let lhs = extract_low_bits(&lhs, 32);
        let rhs = extract_low_bits(&rhs, 32);
        cmp_predicate(kind, &lhs, &rhs)
    } else {
        cmp_predicate(kind, &lhs, &rhs)
    }
}

fn cmp_predicate(kind: QbeCmp, lhs: &str, rhs: &str) -> String {
    match kind {
        QbeCmp::Eq => format!("(= {lhs} {rhs})"),
        QbeCmp::Ne => format!("(distinct {lhs} {rhs})"),
        QbeCmp::Slt => format!("(bvslt {lhs} {rhs})"),
        QbeCmp::Sle => format!("(bvsle {lhs} {rhs})"),
        QbeCmp::Sgt => format!("(bvsgt {lhs} {rhs})"),
        QbeCmp::Sge => format!("(bvsge {lhs} {rhs})"),
        QbeCmp::Ult => format!("(bvult {lhs} {rhs})"),
        QbeCmp::Ule => format!("(bvule {lhs} {rhs})"),
        QbeCmp::Ugt => format!("(bvugt {lhs} {rhs})"),
        QbeCmp::Uge => format!("(bvuge {lhs} {rhs})"),
        QbeCmp::O | QbeCmp::Uo => unreachable!("unsupported compares should be rejected"),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LoadStoreType {
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

fn load_store_type_from_qbe(ty: &QbeType) -> LoadStoreType {
    match ty {
        QbeType::Byte => LoadStoreType::Byte,
        QbeType::SignedByte => LoadStoreType::SignedByte,
        QbeType::UnsignedByte => LoadStoreType::UnsignedByte,
        QbeType::Halfword => LoadStoreType::Halfword,
        QbeType::SignedHalfword => LoadStoreType::SignedHalfword,
        QbeType::UnsignedHalfword => LoadStoreType::UnsignedHalfword,
        QbeType::Word => LoadStoreType::Word,
        QbeType::Long => LoadStoreType::Long,
        QbeType::Single => LoadStoreType::Single,
        QbeType::Double => LoadStoreType::Double,
        QbeType::Aggregate(_) => LoadStoreType::Aggregate,
        QbeType::Zero => LoadStoreType::Zero,
    }
}

fn load_store_width_bits(ty: LoadStoreType) -> Option<u32> {
    match ty {
        LoadStoreType::Byte
        | LoadStoreType::SignedByte
        | LoadStoreType::UnsignedByte
        | LoadStoreType::Zero => Some(8),
        LoadStoreType::Halfword
        | LoadStoreType::SignedHalfword
        | LoadStoreType::UnsignedHalfword => Some(16),
        LoadStoreType::Word | LoadStoreType::Single => Some(32),
        LoadStoreType::Long | LoadStoreType::Double => Some(64),
        LoadStoreType::Aggregate => None,
    }
}

fn load_memory_expr(mem_expr: &str, address_expr: &str, load_ty: LoadStoreType) -> String {
    let width = load_store_width_bits(load_ty)
        .expect("unsupported load types should be rejected before transition generation");

    let loaded = load_raw_bits(mem_expr, address_expr, width);
    match load_ty {
        LoadStoreType::SignedByte => sign_extend_known_width(&loaded, 8, 64),
        LoadStoreType::SignedHalfword => sign_extend_known_width(&loaded, 16, 64),
        LoadStoreType::Word => sign_extend_known_width(&loaded, 32, 64),
        LoadStoreType::Byte | LoadStoreType::UnsignedByte | LoadStoreType::Zero => {
            zero_extend_known_width(&loaded, 8, 64)
        }
        LoadStoreType::Halfword | LoadStoreType::UnsignedHalfword => {
            zero_extend_known_width(&loaded, 16, 64)
        }
        LoadStoreType::Long => loaded,
        LoadStoreType::Single | LoadStoreType::Double | LoadStoreType::Aggregate => {
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

fn collect_regs_statement(statement: &QbeStatement, regs: &mut BTreeSet<String>) {
    if let QbeStatement::Assign(dest, _, _) = statement {
        if let QbeValue::Temporary(name) = dest {
            regs.insert(name.clone());
        }
    }

    collect_values_in_statement(statement, &mut |value| {
        if let QbeValue::Temporary(name) = value {
            regs.insert(name.clone());
        }
    });
}

fn collect_globals_statement(statement: &QbeStatement, globals: &mut BTreeSet<String>) {
    collect_values_in_statement(statement, &mut |value| {
        if let QbeValue::Global(name) = value {
            globals.insert(name.clone());
        }
    });
}

fn collect_values_in_statement(statement: &QbeStatement, on_value: &mut impl FnMut(&QbeValue)) {
    match statement {
        QbeStatement::Assign(_, _, instr) | QbeStatement::Volatile(instr) => {
            collect_values_in_instr(instr, on_value)
        }
    }
}

fn collect_values_in_instr(instr: &QbeInstr, on_value: &mut impl FnMut(&QbeValue)) {
    match instr {
        QbeInstr::Add(lhs, rhs)
        | QbeInstr::Sub(lhs, rhs)
        | QbeInstr::Mul(lhs, rhs)
        | QbeInstr::Div(lhs, rhs)
        | QbeInstr::Udiv(lhs, rhs)
        | QbeInstr::Rem(lhs, rhs)
        | QbeInstr::Urem(lhs, rhs)
        | QbeInstr::And(lhs, rhs)
        | QbeInstr::Or(lhs, rhs)
        | QbeInstr::Shl(lhs, rhs)
        | QbeInstr::Shr(lhs, rhs)
        | QbeInstr::Sar(lhs, rhs)
        | QbeInstr::Cmp(_, _, lhs, rhs) => {
            on_value(lhs);
            on_value(rhs);
        }
        QbeInstr::Copy(value)
        | QbeInstr::Cast(value)
        | QbeInstr::Extsw(value)
        | QbeInstr::Extuw(value)
        | QbeInstr::Extsh(value)
        | QbeInstr::Extuh(value)
        | QbeInstr::Extsb(value)
        | QbeInstr::Extub(value)
        | QbeInstr::Exts(value)
        | QbeInstr::Truncd(value)
        | QbeInstr::Stosi(value)
        | QbeInstr::Stoui(value)
        | QbeInstr::Dtosi(value)
        | QbeInstr::Dtoui(value)
        | QbeInstr::Swtof(value)
        | QbeInstr::Uwtof(value)
        | QbeInstr::Sltof(value)
        | QbeInstr::Ultof(value)
        | QbeInstr::Vastart(value)
        | QbeInstr::Vaarg(_, value)
        | QbeInstr::Load(_, value)
        | QbeInstr::Jnz(value, _, _)
        | QbeInstr::Ret(Some(value)) => on_value(value),
        QbeInstr::Call(_, args, _) => {
            for (_, value) in args {
                on_value(value);
            }
        }
        QbeInstr::Store(_, address, value) => {
            on_value(address);
            on_value(value);
        }
        QbeInstr::Blit(src, dst, _) => {
            on_value(src);
            on_value(dst);
        }
        QbeInstr::Phi(_, left_value, _, right_value) => {
            on_value(left_value);
            on_value(right_value);
        }
        QbeInstr::Alloc4(..)
        | QbeInstr::Alloc8(..)
        | QbeInstr::Alloc16(..)
        | QbeInstr::DbgFile(..)
        | QbeInstr::DbgLoc(..)
        | QbeInstr::Jmp(..)
        | QbeInstr::Ret(None)
        | QbeInstr::Hlt => {}
    }
}

fn value_to_smt(
    value: &QbeValue,
    regs_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> String {
    match value {
        QbeValue::Temporary(name) => reg_read_expr(name, regs_curr, reg_slots),
        QbeValue::Global(name) => {
            let addr = *global_map.get(name).unwrap_or(&GLOBAL_BASE);
            bv_const_u64(addr, 64)
        }
        QbeValue::Const(value) => bv_const_u64(*value, 64),
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

fn temp_name(value: &QbeValue) -> Option<&str> {
    match value {
        QbeValue::Temporary(name) => Some(name.as_str()),
        _ => None,
    }
}

fn assign_type_from_qbe(ty: &QbeType) -> AssignType {
    match ty {
        QbeType::Byte
        | QbeType::SignedByte
        | QbeType::UnsignedByte
        | QbeType::Halfword
        | QbeType::SignedHalfword
        | QbeType::UnsignedHalfword
        | QbeType::Word
        | QbeType::Zero => AssignType::Word,
        QbeType::Long | QbeType::Aggregate(_) => AssignType::Long,
        QbeType::Single => AssignType::Single,
        QbeType::Double => AssignType::Double,
    }
}
