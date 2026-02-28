use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use qbe::{
    BlockItem, Cmp as QbeCmp, Function as QbeFunction, Instr as QbeInstr, Module as QbeModule,
    Statement as QbeStatement, Type as QbeType, Value as QbeValue,
};

use crate::{
    encode_extern_models::{call_is_exit, extern_call_model, ExternCallModel},
    EncodeOptions, FunctionArgInvariantAssumption, ModuleAssumptions, QbeSmtError,
    BLIT_INLINE_LIMIT, GLOBAL_BASE, GLOBAL_STRIDE, INITIAL_HEAP_BASE,
};

pub(crate) fn encode_module(
    module: &QbeModule,
    entry: &str,
    options: &EncodeOptions,
    assumptions: &ModuleAssumptions,
) -> Result<String, QbeSmtError> {
    let context = build_module_encoding_context(module, entry, assumptions)?;

    let mut smt = String::new();
    smt.push_str("(set-logic HORN)\n");
    smt.push_str("(set-option :fp.engine spacer)\n");
    smt.push_str("(set-info :source |qbe-smt chc fixedpoint model|)\n\n");

    for function_name in &context.function_order {
        let function = context
            .functions
            .get(function_name)
            .expect("function metadata exists");
        for pc in 0..function.flattened.statements.len() {
            smt.push_str(&format!(
                "(declare-rel {} ({} {} {} {} {} {} {} {}))\n",
                module_pc_relation_name(function.id, pc),
                REG_STATE_SORT,
                MEM_STATE_SORT,
                BV64_SORT,
                BV64_SORT,
                BV32_SORT,
                REG_STATE_SORT,
                MEM_STATE_SORT,
                BV64_SORT
            ));
        }
        smt.push_str(&format!(
            "(declare-rel {} ({} {} {} {} {} {}))\n",
            module_ret_relation_name(function.id),
            REG_STATE_SORT,
            MEM_STATE_SORT,
            BV64_SORT,
            BV64_SORT,
            MEM_STATE_SORT,
            BV64_SORT
        ));
        smt.push_str(&format!(
            "(declare-rel {} ({} {} {} {} {} {}))\n",
            module_abort_relation_name(function.id),
            REG_STATE_SORT,
            MEM_STATE_SORT,
            BV64_SORT,
            BV64_SORT,
            MEM_STATE_SORT,
            BV64_SORT
        ));
    }
    smt.push_str("(declare-rel bad ())\n\n");

    smt.push_str(&format!("(declare-var regs {})\n", REG_STATE_SORT));
    smt.push_str(&format!("(declare-var mem {})\n", MEM_STATE_SORT));
    smt.push_str(&format!("(declare-var heap {})\n", BV64_SORT));
    smt.push_str(&format!("(declare-var exit {})\n", BV64_SORT));
    smt.push_str(&format!("(declare-var pred {})\n", BV32_SORT));
    smt.push_str(&format!("(declare-var regs_next {})\n", REG_STATE_SORT));
    smt.push_str(&format!("(declare-var mem_next {})\n", MEM_STATE_SORT));
    smt.push_str(&format!("(declare-var heap_next {})\n", BV64_SORT));
    smt.push_str(&format!("(declare-var exit_next {})\n", BV64_SORT));
    smt.push_str(&format!("(declare-var pred_next {})\n", BV32_SORT));
    smt.push_str(&format!("(declare-var in_regs {})\n", REG_STATE_SORT));
    smt.push_str(&format!("(declare-var in_mem {})\n", MEM_STATE_SORT));
    smt.push_str(&format!("(declare-var in_heap {})\n", BV64_SORT));
    smt.push_str(&format!("(declare-var regs_call {})\n", REG_STATE_SORT));
    smt.push_str(&format!("(declare-var mem_call {})\n", MEM_STATE_SORT));
    smt.push_str(&format!("(declare-var heap_call {})\n", BV64_SORT));
    smt.push_str(&format!("(declare-var ret_call {})\n", BV64_SORT));
    smt.push_str(&format!("(declare-var code_call {})\n", BV64_SORT));
    for assumption_index in 0..context.max_arg_invariant_assumptions {
        smt.push_str(&format!(
            "(declare-var {} {})\n",
            assumption_regs_var(assumption_index),
            REG_STATE_SORT
        ));
        smt.push_str(&format!(
            "(declare-var {} {})\n",
            assumption_mem_var(assumption_index),
            MEM_STATE_SORT
        ));
        smt.push_str(&format!(
            "(declare-var {} {})\n",
            assumption_heap_var(assumption_index),
            BV64_SORT
        ));
        smt.push_str(&format!(
            "(declare-var {} {})\n",
            assumption_ret_var(assumption_index),
            BV64_SORT
        ));
    }
    smt.push('\n');

    for function_name in &context.function_order {
        let function = context
            .functions
            .get(function_name)
            .expect("function metadata exists");
        let flat = &function.flattened.statements;
        let label_to_pc = &function.flattened.label_to_pc;
        let label_to_block_id = &function.flattened.label_to_block_id;
        let pc_to_block_id = &function.flattened.pc_to_block_id;

        let mut init_terms = vec![
            format!("(= exit {})", bv_const_u64(0, 64)),
            format!("(= pred {})", bv_const_u64(u32::MAX as u64, 32)),
            "(= in_regs regs)".to_string(),
            "(= in_mem mem)".to_string(),
            "(= in_heap heap)".to_string(),
        ];

        let arg_names: BTreeSet<&str> = function.args.iter().map(|arg| arg.name.as_str()).collect();
        for reg_name in &function.reg_list {
            if !arg_names.contains(reg_name.as_str()) {
                let slot = *function
                    .reg_slots
                    .get(reg_name)
                    .expect("function reg slot exists");
                init_terms.push(format!(
                    "(= (select regs {}) {})",
                    reg_slot_const(slot),
                    bv_const_u64(0, 64)
                ));
            }
        }

        let function_assumptions = context
            .arg_invariant_assumptions
            .get(function_name)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        for (assumption_index, assumption) in function_assumptions.iter().enumerate() {
            let invariant_function = context
                .functions
                .get(&assumption.invariant_function_name)
                .expect("validated invariant function exists");
            let source_arg = function
                .args
                .get(assumption.arg_index)
                .expect("validated function arg index exists");
            let source_slot = *function
                .reg_slots
                .get(&source_arg.name)
                .expect("validated source argument register slot exists");
            let source_value_expr = format!("(select regs {})", reg_slot_const(source_slot));
            let call_regs_expr =
                build_unary_callee_input_regs_expr(invariant_function, &source_value_expr)?;
            let regs_var = assumption_regs_var(assumption_index);
            let mem_var = assumption_mem_var(assumption_index);
            let heap_var = assumption_heap_var(assumption_index);
            let ret_var = assumption_ret_var(assumption_index);

            init_terms.push(format!("(= {regs_var} {call_regs_expr})"));
            init_terms.push(module_ret_relation_app(
                &module_ret_relation_name(invariant_function.id),
                &regs_var,
                "mem",
                "heap",
                &ret_var,
                &mem_var,
                &heap_var,
            ));
            init_terms.push(format!("(distinct {ret_var} {})", bv_const_u64(0, 64)));
        }

        if function.name == context.entry {
            init_terms.push(format!("(= heap {})", bv_const_u64(INITIAL_HEAP_BASE, 64)));
            if options.assume_main_argc_non_negative {
                if let Some(first_arg) = function.args.first() {
                    let slot = *function
                        .reg_slots
                        .get(&first_arg.name)
                        .expect("entry first arg register exists");
                    init_terms.push(format!(
                        "(bvsge (select regs {}) {})",
                        reg_slot_const(slot),
                        bv_const_u64(0, 64)
                    ));
                }
            }

            if let Some((lower, upper)) = options.first_arg_i32_range {
                if let Some(first_arg) = function.args.first() {
                    let slot = *function
                        .reg_slots
                        .get(&first_arg.name)
                        .expect("entry first arg register exists");
                    let lower_bits = lower as i64 as u64;
                    let upper_bits = upper as i64 as u64;
                    init_terms.push(format!(
                        "(bvsge (select regs {}) {})",
                        reg_slot_const(slot),
                        bv_const_u64(lower_bits, 64)
                    ));
                    init_terms.push(format!(
                        "(bvsle (select regs {}) {})",
                        reg_slot_const(slot),
                        bv_const_u64(upper_bits, 64)
                    ));
                }
            }
        }

        smt.push_str(&format!(
            "(rule (=> {} {}))\n\n",
            and_terms(init_terms),
            module_pc_relation_app(
                &module_pc_relation_name(function.id, 0),
                "regs",
                "mem",
                "heap",
                "exit",
                "pred",
                "in_regs",
                "in_mem",
                "in_heap",
            )
        ));

        for (pc, statement) in flat.iter().enumerate() {
            let from_rel = module_pc_relation_name(function.id, pc);
            let phi_guard = phi_guard_expr(statement, "pred", label_to_block_id);

            if let Some(user_call) = classify_user_call(statement, &context.functions) {
                let callee = context
                    .functions
                    .get(user_call.callee())
                    .expect("validated user callee exists");
                let call_regs_expr = build_callee_input_regs_expr(
                    callee,
                    user_call.args(),
                    "regs",
                    &function.reg_slots,
                    &context.global_map,
                )?;
                let ret_relation = module_ret_relation_name(callee.id);
                let abort_relation = module_abort_relation_name(callee.id);

                let mut return_terms = vec![format!("(= regs_call {call_regs_expr})")];
                return_terms.push(module_ret_relation_app(
                    &ret_relation,
                    "regs_call",
                    "mem",
                    "heap",
                    "ret_call",
                    "mem_call",
                    "heap_call",
                ));

                let regs_after_call =
                    regs_after_user_call(statement, "regs", &function.reg_slots, "ret_call")?;
                let call_transition = TransitionExprs {
                    regs_next: regs_after_call,
                    mem_next: "mem_call".to_string(),
                    heap_next: "heap_call".to_string(),
                    exit_next: "exit".to_string(),
                };

                if pc + 1 < flat.len() {
                    emit_module_transition_rule(
                        &mut smt,
                        &from_rel,
                        &module_pc_relation_name(function.id, pc + 1),
                        phi_guard.clone(),
                        return_terms,
                        &call_transition,
                        &pred_update_expr("pred", pc, pc + 1, pc_to_block_id),
                    );
                } else {
                    emit_module_return_rule(
                        &mut smt,
                        &from_rel,
                        &module_ret_relation_name(function.id),
                        phi_guard.clone(),
                        return_terms,
                        &call_transition.exit_next,
                        &call_transition.mem_next,
                        &call_transition.heap_next,
                    );
                }

                let mut abort_terms = vec![format!("(= regs_call {call_regs_expr})")];
                abort_terms.push(module_abort_relation_app(
                    &abort_relation,
                    "regs_call",
                    "mem",
                    "heap",
                    "code_call",
                    "mem_call",
                    "heap_call",
                ));
                emit_module_abort_rule(
                    &mut smt,
                    &from_rel,
                    &module_abort_relation_name(function.id),
                    phi_guard,
                    abort_terms,
                    "code_call",
                    "mem_call",
                    "heap_call",
                );
                continue;
            }

            let transition = TransitionExprs {
                regs_next: regs_update_expr(
                    statement,
                    "regs",
                    "mem",
                    "heap",
                    "pred",
                    &function.reg_slots,
                    &context.global_map,
                    label_to_block_id,
                ),
                mem_next: memory_update_expr(
                    statement,
                    "mem",
                    "regs",
                    &function.reg_slots,
                    &context.global_map,
                ),
                heap_next: heap_update_expr(
                    statement,
                    "heap",
                    "regs",
                    &function.reg_slots,
                    &context.global_map,
                ),
                exit_next: exit_update_expr(
                    statement,
                    "exit",
                    "regs",
                    &function.reg_slots,
                    &context.global_map,
                ),
            };

            match statement {
                QbeStatement::Volatile(QbeInstr::Jmp(target)) => {
                    let target_pc =
                        *label_to_pc
                            .get(target)
                            .ok_or_else(|| QbeSmtError::UnknownLabel {
                                label: target.clone(),
                            })?;
                    emit_module_transition_rule(
                        &mut smt,
                        &from_rel,
                        &module_pc_relation_name(function.id, target_pc),
                        phi_guard,
                        Vec::new(),
                        &transition,
                        &pred_from_block(pc, pc_to_block_id),
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

                    let cond_expr =
                        value_to_smt(cond, "regs", &function.reg_slots, &context.global_map);
                    emit_module_transition_rule(
                        &mut smt,
                        &from_rel,
                        &module_pc_relation_name(function.id, true_pc),
                        and_optional_guards(
                            phi_guard.clone(),
                            Some(format!("(distinct {} {})", cond_expr, bv_const_u64(0, 64))),
                        ),
                        Vec::new(),
                        &transition,
                        &pred_from_block(pc, pc_to_block_id),
                    );
                    emit_module_transition_rule(
                        &mut smt,
                        &from_rel,
                        &module_pc_relation_name(function.id, false_pc),
                        and_optional_guards(
                            phi_guard,
                            Some(format!("(= {} {})", cond_expr, bv_const_u64(0, 64))),
                        ),
                        Vec::new(),
                        &transition,
                        &pred_from_block(pc, pc_to_block_id),
                    );
                }
                QbeStatement::Volatile(QbeInstr::Ret(_))
                | QbeStatement::Volatile(QbeInstr::Hlt) => {
                    emit_module_return_rule(
                        &mut smt,
                        &from_rel,
                        &module_ret_relation_name(function.id),
                        phi_guard,
                        Vec::new(),
                        &transition.exit_next,
                        &transition.mem_next,
                        &transition.heap_next,
                    );
                }
                QbeStatement::Assign(_, _, QbeInstr::Call(function_name, _, _))
                | QbeStatement::Volatile(QbeInstr::Call(function_name, _, _))
                    if call_is_exit(function_name) =>
                {
                    emit_module_abort_rule(
                        &mut smt,
                        &from_rel,
                        &module_abort_relation_name(function.id),
                        phi_guard,
                        Vec::new(),
                        &transition.exit_next,
                        &transition.mem_next,
                        &transition.heap_next,
                    );
                }
                _ => {
                    if pc + 1 < flat.len() {
                        emit_module_transition_rule(
                            &mut smt,
                            &from_rel,
                            &module_pc_relation_name(function.id, pc + 1),
                            phi_guard,
                            Vec::new(),
                            &transition,
                            &pred_update_expr("pred", pc, pc + 1, pc_to_block_id),
                        );
                    } else {
                        emit_module_return_rule(
                            &mut smt,
                            &from_rel,
                            &module_ret_relation_name(function.id),
                            phi_guard,
                            Vec::new(),
                            &transition.exit_next,
                            &transition.mem_next,
                            &transition.heap_next,
                        );
                    }
                }
            }
        }
    }

    let entry_function = context
        .functions
        .get(&context.entry)
        .expect("entry metadata exists");

    smt.push('\n');
    smt.push_str(&format!(
        "(rule (=> (and {} (= exit {})) bad))\n",
        module_ret_relation_app(
            &module_ret_relation_name(entry_function.id),
            "regs",
            "mem",
            "heap",
            "exit",
            "mem_next",
            "heap_next",
        ),
        bv_const_u64(1, 64),
    ));
    smt.push_str(&format!(
        "(rule (=> (and {} (= exit {})) bad))\n",
        module_abort_relation_app(
            &module_abort_relation_name(entry_function.id),
            "regs",
            "mem",
            "heap",
            "exit",
            "mem_next",
            "heap_next",
        ),
        bv_const_u64(1, 64),
    ));
    smt.push_str("(query bad)\n");

    Ok(smt)
}

struct EncodedFunction {
    id: usize,
    name: String,
    args: Vec<FunctionArg>,
    flattened: FlattenedFunction,
    reg_list: Vec<String>,
    reg_slots: HashMap<String, u32>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct ValidatedArgInvariantAssumption {
    function_name: String,
    arg_index: usize,
    invariant_function_name: String,
}

struct ModuleEncodingContext {
    entry: String,
    function_order: Vec<String>,
    functions: HashMap<String, EncodedFunction>,
    global_map: HashMap<String, u64>,
    arg_invariant_assumptions: HashMap<String, Vec<ValidatedArgInvariantAssumption>>,
    max_arg_invariant_assumptions: usize,
}

fn build_module_encoding_context(
    module: &QbeModule,
    entry: &str,
    assumptions: &ModuleAssumptions,
) -> Result<ModuleEncodingContext, QbeSmtError> {
    let mut function_map = HashMap::<String, QbeFunction>::new();
    for function in &module.functions {
        if function_map
            .insert(function.name.clone(), function.clone())
            .is_some()
        {
            return Err(QbeSmtError::Unsupported {
                message: format!("duplicate function definition ${}", function.name),
            });
        }
    }

    if !function_map.contains_key(entry) {
        return Err(QbeSmtError::Unsupported {
            message: format!("entry function ${entry} is missing from module"),
        });
    }

    let mut all_typed_args = HashMap::<String, Vec<FunctionArg>>::new();
    for (name, function) in &function_map {
        all_typed_args.insert(name.clone(), collect_function_args(function)?);
    }

    let mut assumption_records = assumptions.arg_invariant_assumptions.clone();
    assumption_records.sort_by(|lhs, rhs| {
        lhs.function_name
            .cmp(&rhs.function_name)
            .then(lhs.arg_index.cmp(&rhs.arg_index))
            .then(
                lhs.invariant_function_name
                    .cmp(&rhs.invariant_function_name),
            )
    });

    let mut seen_assumptions = BTreeSet::<(String, usize, String)>::new();
    let mut assumptions_by_function =
        HashMap::<String, Vec<ValidatedArgInvariantAssumption>>::new();
    for assumption in assumption_records {
        let key = (
            assumption.function_name.clone(),
            assumption.arg_index,
            assumption.invariant_function_name.clone(),
        );
        if !seen_assumptions.insert(key) {
            continue;
        }
        validate_arg_invariant_assumption(&assumption, &all_typed_args)?;
        assumptions_by_function
            .entry(assumption.function_name.clone())
            .or_default()
            .push(ValidatedArgInvariantAssumption {
                function_name: assumption.function_name,
                arg_index: assumption.arg_index,
                invariant_function_name: assumption.invariant_function_name,
            });
    }
    for function_assumptions in assumptions_by_function.values_mut() {
        function_assumptions.sort_by(|lhs, rhs| {
            lhs.arg_index.cmp(&rhs.arg_index).then(
                lhs.invariant_function_name
                    .cmp(&rhs.invariant_function_name),
            )
        });
    }

    let mut reachable = HashSet::<String>::new();
    let mut worklist = VecDeque::<String>::from([entry.to_string()]);
    while let Some(function_name) = worklist.pop_front() {
        if !reachable.insert(function_name.clone()) {
            continue;
        }
        let function = function_map
            .get(&function_name)
            .expect("worklist function must exist");
        let callees = collect_reachable_user_callees(function, &function_map)?;
        for callee in callees {
            if !reachable.contains(&callee) {
                worklist.push_back(callee);
            }
        }
        if let Some(function_assumptions) = assumptions_by_function.get(&function_name) {
            for assumption in function_assumptions {
                if !reachable.contains(&assumption.invariant_function_name) {
                    worklist.push_back(assumption.invariant_function_name.clone());
                }
            }
        }
    }

    let mut function_order = reachable.into_iter().collect::<Vec<_>>();
    function_order.sort();

    let encoded_functions = function_order.iter().cloned().collect::<HashSet<_>>();
    for (function_name, function_assumptions) in &assumptions_by_function {
        if !encoded_functions.contains(function_name) {
            return Err(QbeSmtError::Unsupported {
                message: format!(
                    "arg-invariant assumption target function ${function_name} is not encoded from entry ${entry}"
                ),
            });
        }
        for assumption in function_assumptions {
            if !encoded_functions.contains(&assumption.invariant_function_name) {
                return Err(QbeSmtError::Unsupported {
                    message: format!(
                        "arg-invariant assumption target invariant function ${} is not encoded from entry ${entry}",
                        assumption.invariant_function_name
                    ),
                });
            }
        }
    }

    let mut user_arity = HashMap::<String, usize>::new();
    let mut typed_args = HashMap::<String, Vec<FunctionArg>>::new();
    for function_name in &function_order {
        let args = all_typed_args
            .get(function_name)
            .expect("reachable typed args exist")
            .clone();
        user_arity.insert(function_name.clone(), args.len());
        typed_args.insert(function_name.clone(), args);
    }

    let mut functions = HashMap::new();
    let mut globals = BTreeSet::<String>::new();
    for (function_id, function_name) in function_order.iter().enumerate() {
        let function = function_map
            .get(function_name)
            .expect("reachable function exists");
        let args = typed_args
            .get(function_name)
            .expect("typed args are populated")
            .clone();
        let flattened = flatten_reachable_statements(function)?;
        if flattened.statements.is_empty() {
            return Err(QbeSmtError::EmptyFunction);
        }

        for (pc, statement) in flattened.statements.iter().enumerate() {
            validate_statement_supported(
                statement,
                pc,
                &flattened.label_to_block_id,
                Some(&user_arity),
            )?;
        }

        let mut regs = BTreeSet::<String>::new();
        for arg in &args {
            regs.insert(arg.name.clone());
        }
        for statement in &flattened.statements {
            collect_regs_statement(statement, &mut regs);
        }

        let reg_list: Vec<String> = regs.into_iter().collect();
        let mut reg_slots = HashMap::<String, u32>::new();
        for (slot, name) in reg_list.iter().enumerate() {
            reg_slots.insert(name.clone(), slot as u32);
        }

        let arg_names = args
            .iter()
            .map(|arg| arg.name.clone())
            .collect::<HashSet<_>>();
        for statement in &flattened.statements {
            collect_globals_statement(statement, &mut globals);
        }
        for arg_name in arg_names {
            globals.remove(&arg_name);
        }

        functions.insert(
            function_name.clone(),
            EncodedFunction {
                id: function_id,
                name: function_name.clone(),
                args,
                flattened,
                reg_list,
                reg_slots,
            },
        );
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

    let mut encoded_arg_invariant_assumptions =
        HashMap::<String, Vec<ValidatedArgInvariantAssumption>>::new();
    let mut max_arg_invariant_assumptions = 0usize;
    for function_name in &function_order {
        let function_assumptions = assumptions_by_function
            .get(function_name)
            .cloned()
            .unwrap_or_default();
        if function_assumptions.len() > max_arg_invariant_assumptions {
            max_arg_invariant_assumptions = function_assumptions.len();
        }
        if !function_assumptions.is_empty() {
            encoded_arg_invariant_assumptions.insert(function_name.clone(), function_assumptions);
        }
    }

    Ok(ModuleEncodingContext {
        entry: entry.to_string(),
        function_order,
        functions,
        global_map,
        arg_invariant_assumptions: encoded_arg_invariant_assumptions,
        max_arg_invariant_assumptions,
    })
}

fn validate_arg_invariant_assumption(
    assumption: &FunctionArgInvariantAssumption,
    all_typed_args: &HashMap<String, Vec<FunctionArg>>,
) -> Result<(), QbeSmtError> {
    let Some(function_args) = all_typed_args.get(&assumption.function_name) else {
        return Err(QbeSmtError::Unsupported {
            message: format!(
                "arg-invariant assumption target function ${} is missing from module",
                assumption.function_name
            ),
        });
    };

    if assumption.arg_index >= function_args.len() {
        return Err(QbeSmtError::Unsupported {
            message: format!(
                "arg-invariant assumption target ${} argument index {} is out of range (arity={})",
                assumption.function_name,
                assumption.arg_index,
                function_args.len()
            ),
        });
    }

    let Some(invariant_args) = all_typed_args.get(&assumption.invariant_function_name) else {
        return Err(QbeSmtError::Unsupported {
            message: format!(
                "arg-invariant assumption invariant function ${} is missing from module",
                assumption.invariant_function_name
            ),
        });
    };

    if invariant_args.len() != 1 {
        return Err(QbeSmtError::Unsupported {
            message: format!(
                "arg-invariant assumption invariant function ${} must have arity 1, found {}",
                assumption.invariant_function_name,
                invariant_args.len()
            ),
        });
    }

    Ok(())
}

fn collect_reachable_user_callees(
    function: &QbeFunction,
    function_map: &HashMap<String, QbeFunction>,
) -> Result<BTreeSet<String>, QbeSmtError> {
    let mut out = BTreeSet::new();
    let reachable = reachable_block_indices(function)?;
    for block_idx in reachable {
        let block = &function.blocks[block_idx];
        for item in &block.items {
            let BlockItem::Statement(statement) = item else {
                continue;
            };
            let call_name = match statement {
                QbeStatement::Assign(_, _, QbeInstr::Call(name, _, _))
                | QbeStatement::Volatile(QbeInstr::Call(name, _, _)) => Some(name),
                _ => None,
            };
            if let Some(name) = call_name {
                if function_map.contains_key(name) {
                    out.insert(name.clone());
                }
            }
        }
    }
    Ok(out)
}

enum UserCallSite<'a> {
    Assign {
        callee: &'a str,
        args: &'a [(QbeType, QbeValue)],
    },
    Volatile {
        callee: &'a str,
        args: &'a [(QbeType, QbeValue)],
    },
}

impl<'a> UserCallSite<'a> {
    fn callee(&self) -> &'a str {
        match self {
            UserCallSite::Assign { callee, .. } | UserCallSite::Volatile { callee, .. } => callee,
        }
    }

    fn args(&self) -> &'a [(QbeType, QbeValue)] {
        match self {
            UserCallSite::Assign { args, .. } | UserCallSite::Volatile { args, .. } => args,
        }
    }
}

fn classify_user_call<'a>(
    statement: &'a QbeStatement,
    user_functions: &HashMap<String, EncodedFunction>,
) -> Option<UserCallSite<'a>> {
    match statement {
        QbeStatement::Assign(_, _, QbeInstr::Call(callee, args, _))
            if user_functions.contains_key(callee) =>
        {
            Some(UserCallSite::Assign {
                callee: callee.as_str(),
                args,
            })
        }
        QbeStatement::Volatile(QbeInstr::Call(callee, args, _))
            if user_functions.contains_key(callee) =>
        {
            Some(UserCallSite::Volatile {
                callee: callee.as_str(),
                args,
            })
        }
        _ => None,
    }
}

fn regs_after_user_call(
    statement: &QbeStatement,
    regs_curr: &str,
    reg_slots: &HashMap<String, u32>,
    ret_expr: &str,
) -> Result<String, QbeSmtError> {
    match statement {
        QbeStatement::Assign(QbeValue::Temporary(dest), ty, QbeInstr::Call(_, _, _)) => {
            let slot = *reg_slots
                .get(dest)
                .ok_or_else(|| QbeSmtError::Unsupported {
                    message: format!("missing destination register slot %{dest} for call result"),
                })?;
            let assign_ty = assign_type_from_qbe(ty);
            Ok(format!(
                "(store {regs_curr} {} {})",
                reg_slot_const(slot),
                normalize_to_assign_type(ret_expr, assign_ty),
            ))
        }
        QbeStatement::Volatile(QbeInstr::Call(_, _, _)) => Ok(regs_curr.to_string()),
        _ => Err(QbeSmtError::Unsupported {
            message: "internal error: expected call statement while updating call result"
                .to_string(),
        }),
    }
}

fn build_callee_input_regs_expr(
    callee: &EncodedFunction,
    args: &[(QbeType, QbeValue)],
    regs_curr: &str,
    caller_reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> Result<String, QbeSmtError> {
    if args.len() != callee.args.len() {
        return Err(QbeSmtError::Unsupported {
            message: format!(
                "call target ${} requires exactly {} argument(s), got {}",
                callee.name,
                callee.args.len(),
                args.len()
            ),
        });
    }

    let mut regs_expr = zero_regs_array_expr();
    for ((_, value), callee_arg) in args.iter().zip(callee.args.iter()) {
        let arg_expr = value_to_smt(value, regs_curr, caller_reg_slots, global_map);
        let normalized = normalize_to_assign_type(&arg_expr, callee_arg.ty);
        let slot =
            *callee
                .reg_slots
                .get(&callee_arg.name)
                .ok_or_else(|| QbeSmtError::Unsupported {
                    message: format!(
                        "missing callee argument register slot %{} for ${}",
                        callee_arg.name, callee.name
                    ),
                })?;
        regs_expr = format!("(store {regs_expr} {} {normalized})", reg_slot_const(slot));
    }
    Ok(regs_expr)
}

fn build_unary_callee_input_regs_expr(
    callee: &EncodedFunction,
    arg_expr: &str,
) -> Result<String, QbeSmtError> {
    if callee.args.len() != 1 {
        return Err(QbeSmtError::Unsupported {
            message: format!(
                "arg-invariant assumption target ${} must accept exactly one argument",
                callee.name
            ),
        });
    }

    let callee_arg = &callee.args[0];
    let slot = *callee
        .reg_slots
        .get(&callee_arg.name)
        .ok_or_else(|| QbeSmtError::Unsupported {
            message: format!(
                "missing callee argument register slot %{} for ${}",
                callee_arg.name, callee.name
            ),
        })?;
    let normalized = normalize_to_assign_type(arg_expr, callee_arg.ty);
    Ok(format!(
        "(store {} {} {normalized})",
        zero_regs_array_expr(),
        reg_slot_const(slot),
    ))
}

fn zero_regs_array_expr() -> String {
    format!(
        "((as const (Array (_ BitVec 32) (_ BitVec 64))) {})",
        bv_const_u64(0, 64)
    )
}

fn assumption_regs_var(index: usize) -> String {
    format!("regs_call_{index}")
}

fn assumption_mem_var(index: usize) -> String {
    format!("mem_call_{index}")
}

fn assumption_heap_var(index: usize) -> String {
    format!("heap_call_{index}")
}

fn assumption_ret_var(index: usize) -> String {
    format!("ret_call_{index}")
}

const REG_STATE_SORT: &str = "(Array (_ BitVec 32) (_ BitVec 64))";
const MEM_STATE_SORT: &str = "(Array (_ BitVec 64) (_ BitVec 8))";
const BV64_SORT: &str = "(_ BitVec 64)";
const BV32_SORT: &str = "(_ BitVec 32)";
const CLIB_CALL_INLINE_LIMIT: u64 = 16;

struct FlattenedFunction {
    statements: Vec<QbeStatement>,
    label_to_pc: HashMap<String, usize>,
    label_to_block_id: HashMap<String, u32>,
    pc_to_block_id: Vec<u32>,
}

fn flatten_reachable_statements(function: &QbeFunction) -> Result<FlattenedFunction, QbeSmtError> {
    let reachable_blocks = reachable_block_indices(function)?;
    let mut flat = Vec::<QbeStatement>::new();
    let mut label_to_pc = HashMap::<String, usize>::new();
    let mut label_to_block_id = HashMap::<String, u32>::new();
    let mut pc_to_block_id = Vec::<u32>::new();

    for (idx, block) in function.blocks.iter().enumerate() {
        if !reachable_blocks.contains(&idx) {
            continue;
        }
        if label_to_pc.contains_key(&block.label) {
            return Err(QbeSmtError::DuplicateLabel {
                label: block.label.clone(),
            });
        }
        if label_to_block_id.contains_key(&block.label) {
            return Err(QbeSmtError::DuplicateLabel {
                label: block.label.clone(),
            });
        }
        let block_id = idx as u32;
        label_to_block_id.insert(block.label.clone(), block_id);
        label_to_pc.insert(block.label.clone(), flat.len());
        for item in &block.items {
            if let BlockItem::Statement(statement) = item {
                flat.push(statement.clone());
                pc_to_block_id.push(block_id);
            }
        }
    }

    Ok(FlattenedFunction {
        statements: flat,
        label_to_pc,
        label_to_block_id,
        pc_to_block_id,
    })
}

fn reachable_block_indices(function: &QbeFunction) -> Result<BTreeSet<usize>, QbeSmtError> {
    let mut label_to_index = HashMap::<String, usize>::new();
    for (idx, block) in function.blocks.iter().enumerate() {
        if label_to_index.insert(block.label.clone(), idx).is_some() {
            return Err(QbeSmtError::DuplicateLabel {
                label: block.label.clone(),
            });
        }
    }

    let mut reachable = BTreeSet::new();
    let mut worklist = vec![0usize];

    while let Some(block_idx) = worklist.pop() {
        if block_idx >= function.blocks.len() || !reachable.insert(block_idx) {
            continue;
        }

        let block = &function.blocks[block_idx];
        let terminator = block.items.iter().rev().find_map(|item| {
            if let BlockItem::Statement(QbeStatement::Volatile(instr)) = item {
                Some(instr)
            } else {
                None
            }
        });

        match terminator {
            Some(QbeInstr::Jmp(target)) => {
                let next = label_to_index
                    .get(target)
                    .ok_or_else(|| QbeSmtError::UnknownLabel {
                        label: target.clone(),
                    })?;
                worklist.push(*next);
            }
            Some(QbeInstr::Jnz(_, if_true, if_false)) => {
                let next_true =
                    label_to_index
                        .get(if_true)
                        .ok_or_else(|| QbeSmtError::UnknownLabel {
                            label: if_true.clone(),
                        })?;
                let next_false =
                    label_to_index
                        .get(if_false)
                        .ok_or_else(|| QbeSmtError::UnknownLabel {
                            label: if_false.clone(),
                        })?;
                worklist.push(*next_true);
                worklist.push(*next_false);
            }
            Some(QbeInstr::Ret(_)) | Some(QbeInstr::Hlt) => {}
            _ => {
                if block_idx + 1 < function.blocks.len() {
                    worklist.push(block_idx + 1);
                }
            }
        }
    }

    Ok(reachable)
}

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

#[derive(Clone, Debug)]
struct FunctionArg {
    name: String,
    ty: AssignType,
}

struct TransitionExprs {
    regs_next: String,
    mem_next: String,
    heap_next: String,
    exit_next: String,
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

fn module_pc_relation_name(function_id: usize, pc: usize) -> String {
    format!("f{}_pc_{}", function_id, pc)
}

fn module_ret_relation_name(function_id: usize) -> String {
    format!("f{}_ret", function_id)
}

fn module_abort_relation_name(function_id: usize) -> String {
    format!("f{}_abort", function_id)
}

fn module_pc_relation_app(
    relation: &str,
    regs: &str,
    mem: &str,
    heap: &str,
    exit: &str,
    pred: &str,
    in_regs: &str,
    in_mem: &str,
    in_heap: &str,
) -> String {
    format!("({relation} {regs} {mem} {heap} {exit} {pred} {in_regs} {in_mem} {in_heap})")
}

fn module_ret_relation_app(
    relation: &str,
    in_regs: &str,
    in_mem: &str,
    in_heap: &str,
    ret: &str,
    mem_out: &str,
    heap_out: &str,
) -> String {
    format!("({relation} {in_regs} {in_mem} {in_heap} {ret} {mem_out} {heap_out})")
}

fn module_abort_relation_app(
    relation: &str,
    in_regs: &str,
    in_mem: &str,
    in_heap: &str,
    code: &str,
    mem_out: &str,
    heap_out: &str,
) -> String {
    format!("({relation} {in_regs} {in_mem} {in_heap} {code} {mem_out} {heap_out})")
}

fn emit_module_transition_rule(
    smt: &mut String,
    from_relation: &str,
    to_relation: &str,
    guard: Option<String>,
    mut extra_terms: Vec<String>,
    next: &TransitionExprs,
    pred_next_expr: &str,
) {
    let mut body_terms = vec![module_pc_relation_app(
        from_relation,
        "regs",
        "mem",
        "heap",
        "exit",
        "pred",
        "in_regs",
        "in_mem",
        "in_heap",
    )];
    if let Some(guard) = guard {
        body_terms.push(guard);
    }
    body_terms.append(&mut extra_terms);
    body_terms.push(format!("(= regs_next {})", next.regs_next));
    body_terms.push(format!("(= mem_next {})", next.mem_next));
    body_terms.push(format!("(= heap_next {})", next.heap_next));
    body_terms.push(format!("(= exit_next {})", next.exit_next));
    body_terms.push(format!("(= pred_next {pred_next_expr})"));

    let body = and_terms(body_terms);
    let head = module_pc_relation_app(
        to_relation,
        "regs_next",
        "mem_next",
        "heap_next",
        "exit_next",
        "pred_next",
        "in_regs",
        "in_mem",
        "in_heap",
    );

    smt.push_str(&format!("(rule (=> {body} {head}))\n"));
}

fn emit_module_return_rule(
    smt: &mut String,
    from_relation: &str,
    to_relation: &str,
    guard: Option<String>,
    mut extra_terms: Vec<String>,
    ret_expr: &str,
    mem_expr: &str,
    heap_expr: &str,
) {
    let mut body_terms = vec![module_pc_relation_app(
        from_relation,
        "regs",
        "mem",
        "heap",
        "exit",
        "pred",
        "in_regs",
        "in_mem",
        "in_heap",
    )];
    if let Some(guard) = guard {
        body_terms.push(guard);
    }
    body_terms.append(&mut extra_terms);
    if ret_expr != "ret_call" {
        body_terms.push(format!("(= ret_call {ret_expr})"));
    }
    if mem_expr != "mem_call" {
        body_terms.push(format!("(= mem_call {mem_expr})"));
    }
    if heap_expr != "heap_call" {
        body_terms.push(format!("(= heap_call {heap_expr})"));
    }

    let body = and_terms(body_terms);
    let head = module_ret_relation_app(
        to_relation,
        "in_regs",
        "in_mem",
        "in_heap",
        "ret_call",
        "mem_call",
        "heap_call",
    );

    smt.push_str(&format!("(rule (=> {body} {head}))\n"));
}

fn emit_module_abort_rule(
    smt: &mut String,
    from_relation: &str,
    to_relation: &str,
    guard: Option<String>,
    mut extra_terms: Vec<String>,
    code_expr: &str,
    mem_expr: &str,
    heap_expr: &str,
) {
    let mut body_terms = vec![module_pc_relation_app(
        from_relation,
        "regs",
        "mem",
        "heap",
        "exit",
        "pred",
        "in_regs",
        "in_mem",
        "in_heap",
    )];
    if let Some(guard) = guard {
        body_terms.push(guard);
    }
    body_terms.append(&mut extra_terms);
    if code_expr != "code_call" {
        body_terms.push(format!("(= code_call {code_expr})"));
    }
    if mem_expr != "mem_call" {
        body_terms.push(format!("(= mem_call {mem_expr})"));
    }
    if heap_expr != "heap_call" {
        body_terms.push(format!("(= heap_call {heap_expr})"));
    }

    let body = and_terms(body_terms);
    let head = module_abort_relation_app(
        to_relation,
        "in_regs",
        "in_mem",
        "in_heap",
        "code_call",
        "mem_call",
        "heap_call",
    );

    smt.push_str(&format!("(rule (=> {body} {head}))\n"));
}

fn and_optional_guards(lhs: Option<String>, rhs: Option<String>) -> Option<String> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => Some(format!("(and {lhs} {rhs})")),
        (Some(lhs), None) => Some(lhs),
        (None, Some(rhs)) => Some(rhs),
        (None, None) => None,
    }
}

fn pred_update_expr(
    pred_curr: &str,
    from_pc: usize,
    to_pc: usize,
    pc_to_block_id: &[u32],
) -> String {
    let from_block = pc_to_block_id[from_pc];
    let to_block = pc_to_block_id[to_pc];
    if from_block == to_block {
        pred_curr.to_string()
    } else {
        bv_const_u64(from_block as u64, 32)
    }
}

fn pred_from_block(from_pc: usize, pc_to_block_id: &[u32]) -> String {
    let from_block = pc_to_block_id[from_pc];
    bv_const_u64(from_block as u64, 32)
}

fn phi_guard_expr(
    statement: &QbeStatement,
    pred_curr: &str,
    label_to_block_id: &HashMap<String, u32>,
) -> Option<String> {
    let QbeStatement::Assign(_, _, QbeInstr::Phi(label_left, _, label_right, _)) = statement else {
        return None;
    };

    let left_id = *label_to_block_id
        .get(label_left)
        .expect("phi predecessor labels are validated");
    let right_id = *label_to_block_id
        .get(label_right)
        .expect("phi predecessor labels are validated");
    Some(format!(
        "(or (= {pred_curr} {}) (= {pred_curr} {}))",
        bv_const_u64(left_id as u64, 32),
        bv_const_u64(right_id as u64, 32)
    ))
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

        out.push(FunctionArg {
            name: name.clone(),
            ty: assign_ty,
        });
    }

    Ok(out)
}

fn validate_statement_supported(
    statement: &QbeStatement,
    pc: usize,
    label_to_block_id: &HashMap<String, u32>,
    user_call_arity: Option<&HashMap<String, usize>>,
) -> Result<(), QbeSmtError> {
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
                    if matches!(
                        kind,
                        QbeCmp::O | QbeCmp::Uo | QbeCmp::Lt | QbeCmp::Le | QbeCmp::Gt | QbeCmp::Ge
                    ) || matches!(assign_ty, AssignType::Single | AssignType::Double)
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
                QbeInstr::Call(function, args, variadic_index) => {
                    validate_call_supported(
                        function,
                        args,
                        *variadic_index,
                        pc,
                        true,
                        user_call_arity,
                    )?;
                }
                QbeInstr::Phi(label_left, _, label_right, _) => {
                    if matches!(assign_ty, AssignType::Single | AssignType::Double) {
                        return Err(QbeSmtError::Unsupported {
                            message: format!(
                                "pc {pc}: phi is unsupported for floating-point assignment type {:?}",
                                assign_ty
                            ),
                        });
                    }
                    if !label_to_block_id.contains_key(label_left) {
                        return Err(QbeSmtError::UnknownLabel {
                            label: label_left.clone(),
                        });
                    }
                    if !label_to_block_id.contains_key(label_right) {
                        return Err(QbeSmtError::UnknownLabel {
                            label: label_right.clone(),
                        });
                    }
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
            QbeInstr::Call(function, args, variadic_index) => {
                validate_call_supported(
                    function,
                    args,
                    *variadic_index,
                    pc,
                    false,
                    user_call_arity,
                )?;
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

fn validate_call_supported(
    function: &str,
    args: &[(QbeType, QbeValue)],
    variadic_index: Option<u64>,
    pc: usize,
    in_assignment: bool,
    user_call_arity: Option<&HashMap<String, usize>>,
) -> Result<(), QbeSmtError> {
    if let Some(user_call_arity) = user_call_arity {
        if let Some(expected) = user_call_arity.get(function) {
            if variadic_index.is_some() {
                return Err(QbeSmtError::Unsupported {
                    message: format!(
                        "pc {pc}: variadic user call target ${function} is unsupported"
                    ),
                });
            }
            if args.len() != *expected {
                return Err(QbeSmtError::Unsupported {
                    message: format!(
                        "pc {pc}: call target ${function} requires exactly {expected} argument(s), got {}",
                        args.len()
                    ),
                });
            }
            return Ok(());
        }
    }

    let Some(model) = extern_call_model(function) else {
        return Err(QbeSmtError::Unsupported {
            message: format!("pc {pc}: unsupported call target ${function}"),
        });
    };

    if model == ExternCallModel::Printf {
        if variadic_index.is_none() {
            return Err(QbeSmtError::Unsupported {
                message: format!("pc {pc}: call target $printf must be variadic"),
            });
        }
        if args.is_empty() {
            return Err(QbeSmtError::Unsupported {
                message: format!("pc {pc}: call target $printf requires at least one argument"),
            });
        }
    } else if variadic_index.is_some() {
        return Err(QbeSmtError::Unsupported {
            message: format!("pc {pc}: variadic call target ${function} is unsupported"),
        });
    }

    if model == ExternCallModel::Exit && args.is_empty() {
        return Err(QbeSmtError::Unsupported {
            message: format!("pc {pc}: call target $exit requires one argument"),
        });
    }

    if args.len() < model.min_arity() {
        return Err(QbeSmtError::Unsupported {
            message: format!(
                "pc {pc}: call target ${function} requires at least {} argument(s), got {}",
                model.min_arity(),
                args.len()
            ),
        });
    }
    if let Some(exact) = model.exact_arity() {
        if args.len() != exact {
            return Err(QbeSmtError::Unsupported {
                message: format!(
                    "pc {pc}: call target ${function} requires exactly {exact} argument(s), got {}",
                    args.len()
                ),
            });
        }
    }

    if model == ExternCallModel::Exit && in_assignment {
        return Err(QbeSmtError::Unsupported {
            message: format!("pc {pc}: call target $exit is unsupported in assignments"),
        });
    }

    Ok(())
}

fn regs_update_expr(
    statement: &QbeStatement,
    regs_curr: &str,
    mem_curr: &str,
    heap_curr: &str,
    pred_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
    label_to_block_id: &HashMap<String, u32>,
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
        QbeInstr::Call(function, args, _) => call_assign_result_expr(
            extern_call_model(function).expect("call model should be validated"),
            args,
            assign_ty,
            slot,
            regs_curr,
            mem_curr,
            heap_curr,
            reg_slots,
            global_map,
        ),
        QbeInstr::Phi(label_left, left_value, label_right, right_value) => {
            let left_expr = normalize_to_assign_type(
                &value_to_smt(left_value, regs_curr, reg_slots, global_map),
                assign_ty,
            );
            let right_expr = normalize_to_assign_type(
                &value_to_smt(right_value, regs_curr, reg_slots, global_map),
                assign_ty,
            );
            let left_block = *label_to_block_id
                .get(label_left)
                .expect("phi predecessor labels are validated");
            let right_block = *label_to_block_id
                .get(label_right)
                .expect("phi predecessor labels are validated");
            let pred_is_left = format!("(= {pred_curr} {})", bv_const_u64(left_block as u64, 32));
            let pred_is_right = format!("(= {pred_curr} {})", bv_const_u64(right_block as u64, 32));
            format!(
                "(ite {pred_is_left} {left_expr} (ite {pred_is_right} {right_expr} {}))",
                bv_const_u64(0, 64)
            )
        }
        _ => {
            unreachable!("unsupported instructions should be rejected before transition generation")
        }
    };

    format!("(store {regs_curr} {} {value_expr})", reg_slot_const(slot))
}

fn call_assign_result_expr(
    model: ExternCallModel,
    args: &[(QbeType, QbeValue)],
    assign_ty: AssignType,
    dest_slot: u32,
    regs_curr: &str,
    mem_curr: &str,
    heap_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> String {
    let unknown_result = unconstrained_assign_value_expr(assign_ty, dest_slot, "regs_next");

    match model {
        ExternCallModel::Malloc | ExternCallModel::Calloc => {
            normalize_to_assign_type(heap_curr, assign_ty)
        }
        ExternCallModel::Realloc => {
            let ptr_expr = call_arg_expr(args, 0, regs_curr, reg_slots, global_map)
                .unwrap_or_else(|| bv_const_u64(0, 64));
            let malloc_like_result = normalize_to_assign_type(heap_curr, assign_ty);
            format!(
                "(ite (= {ptr_expr} {}) {malloc_like_result} {unknown_result})",
                bv_const_u64(0, 64),
            )
        }
        ExternCallModel::Memcpy
        | ExternCallModel::Memmove
        | ExternCallModel::Memset
        | ExternCallModel::Strcpy
        | ExternCallModel::Strncpy => call_arg_expr(args, 0, regs_curr, reg_slots, global_map)
            .map(|dest| normalize_to_assign_type(&dest, assign_ty))
            .unwrap_or(unknown_result),
        ExternCallModel::Memcmp => {
            let Some(left_expr) = call_arg_expr(args, 0, regs_curr, reg_slots, global_map) else {
                return unknown_result;
            };
            let Some(right_expr) = call_arg_expr(args, 1, regs_curr, reg_slots, global_map) else {
                return unknown_result;
            };
            let Some(len_expr) = call_arg_expr(args, 2, regs_curr, reg_slots, global_map) else {
                return unknown_result;
            };
            let cmp_expr = bounded_memcmp_result_with_fallback_expr(
                mem_curr,
                &left_expr,
                &right_expr,
                &len_expr,
                CLIB_CALL_INLINE_LIMIT,
                &unknown_result,
            );
            normalize_to_assign_type(&cmp_expr, assign_ty)
        }
        ExternCallModel::Exit
        | ExternCallModel::Free
        | ExternCallModel::Strlen
        | ExternCallModel::Strcmp
        | ExternCallModel::Open
        | ExternCallModel::Read
        | ExternCallModel::Write
        | ExternCallModel::Close
        | ExternCallModel::Printf => unknown_result,
    }
}

fn unconstrained_assign_value_expr(assign_ty: AssignType, slot: u32, regs_next: &str) -> String {
    let self_ref = format!("(select {regs_next} {})", reg_slot_const(slot));
    normalize_to_assign_type(&self_ref, assign_ty)
}

fn call_arg_expr(
    args: &[(QbeType, QbeValue)],
    index: usize,
    regs_curr: &str,
    reg_slots: &HashMap<String, u32>,
    global_map: &HashMap<String, u64>,
) -> Option<String> {
    args.get(index)
        .map(|(_, value)| value_to_smt(value, regs_curr, reg_slots, global_map))
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
        QbeStatement::Assign(_, _, QbeInstr::Call(function, args, _))
        | QbeStatement::Volatile(QbeInstr::Call(function, args, _)) => {
            match extern_call_model(function).expect("call model should be validated") {
                ExternCallModel::Memcpy | ExternCallModel::Memmove => {
                    let Some(dst_expr) = call_arg_expr(args, 0, regs_curr, reg_slots, global_map)
                    else {
                        return "mem_next".to_string();
                    };
                    let Some(src_expr) = call_arg_expr(args, 1, regs_curr, reg_slots, global_map)
                    else {
                        return "mem_next".to_string();
                    };
                    let Some(len_expr) = call_arg_expr(args, 2, regs_curr, reg_slots, global_map)
                    else {
                        return "mem_next".to_string();
                    };
                    bounded_copy_with_fallback_expr(
                        mem_curr,
                        &src_expr,
                        &dst_expr,
                        &len_expr,
                        CLIB_CALL_INLINE_LIMIT,
                        "mem_next",
                    )
                }
                ExternCallModel::Memset => {
                    let Some(dst_expr) = call_arg_expr(args, 0, regs_curr, reg_slots, global_map)
                    else {
                        return "mem_next".to_string();
                    };
                    let Some(fill_expr) = call_arg_expr(args, 1, regs_curr, reg_slots, global_map)
                    else {
                        return "mem_next".to_string();
                    };
                    let Some(len_expr) = call_arg_expr(args, 2, regs_curr, reg_slots, global_map)
                    else {
                        return "mem_next".to_string();
                    };
                    let byte_expr = extract_low_bits(&fill_expr, 8);
                    bounded_set_with_fallback_expr(
                        mem_curr,
                        &dst_expr,
                        &len_expr,
                        &byte_expr,
                        CLIB_CALL_INLINE_LIMIT,
                        "mem_next",
                    )
                }
                ExternCallModel::Calloc => {
                    let Some(nmemb_expr) = call_arg_expr(args, 0, regs_curr, reg_slots, global_map)
                    else {
                        return "mem_next".to_string();
                    };
                    let Some(size_expr) = call_arg_expr(args, 1, regs_curr, reg_slots, global_map)
                    else {
                        return "mem_next".to_string();
                    };
                    let total_expr = format!("(bvmul {nmemb_expr} {size_expr})");
                    bounded_set_with_fallback_expr(
                        mem_curr,
                        "heap",
                        &total_expr,
                        &bv_const_u64(0, 8),
                        CLIB_CALL_INLINE_LIMIT,
                        "mem_next",
                    )
                }
                ExternCallModel::Realloc => {
                    let ptr_expr = call_arg_expr(args, 0, regs_curr, reg_slots, global_map)
                        .unwrap_or_else(|| bv_const_u64(0, 64));
                    format!(
                        "(ite (= {ptr_expr} {}) {mem_curr} mem_next)",
                        bv_const_u64(0, 64)
                    )
                }
                ExternCallModel::Read => {
                    let Some(buf_expr) = call_arg_expr(args, 1, regs_curr, reg_slots, global_map)
                    else {
                        return "mem_next".to_string();
                    };
                    let Some(count_expr) = call_arg_expr(args, 2, regs_curr, reg_slots, global_map)
                    else {
                        return "mem_next".to_string();
                    };
                    bounded_havoc_with_fallback_expr(
                        mem_curr,
                        &buf_expr,
                        &count_expr,
                        CLIB_CALL_INLINE_LIMIT,
                        "mem_next",
                    )
                }
                ExternCallModel::Strncpy => {
                    let Some(dst_expr) = call_arg_expr(args, 0, regs_curr, reg_slots, global_map)
                    else {
                        return "mem_next".to_string();
                    };
                    let Some(count_expr) = call_arg_expr(args, 2, regs_curr, reg_slots, global_map)
                    else {
                        return "mem_next".to_string();
                    };
                    bounded_havoc_with_fallback_expr(
                        mem_curr,
                        &dst_expr,
                        &count_expr,
                        CLIB_CALL_INLINE_LIMIT,
                        "mem_next",
                    )
                }
                ExternCallModel::Strcpy => "mem_next".to_string(),
                ExternCallModel::Malloc
                | ExternCallModel::Free
                | ExternCallModel::Memcmp
                | ExternCallModel::Strlen
                | ExternCallModel::Strcmp
                | ExternCallModel::Open
                | ExternCallModel::Write
                | ExternCallModel::Close
                | ExternCallModel::Exit
                | ExternCallModel::Printf => mem_curr.to_string(),
            }
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
            match extern_call_model(function).expect("call model should be validated") {
                ExternCallModel::Malloc => {
                    let size_expr = call_arg_expr(args, 0, regs_curr, reg_slots, global_map)
                        .unwrap_or_else(|| bv_const_u64(8, 64));
                    format!("(bvadd {heap_curr} {})", non_zero_size_expr(&size_expr))
                }
                ExternCallModel::Calloc => {
                    let nmemb_expr = call_arg_expr(args, 0, regs_curr, reg_slots, global_map)
                        .unwrap_or_else(|| bv_const_u64(0, 64));
                    let size_expr = call_arg_expr(args, 1, regs_curr, reg_slots, global_map)
                        .unwrap_or_else(|| bv_const_u64(0, 64));
                    let total_expr = format!("(bvmul {nmemb_expr} {size_expr})");
                    format!("(bvadd {heap_curr} {})", non_zero_size_expr(&total_expr))
                }
                ExternCallModel::Realloc => {
                    let ptr_expr = call_arg_expr(args, 0, regs_curr, reg_slots, global_map)
                        .unwrap_or_else(|| bv_const_u64(0, 64));
                    let size_expr = call_arg_expr(args, 1, regs_curr, reg_slots, global_map)
                        .unwrap_or_else(|| bv_const_u64(8, 64));
                    let realloc_malloc =
                        format!("(bvadd {heap_curr} {})", non_zero_size_expr(&size_expr));
                    format!(
                        "(ite (= {ptr_expr} {}) {realloc_malloc} heap_next)",
                        bv_const_u64(0, 64)
                    )
                }
                ExternCallModel::Exit
                | ExternCallModel::Free
                | ExternCallModel::Memcpy
                | ExternCallModel::Memmove
                | ExternCallModel::Memset
                | ExternCallModel::Memcmp
                | ExternCallModel::Strlen
                | ExternCallModel::Strcmp
                | ExternCallModel::Strcpy
                | ExternCallModel::Strncpy
                | ExternCallModel::Open
                | ExternCallModel::Read
                | ExternCallModel::Write
                | ExternCallModel::Close
                | ExternCallModel::Printf => heap_curr.to_string(),
            }
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
        QbeStatement::Assign(_, _, QbeInstr::Call(function, args, _))
        | QbeStatement::Volatile(QbeInstr::Call(function, args, _)) => {
            if extern_call_model(function) == Some(ExternCallModel::Exit) {
                if let Some((_, code)) = args.first() {
                    value_to_smt(code, regs_curr, reg_slots, global_map)
                } else {
                    bv_const_u64(0, 64)
                }
            } else {
                exit_curr.to_string()
            }
        }
        _ => exit_curr.to_string(),
    }
}

fn non_zero_size_expr(size_expr: &str) -> String {
    format!(
        "(ite (= {size_expr} {}) {} {size_expr})",
        bv_const_u64(0, 64),
        bv_const_u64(1, 64)
    )
}

fn bounded_copy_with_fallback_expr(
    mem_curr: &str,
    src_expr: &str,
    dst_expr: &str,
    len_expr: &str,
    limit: u64,
    mem_fallback: &str,
) -> String {
    let precise = bounded_copy_expr(mem_curr, src_expr, dst_expr, len_expr, limit);
    format!(
        "(ite (bvule {len_expr} {}) {precise} {mem_fallback})",
        bv_const_u64(limit, 64)
    )
}

fn bounded_copy_expr(
    mem_curr: &str,
    src_expr: &str,
    dst_expr: &str,
    len_expr: &str,
    limit: u64,
) -> String {
    let mut acc = mem_curr.to_string();
    for i in 0..limit {
        let index_expr = bv_const_u64(i, 64);
        let cond = format!("(bvugt {len_expr} {index_expr})");
        let src_i = format!("(bvadd {src_expr} {index_expr})");
        let dst_i = format!("(bvadd {dst_expr} {index_expr})");
        let byte_i = format!("(select {mem_curr} {src_i})");
        let write_i = format!("(store {acc} {dst_i} {byte_i})");
        acc = format!("(ite {cond} {write_i} {acc})");
    }
    acc
}

fn bounded_set_with_fallback_expr(
    mem_curr: &str,
    dst_expr: &str,
    len_expr: &str,
    byte_expr: &str,
    limit: u64,
    mem_fallback: &str,
) -> String {
    let precise = bounded_set_expr(mem_curr, dst_expr, len_expr, byte_expr, limit);
    format!(
        "(ite (bvule {len_expr} {}) {precise} {mem_fallback})",
        bv_const_u64(limit, 64)
    )
}

fn bounded_set_expr(
    mem_curr: &str,
    dst_expr: &str,
    len_expr: &str,
    byte_expr: &str,
    limit: u64,
) -> String {
    let mut acc = mem_curr.to_string();
    for i in 0..limit {
        let index_expr = bv_const_u64(i, 64);
        let cond = format!("(bvugt {len_expr} {index_expr})");
        let dst_i = format!("(bvadd {dst_expr} {index_expr})");
        let write_i = format!("(store {acc} {dst_i} {byte_expr})");
        acc = format!("(ite {cond} {write_i} {acc})");
    }
    acc
}

fn bounded_havoc_with_fallback_expr(
    mem_curr: &str,
    dst_expr: &str,
    len_expr: &str,
    limit: u64,
    mem_fallback: &str,
) -> String {
    let precise = bounded_havoc_expr(mem_curr, dst_expr, len_expr, limit, mem_fallback);
    format!(
        "(ite (bvule {len_expr} {}) {precise} {mem_fallback})",
        bv_const_u64(limit, 64)
    )
}

fn bounded_havoc_expr(
    mem_curr: &str,
    dst_expr: &str,
    len_expr: &str,
    limit: u64,
    mem_havoc_source: &str,
) -> String {
    let mut acc = mem_curr.to_string();
    for i in 0..limit {
        let index_expr = bv_const_u64(i, 64);
        let cond = format!("(bvugt {len_expr} {index_expr})");
        let dst_i = format!("(bvadd {dst_expr} {index_expr})");
        let havoc_byte = format!("(select {mem_havoc_source} {dst_i})");
        let write_i = format!("(store {acc} {dst_i} {havoc_byte})");
        acc = format!("(ite {cond} {write_i} {acc})");
    }
    acc
}

fn bounded_memcmp_result_with_fallback_expr(
    mem_curr: &str,
    left_expr: &str,
    right_expr: &str,
    len_expr: &str,
    limit: u64,
    fallback: &str,
) -> String {
    let precise = bounded_memcmp_result_expr(mem_curr, left_expr, right_expr, len_expr, limit);
    format!(
        "(ite (bvule {len_expr} {}) {precise} {fallback})",
        bv_const_u64(limit, 64)
    )
}

fn bounded_memcmp_result_expr(
    mem_curr: &str,
    left_expr: &str,
    right_expr: &str,
    len_expr: &str,
    limit: u64,
) -> String {
    let mut all_equal = "true".to_string();
    for i in 0..limit {
        let index_expr = bv_const_u64(i, 64);
        let cond = format!("(bvugt {len_expr} {index_expr})");
        let left_i = format!("(bvadd {left_expr} {index_expr})");
        let right_i = format!("(bvadd {right_expr} {index_expr})");
        let bytes_equal = format!("(= (select {mem_curr} {left_i}) (select {mem_curr} {right_i}))");
        all_equal = format!("(and {all_equal} (ite {cond} {bytes_equal} true))");
    }
    format!(
        "(ite {all_equal} {} {})",
        bv_const_u64(0, 64),
        bv_const_u64(1, 64)
    )
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
        QbeCmp::Lt | QbeCmp::Le | QbeCmp::Gt | QbeCmp::Ge => {
            unreachable!("floating-point compares should be rejected")
        }
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
        QbeValue::SingleConst(_) => {
            unreachable!("floating-point constants should be rejected")
        }
        QbeValue::DoubleConst(_) => {
            unreachable!("floating-point constants should be rejected")
        }
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
