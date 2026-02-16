use qbe::Function as QbeFunction;
use thiserror::Error;

mod classify;
mod encode;

pub use classify::{LoopProof, LoopProofStatus};

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

/// Errors produced by the encoder/classifier.
#[derive(Debug, Error)]
pub enum QbeSmtError {
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
pub fn qbe_to_smt(function: &QbeFunction, options: &EncodeOptions) -> Result<String, QbeSmtError> {
    encode::encode_function(function, options)
}

/// Classify simple loops in a single QBE function body.
pub fn classify_simple_loops(function: &QbeFunction) -> Result<Vec<LoopProof>, QbeSmtError> {
    classify::classify_simple_loops_in_function(function)
}

pub(crate) const BLIT_INLINE_LIMIT: u64 = 64;
pub(crate) const INITIAL_HEAP_BASE: u64 = 0x0010_0000;
pub(crate) const GLOBAL_BASE: u64 = 0x4000_0000;
pub(crate) const GLOBAL_STRIDE: u64 = 0x1000;

#[cfg(test)]
mod tests {
    use qbe::{Block, BlockItem, Cmp, Function, Instr, Linkage, Statement, Type, Value};

    use super::{classify_simple_loops, qbe_to_smt, EncodeOptions, LoopProofStatus};

    fn temp(name: &str) -> Value {
        Value::Temporary(name.to_string())
    }

    fn assign(dest: &str, ty: Type, instr: Instr) -> Statement {
        Statement::Assign(temp(dest), ty, instr)
    }

    fn volatile(instr: Instr) -> Statement {
        Statement::Volatile(instr)
    }

    fn block(label: &str, statements: Vec<Statement>) -> Block {
        Block {
            label: label.to_string(),
            items: statements
                .into_iter()
                .map(BlockItem::Statement)
                .collect::<Vec<_>>(),
        }
    }

    fn make_main(arguments: Vec<(Type, Value)>, blocks: Vec<Block>) -> Function {
        Function {
            linkage: Linkage::default(),
            name: "main".to_string(),
            arguments,
            return_ty: Some(Type::Word),
            blocks,
        }
    }

    #[test]
    fn emits_horn_script_with_bad_query() {
        let function = make_main(
            vec![(Type::Word, temp("x"))],
            vec![block(
                "start",
                vec![
                    assign("y", Type::Word, Instr::Add(temp("x"), Value::Const(1))),
                    volatile(Instr::Ret(Some(temp("y")))),
                ],
            )],
        );

        let smt = qbe_to_smt(
            &function,
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
        let function = make_main(
            vec![(Type::Word, temp("x"))],
            vec![
                block(
                    "entry",
                    vec![volatile(Instr::Jnz(
                        temp("x"),
                        "then".to_string(),
                        "else".to_string(),
                    ))],
                ),
                block("then", vec![volatile(Instr::Ret(Some(Value::Const(1))))]),
                block("else", vec![volatile(Instr::Ret(Some(Value::Const(0))))]),
            ],
        );

        let smt = qbe_to_smt(
            &function,
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
        let function = make_main(
            vec![(Type::Word, temp("x"))],
            vec![
                block("entry", vec![volatile(Instr::Jmp("loop".to_string()))]),
                block(
                    "loop",
                    vec![
                        assign("x", Type::Word, Instr::Sub(temp("x"), Value::Const(1))),
                        volatile(Instr::Jnz(
                            temp("x"),
                            "loop".to_string(),
                            "done".to_string(),
                        )),
                    ],
                ),
                block("done", vec![volatile(Instr::Ret(Some(Value::Const(0))))]),
            ],
        );

        let smt = qbe_to_smt(
            &function,
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
        let function = make_main(
            vec![(Type::Word, temp("x"))],
            vec![block(
                "entry",
                vec![
                    assign("p", Type::Long, Instr::Alloc8(8)),
                    volatile(Instr::Store(Type::Word, temp("p"), temp("x"))),
                    assign("y", Type::Word, Instr::Load(Type::Word, temp("p"))),
                    volatile(Instr::Ret(Some(temp("y")))),
                ],
            )],
        );

        let smt = qbe_to_smt(
            &function,
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
        let function = make_main(
            vec![(Type::Word, temp("argc")), (Type::Long, temp("argv"))],
            vec![block(
                "entry",
                vec![volatile(Instr::Ret(Some(temp("argc"))))],
            )],
        );

        let smt = qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: true,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(bvsge (select regs (_ bv0 32)) (_ bv0 64))"));
    }

    #[test]
    fn rejects_missing_labels() {
        let function = make_main(
            vec![(Type::Word, temp("x"))],
            vec![block(
                "entry",
                vec![volatile(Instr::Jmp("missing".to_string()))],
            )],
        );

        let err = qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
            },
        )
        .expect_err("should fail");
        assert!(err.to_string().contains("unknown label @missing"));
    }

    #[test]
    fn rejects_unsupported_calls() {
        let function = make_main(
            vec![(Type::Word, temp("x"))],
            vec![block(
                "entry",
                vec![
                    assign(
                        "y",
                        Type::Word,
                        Instr::Call("foo".to_string(), vec![(Type::Word, temp("x"))], None),
                    ),
                    volatile(Instr::Ret(Some(temp("y")))),
                ],
            )],
        );

        let err = qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
            },
        )
        .expect_err("unsupported call should fail");
        assert!(err.to_string().contains("unsupported call target $foo"));
    }

    #[test]
    fn rejects_unknown_assignment_operations() {
        let function = make_main(
            vec![],
            vec![block(
                "entry",
                vec![
                    assign("x", Type::Word, Instr::Exts(Value::Const(2))),
                    volatile(Instr::Ret(Some(temp("x")))),
                ],
            )],
        );

        let err = qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
            },
        )
        .expect_err("unsupported op should fail");

        assert!(err.to_string().contains("unsupported unary operation exts"));
    }

    #[test]
    fn classifies_non_terminating_identity_loop() {
        let function = make_main(
            vec![],
            vec![
                block(
                    "start",
                    vec![
                        assign("i", Type::Word, Instr::Copy(Value::Const(7))),
                        volatile(Instr::Jmp("while_cond".to_string())),
                    ],
                ),
                block(
                    "while_cond",
                    vec![
                        assign(
                            "cond",
                            Type::Word,
                            Instr::Cmp(Type::Word, Cmp::Sgt, temp("i"), Value::Const(0)),
                        ),
                        volatile(Instr::Jnz(
                            temp("cond"),
                            "while_body".to_string(),
                            "while_end".to_string(),
                        )),
                    ],
                ),
                block(
                    "while_body",
                    vec![
                        assign("next", Type::Word, Instr::Sub(temp("i"), Value::Const(0))),
                        assign("i", Type::Word, Instr::Copy(temp("next"))),
                        volatile(Instr::Jmp("while_cond".to_string())),
                    ],
                ),
                block(
                    "while_end",
                    vec![volatile(Instr::Ret(Some(Value::Const(0))))],
                ),
            ],
        );

        let proofs = classify_simple_loops(&function).expect("classifies");
        assert_eq!(proofs.len(), 1);
        assert_eq!(proofs[0].header_label, "while_cond");
        assert_eq!(proofs[0].status, LoopProofStatus::NonTerminating);
    }

    #[test]
    fn classifies_progress_loop_as_unknown() {
        let function = make_main(
            vec![],
            vec![
                block(
                    "start",
                    vec![
                        assign("i", Type::Word, Instr::Copy(Value::Const(7))),
                        volatile(Instr::Jmp("while_cond".to_string())),
                    ],
                ),
                block(
                    "while_cond",
                    vec![
                        assign(
                            "cond",
                            Type::Word,
                            Instr::Cmp(Type::Word, Cmp::Sgt, temp("i"), Value::Const(0)),
                        ),
                        volatile(Instr::Jnz(
                            temp("cond"),
                            "while_body".to_string(),
                            "while_end".to_string(),
                        )),
                    ],
                ),
                block(
                    "while_body",
                    vec![
                        assign("next", Type::Word, Instr::Sub(temp("i"), Value::Const(1))),
                        assign("i", Type::Word, Instr::Copy(temp("next"))),
                        volatile(Instr::Jmp("while_cond".to_string())),
                    ],
                ),
                block(
                    "while_end",
                    vec![volatile(Instr::Ret(Some(Value::Const(0))))],
                ),
            ],
        );

        let proofs = classify_simple_loops(&function).expect("classifies");
        assert_eq!(proofs.len(), 1);
        assert_eq!(proofs[0].status, LoopProofStatus::Unknown);
    }

    #[test]
    fn classifies_non_terminating_sub_call_identity_loop() {
        let function = make_main(
            vec![],
            vec![
                block(
                    "start",
                    vec![
                        assign("i", Type::Word, Instr::Copy(Value::Const(9))),
                        volatile(Instr::Jmp("while_cond".to_string())),
                    ],
                ),
                block(
                    "while_cond",
                    vec![
                        assign(
                            "cond",
                            Type::Word,
                            Instr::Cmp(Type::Word, Cmp::Sgt, temp("i"), Value::Const(0)),
                        ),
                        volatile(Instr::Jnz(
                            temp("cond"),
                            "while_body".to_string(),
                            "while_end".to_string(),
                        )),
                    ],
                ),
                block(
                    "while_body",
                    vec![
                        assign(
                            "next",
                            Type::Word,
                            Instr::Call(
                                "sub".to_string(),
                                vec![(Type::Word, temp("i")), (Type::Word, Value::Const(0))],
                                None,
                            ),
                        ),
                        assign("i", Type::Word, Instr::Copy(temp("next"))),
                        volatile(Instr::Jmp("while_cond".to_string())),
                    ],
                ),
                block(
                    "while_end",
                    vec![volatile(Instr::Ret(Some(Value::Const(0))))],
                ),
            ],
        );

        let proofs = classify_simple_loops(&function).expect("classifies");
        assert_eq!(proofs.len(), 1);
        assert_eq!(proofs[0].status, LoopProofStatus::NonTerminating);
    }
}
