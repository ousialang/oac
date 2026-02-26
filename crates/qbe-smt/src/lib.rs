use qbe::Function as QbeFunction;
use std::io::Write;
use std::process::{Command, Stdio};
use thiserror::Error;

mod classify;
mod encode;

pub use classify::{LoopProof, LoopProofStatus};

/// Options for CHC/fixedpoint QBE-to-SMT encoding.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct EncodeOptions {
    /// Add `argc >= 0` constraint for the first function argument in the initial state.
    pub assume_main_argc_non_negative: bool,
    /// Constrain the first function argument (interpreted as signed I32) to an inclusive range.
    pub first_arg_i32_range: Option<(i32, i32)>,
}

impl Default for EncodeOptions {
    fn default() -> Self {
        Self {
            assume_main_argc_non_negative: false,
            first_arg_i32_range: None,
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
    #[error("z3 executable not found. Install z3 to run CHC/fixedpoint proofs")]
    SolverUnavailable,
    #[error("failed to run z3: {message}")]
    SolverIo { message: String },
    #[error("unexpected z3 output (status={status}): stdout='{stdout}' stderr='{stderr}'")]
    SolverOutput {
        status: String,
        stdout: String,
        stderr: String,
    },
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

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum SolverResult {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SolverRun {
    pub result: SolverResult,
    pub stdout: String,
    pub stderr: String,
}

pub fn solve_chc_script_with_diagnostics(
    smt: &str,
    timeout_seconds: u64,
) -> Result<SolverRun, QbeSmtError> {
    let (status, stdout, stderr) = run_z3_query(smt, timeout_seconds)?;
    let first = stdout
        .lines()
        .map(str::trim)
        .find(|line| !line.is_empty())
        .unwrap_or("");

    let result = match first {
        "sat" => SolverResult::Sat,
        "unsat" => SolverResult::Unsat,
        "unknown" | "timeout" => SolverResult::Unknown,
        _ => {
            return Err(QbeSmtError::SolverOutput {
                status,
                stdout: stdout.trim().to_string(),
                stderr: stderr.trim().to_string(),
            })
        }
    };

    Ok(SolverRun {
        result,
        stdout,
        stderr,
    })
}

pub fn solve_chc_script(smt: &str, timeout_seconds: u64) -> Result<SolverResult, QbeSmtError> {
    Ok(solve_chc_script_with_diagnostics(smt, timeout_seconds)?.result)
}

fn run_z3_query(smt: &str, timeout_seconds: u64) -> Result<(String, String, String), QbeSmtError> {
    let mut command = Command::new("z3");
    command
        .arg(format!("-T:{timeout_seconds}"))
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    let mut child = command.spawn().map_err(|err| {
        if err.kind() == std::io::ErrorKind::NotFound {
            QbeSmtError::SolverUnavailable
        } else {
            QbeSmtError::SolverIo {
                message: format!("spawn failed: {err}"),
            }
        }
    })?;

    {
        let stdin = child.stdin.as_mut().ok_or_else(|| QbeSmtError::SolverIo {
            message: "failed to open z3 stdin".to_string(),
        })?;
        stdin
            .write_all(smt.as_bytes())
            .map_err(|err| QbeSmtError::SolverIo {
                message: format!("failed to send SMT query to z3: {err}"),
            })?;
    }

    let output = child
        .wait_with_output()
        .map_err(|err| QbeSmtError::SolverIo {
            message: format!("failed to wait for z3 process: {err}"),
        })?;

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    Ok((output.status.to_string(), stdout, stderr))
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
                first_arg_i32_range: None,
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
                first_arg_i32_range: None,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(distinct (select regs (_ bv0 32)) (_ bv0 64))"));
        assert!(smt.contains("(pc_1 regs_next mem_next heap_next exit_next pred_next)"));
        assert!(smt.contains("(pc_2 regs_next mem_next heap_next exit_next pred_next)"));
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
                first_arg_i32_range: None,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(pc_2 regs mem heap exit pred)"));
        assert!(smt.contains("(pc_1 regs_next mem_next heap_next exit_next pred_next)"));
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
                first_arg_i32_range: None,
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
                first_arg_i32_range: None,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(bvsge (select regs (_ bv0 32)) (_ bv0 64))"));
    }

    #[test]
    fn emits_first_arg_i32_range_constraint_when_enabled() {
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
                assume_main_argc_non_negative: false,
                first_arg_i32_range: Some((5, 9)),
            },
        )
        .expect("encodes");

        assert!(smt.contains("(bvsge (select regs (_ bv0 32)) (_ bv5 64))"));
        assert!(smt.contains("(bvsle (select regs (_ bv0 32)) (_ bv9 64))"));
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
                first_arg_i32_range: None,
            },
        )
        .expect_err("should fail");
        assert!(err.to_string().contains("unknown label @missing"));
    }

    #[test]
    fn models_exit_call_as_halting_transition() {
        let function = make_main(
            vec![],
            vec![block(
                "entry",
                vec![volatile(Instr::Call(
                    "exit".to_string(),
                    vec![(Type::Word, Value::Const(242))],
                    None,
                ))],
            )],
        );

        let smt = qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect("exit call should encode");

        assert!(smt.contains("(= exit_next (_ bv242 64))"));
        assert!(smt.contains("(halt_state regs_next mem_next heap_next exit_next pred_next)"));
    }

    #[test]
    fn rejects_exit_without_argument() {
        let function = make_main(
            vec![],
            vec![block(
                "entry",
                vec![volatile(Instr::Call("exit".to_string(), vec![], None))],
            )],
        );

        let err = qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect_err("exit without args should fail");
        assert!(err
            .to_string()
            .contains("call target $exit requires one argument"));
    }

    #[test]
    fn models_memcpy_with_symbolic_length_and_fallback_branch() {
        let function = make_main(
            vec![
                (Type::Long, temp("dst")),
                (Type::Long, temp("src")),
                (Type::Long, temp("n")),
            ],
            vec![block(
                "entry",
                vec![
                    volatile(Instr::Call(
                        "memcpy".to_string(),
                        vec![
                            (Type::Long, temp("dst")),
                            (Type::Long, temp("src")),
                            (Type::Long, temp("n")),
                        ],
                        None,
                    )),
                    volatile(Instr::Ret(Some(Value::Const(0)))),
                ],
            )],
        );

        let smt = qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect("memcpy should encode");

        assert!(smt.contains("(ite (bvule"));
        assert!(smt.contains("(select mem"));
    }

    #[test]
    fn models_memmove_overlap_case() {
        let function = make_main(
            vec![(Type::Long, temp("dst")), (Type::Long, temp("n"))],
            vec![block(
                "entry",
                vec![
                    volatile(Instr::Call(
                        "memmove".to_string(),
                        vec![
                            (Type::Long, temp("dst")),
                            (Type::Long, temp("dst")),
                            (Type::Long, temp("n")),
                        ],
                        None,
                    )),
                    volatile(Instr::Ret(Some(Value::Const(0)))),
                ],
            )],
        );

        qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect("memmove overlap case should encode");
    }

    #[test]
    fn models_memset_bounded_writes() {
        let function = make_main(
            vec![
                (Type::Long, temp("dst")),
                (Type::Long, temp("n")),
                (Type::Word, temp("fill")),
            ],
            vec![block(
                "entry",
                vec![
                    volatile(Instr::Call(
                        "memset".to_string(),
                        vec![
                            (Type::Long, temp("dst")),
                            (Type::Word, temp("fill")),
                            (Type::Long, temp("n")),
                        ],
                        None,
                    )),
                    volatile(Instr::Ret(Some(Value::Const(0)))),
                ],
            )],
        );

        let smt = qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect("memset should encode");

        assert!(smt.contains("((_ extract 7 0)"));
        assert!(smt.contains("(store"));
    }

    #[test]
    fn models_calloc_realloc_and_free_calls() {
        let function = make_main(
            vec![],
            vec![block(
                "entry",
                vec![
                    assign(
                        "p",
                        Type::Long,
                        Instr::Call(
                            "calloc".to_string(),
                            vec![(Type::Long, Value::Const(2)), (Type::Long, Value::Const(8))],
                            None,
                        ),
                    ),
                    assign(
                        "q",
                        Type::Long,
                        Instr::Call(
                            "realloc".to_string(),
                            vec![(Type::Long, temp("p")), (Type::Long, Value::Const(32))],
                            None,
                        ),
                    ),
                    volatile(Instr::Call(
                        "free".to_string(),
                        vec![(Type::Long, temp("q"))],
                        None,
                    )),
                    volatile(Instr::Ret(Some(Value::Const(0)))),
                ],
            )],
        );

        qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect("calloc/realloc/free should encode");
    }

    #[test]
    fn models_variadic_printf_call() {
        let function = make_main(
            vec![],
            vec![block(
                "entry",
                vec![
                    volatile(Instr::Call(
                        "printf".to_string(),
                        vec![(Type::Long, Value::Const(0)), (Type::Word, Value::Const(7))],
                        Some(1),
                    )),
                    volatile(Instr::Ret(Some(Value::Const(0)))),
                ],
            )],
        );

        qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect("variadic printf should encode");
    }

    #[test]
    fn rejects_printf_without_variadic_marker() {
        let function = make_main(
            vec![],
            vec![block(
                "entry",
                vec![
                    volatile(Instr::Call(
                        "printf".to_string(),
                        vec![(Type::Long, Value::Const(0))],
                        None,
                    )),
                    volatile(Instr::Ret(Some(Value::Const(0)))),
                ],
            )],
        );

        let err = qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect_err("printf without variadic marker should fail");
        assert!(err
            .to_string()
            .contains("call target $printf must be variadic"));
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
                first_arg_i32_range: None,
            },
        )
        .expect_err("unsupported call should fail");
        assert!(err.to_string().contains("unsupported call target $foo"));
    }

    #[test]
    fn ignores_unsupported_calls_in_unreachable_blocks() {
        let function = make_main(
            vec![],
            vec![
                block("entry", vec![volatile(Instr::Ret(Some(Value::Const(0))))]),
                block(
                    "dead",
                    vec![
                        assign(
                            "y",
                            Type::Word,
                            Instr::Call(
                                "foo".to_string(),
                                vec![(Type::Word, Value::Const(1))],
                                None,
                            ),
                        ),
                        volatile(Instr::Ret(Some(temp("y")))),
                    ],
                ),
            ],
        );

        let smt = qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect("encodes while ignoring unreachable unsupported calls");

        assert!(!smt.contains("foo"));
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
                first_arg_i32_range: None,
            },
        )
        .expect_err("unsupported op should fail");

        assert!(err.to_string().contains("unsupported unary operation exts"));
    }

    #[test]
    fn encodes_phi_with_predecessor_guard() {
        let function = make_main(
            vec![(Type::Word, temp("cond"))],
            vec![
                block(
                    "entry",
                    vec![volatile(Instr::Jnz(
                        temp("cond"),
                        "left".to_string(),
                        "right".to_string(),
                    ))],
                ),
                block(
                    "left",
                    vec![
                        assign("x_left", Type::Word, Instr::Copy(Value::Const(1))),
                        volatile(Instr::Jmp("join".to_string())),
                    ],
                ),
                block(
                    "right",
                    vec![
                        assign("x_right", Type::Word, Instr::Copy(Value::Const(2))),
                        volatile(Instr::Jmp("join".to_string())),
                    ],
                ),
                block(
                    "join",
                    vec![
                        assign(
                            "x",
                            Type::Word,
                            Instr::Phi(
                                "left".to_string(),
                                temp("x_left"),
                                "right".to_string(),
                                temp("x_right"),
                            ),
                        ),
                        volatile(Instr::Ret(Some(temp("x")))),
                    ],
                ),
            ],
        );

        let smt = qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(or (= pred (_ bv1 32)) (= pred (_ bv2 32)))"));
        assert!(smt.contains("(ite (= pred (_ bv1 32))"));
    }

    #[test]
    fn rejects_phi_with_unknown_label() {
        let function = make_main(
            vec![],
            vec![block(
                "entry",
                vec![
                    assign(
                        "x",
                        Type::Word,
                        Instr::Phi(
                            "missing".to_string(),
                            Value::Const(1),
                            "entry".to_string(),
                            Value::Const(2),
                        ),
                    ),
                    volatile(Instr::Ret(Some(temp("x")))),
                ],
            )],
        );

        let err = qbe_to_smt(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect_err("phi with unknown label should fail");
        assert!(err.to_string().contains("unknown label @missing"));
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
