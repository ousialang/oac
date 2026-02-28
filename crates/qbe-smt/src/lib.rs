use ariadne::{sources, Config, Label, Report, ReportKind};
use qbe::{Function as QbeFunction, Module as QbeModule};
use std::io::IsTerminal;
use std::io::Write;
use std::process::{Command, Stdio};
use thiserror::Error;

mod classify;
mod encode;
mod encode_extern_models;

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

/// Assumes that a function argument satisfies a struct invariant relation.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct FunctionArgInvariantAssumption {
    pub function_name: String,
    pub arg_index: usize,
    pub invariant_function_name: String,
}

/// Module-level assumptions injected as function-entry preconditions.
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct ModuleAssumptions {
    pub arg_invariant_assumptions: Vec<FunctionArgInvariantAssumption>,
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

impl QbeSmtError {
    pub fn render_report_plain(&self, source_id: &str) -> String {
        self.render_report(source_id, false)
    }

    pub fn render_report_terminal_auto(&self, source_id: &str) -> String {
        self.render_report(source_id, std::io::stderr().is_terminal())
    }

    fn render_report(&self, source_id: &str, use_color: bool) -> String {
        let message = self.to_string();
        let mut report = Report::build(ReportKind::Error, (source_id.to_string(), 0..1))
            .with_code("QBE-SMT-001")
            .with_message("qbe-smt error")
            .with_label(Label::new((source_id.to_string(), 0..1)).with_message(message.clone()))
            .with_config(Config::default().with_color(use_color));

        match self {
            QbeSmtError::Unsupported { .. } => {
                report =
                    report.with_note("qbe-smt is strict fail-closed for unsupported operations");
            }
            QbeSmtError::SolverUnavailable => {
                report = report.with_help("install z3 and ensure it is on PATH");
            }
            _ => {}
        }

        let mut output = Vec::new();
        let source_entries = vec![(source_id.to_string(), String::new())];
        match report.finish().write(sources(source_entries), &mut output) {
            Ok(()) => String::from_utf8_lossy(&output).trim_end().to_string(),
            Err(_) => format!("qbe-smt error: {message}"),
        }
    }
}

/// Encode a QBE module into SMT-LIB text, starting from one entry function.
///
/// This builds an interprocedural CHC model over the entry function and all
/// reachable user-defined callees.
pub fn qbe_module_to_smt(
    module: &QbeModule,
    entry: &str,
    options: &EncodeOptions,
) -> Result<String, QbeSmtError> {
    qbe_module_to_smt_with_assumptions(module, entry, options, &ModuleAssumptions::default())
}

/// Encode a QBE module into SMT-LIB text, starting from one entry function,
/// with explicit module-level assumptions.
pub fn qbe_module_to_smt_with_assumptions(
    module: &QbeModule,
    entry: &str,
    options: &EncodeOptions,
    assumptions: &ModuleAssumptions,
) -> Result<String, QbeSmtError> {
    encode::encode_module(module, entry, options, assumptions)
}

/// Encode one QBE function body into SMT-LIB text.
///
/// This is a compatibility wrapper over module encoding.
pub fn qbe_to_smt(function: &QbeFunction, options: &EncodeOptions) -> Result<String, QbeSmtError> {
    let module = QbeModule {
        functions: vec![function.clone()],
        types: vec![],
        data: vec![],
    };
    qbe_module_to_smt(&module, &function.name, options)
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

    let write_result = {
        let stdin = child.stdin.as_mut().ok_or_else(|| QbeSmtError::SolverIo {
            message: "failed to open z3 stdin".to_string(),
        })?;
        stdin.write_all(smt.as_bytes())
    };
    if let Err(err) = write_result {
        if err.kind() != std::io::ErrorKind::BrokenPipe {
            return Err(QbeSmtError::SolverIo {
                message: format!("failed to send SMT query to z3: {err}"),
            });
        }
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
    use qbe::{Block, BlockItem, Cmp, Function, Instr, Linkage, Module, Statement, Type, Value};

    use super::{
        classify_simple_loops, qbe_module_to_smt, qbe_module_to_smt_with_assumptions, qbe_to_smt,
        EncodeOptions, FunctionArgInvariantAssumption, LoopProofStatus, ModuleAssumptions,
    };

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

    fn module_with(functions: Vec<Function>) -> Module {
        Module {
            functions,
            types: vec![],
            data: vec![],
        }
    }

    fn encode_single_function(
        function: &Function,
        options: &EncodeOptions,
    ) -> Result<String, super::QbeSmtError> {
        qbe_module_to_smt(
            &module_with(vec![function.clone()]),
            &function.name,
            options,
        )
    }

    fn encode_single_function_with_assumptions(
        function: &Function,
        options: &EncodeOptions,
        assumptions: &ModuleAssumptions,
    ) -> Result<String, super::QbeSmtError> {
        qbe_module_to_smt_with_assumptions(
            &module_with(vec![function.clone()]),
            &function.name,
            options,
            assumptions,
        )
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

        let smt = encode_single_function(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(set-logic HORN)"));
        assert!(smt.contains("(set-option :fp.engine spacer)"));
        assert!(smt.contains("(declare-rel f0_pc_0"));
        assert!(smt.contains("(declare-rel f0_ret"));
        assert!(smt.contains("(declare-rel f0_abort"));
        assert!(smt.contains("(declare-rel bad ())"));
        assert!(smt.contains("(query bad)"));
        assert!(smt.contains("(= exit (_ bv1 64))"));
    }

    #[test]
    fn error_rendering_helpers_produce_report_text() {
        let err = super::QbeSmtError::SolverUnavailable;
        let plain = err.render_report_plain("checker");
        assert!(plain.contains("qbe-smt error"));
        assert!(plain.contains("z3"));
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

        let smt = encode_single_function(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(distinct (select regs (_ bv0 32)) (_ bv0 64))"));
        assert!(smt.contains(
            "(f0_pc_1 regs_next mem_next heap_next exit_next pred_next in_regs in_mem in_heap)"
        ));
        assert!(smt.contains(
            "(f0_pc_2 regs_next mem_next heap_next exit_next pred_next in_regs in_mem in_heap)"
        ));
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

        let smt = encode_single_function(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect("encodes");

        assert!(smt.contains("(f0_pc_2 regs mem heap exit pred in_regs in_mem in_heap)"));
        assert!(smt.contains(
            "(f0_pc_1 regs_next mem_next heap_next exit_next pred_next in_regs in_mem in_heap)"
        ));
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

        let smt = encode_single_function(
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

        let smt = encode_single_function(
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

        let smt = encode_single_function(
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

        let err = encode_single_function(
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

        let smt = encode_single_function(
            &function,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect("exit call should encode");

        assert!(smt.contains("(= code_call (_ bv242 64))"));
        assert!(smt.contains("(f0_abort in_regs in_mem in_heap code_call mem_call heap_call)"));
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

        let err = encode_single_function(
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

        let smt = encode_single_function(
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
    fn models_memcmp_with_symbolic_length_and_fallback_branch() {
        let function = make_main(
            vec![
                (Type::Long, temp("lhs")),
                (Type::Long, temp("rhs")),
                (Type::Long, temp("n")),
            ],
            vec![block(
                "entry",
                vec![
                    assign(
                        "cmp",
                        Type::Word,
                        Instr::Call(
                            "memcmp".to_string(),
                            vec![
                                (Type::Long, temp("lhs")),
                                (Type::Long, temp("rhs")),
                                (Type::Long, temp("n")),
                            ],
                            None,
                        ),
                    ),
                    volatile(Instr::Ret(Some(temp("cmp")))),
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
        .expect("memcmp should encode");

        assert!(smt.contains("(bvule (select regs (_ bv2 32))"));
        assert!(smt.contains("(select mem (bvadd"));
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

        encode_single_function(
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

        let smt = encode_single_function(
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

        encode_single_function(
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

        encode_single_function(
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

        let err = encode_single_function(
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

        let err = encode_single_function(
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
    fn module_encoder_accepts_reachable_user_calls_without_inlining() {
        let helper = Function {
            linkage: Linkage::default(),
            name: "helper".to_string(),
            arguments: vec![(Type::Word, temp("x"))],
            return_ty: Some(Type::Word),
            blocks: vec![block(
                "entry",
                vec![
                    assign("y", Type::Word, Instr::Add(temp("x"), Value::Const(1))),
                    volatile(Instr::Ret(Some(temp("y")))),
                ],
            )],
        };

        let main = make_main(
            vec![(Type::Word, temp("a"))],
            vec![block(
                "entry",
                vec![
                    assign(
                        "r",
                        Type::Word,
                        Instr::Call("helper".to_string(), vec![(Type::Word, temp("a"))], None),
                    ),
                    volatile(Instr::Ret(Some(temp("r")))),
                ],
            )],
        );

        let module = module_with(vec![main.clone(), helper]);

        let single_err = encode_single_function(
            &main,
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect_err("single-function encoder should reject unresolved user call target");
        assert!(single_err
            .to_string()
            .contains("unsupported call target $helper"));

        let smt = qbe_module_to_smt(
            &module,
            "main",
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect("module encoder should accept user calls with summaries");
        assert!(smt.contains("(declare-rel f0_ret"));
        assert!(smt.contains("(declare-rel f1_ret"));
        assert!(smt.contains("(query bad)"));
    }

    #[test]
    fn module_encoder_accepts_self_recursive_user_calls() {
        let main = make_main(
            vec![(Type::Word, temp("a"))],
            vec![block(
                "entry",
                vec![
                    assign(
                        "r",
                        Type::Word,
                        Instr::Call("main".to_string(), vec![(Type::Word, temp("a"))], None),
                    ),
                    volatile(Instr::Ret(Some(temp("r")))),
                ],
            )],
        );

        let module = module_with(vec![main]);
        let smt = qbe_module_to_smt(&module, "main", &EncodeOptions::default())
            .expect("module encoder should accept self-recursive user calls");

        assert!(smt.contains("(declare-rel f0_ret"));
        assert!(smt.contains("(declare-rel f0_abort"));
        assert!(smt.contains("(query bad)"));
    }

    #[test]
    fn module_encoder_rejects_missing_entry_function() {
        let helper = Function {
            linkage: Linkage::default(),
            name: "helper".to_string(),
            arguments: vec![(Type::Word, temp("x"))],
            return_ty: Some(Type::Word),
            blocks: vec![block("entry", vec![volatile(Instr::Ret(Some(temp("x"))))])],
        };
        let module = module_with(vec![helper]);
        let err = qbe_module_to_smt(
            &module,
            "main",
            &EncodeOptions {
                assume_main_argc_non_negative: false,
                first_arg_i32_range: None,
            },
        )
        .expect_err("missing module entry should fail closed");
        assert!(err
            .to_string()
            .contains("entry function $main is missing from module"));
    }

    #[test]
    fn encodes_arg_invariant_assumption_in_entry_rule() {
        let invariant = Function {
            linkage: Linkage::default(),
            name: "__struct__Box__invariant".to_string(),
            arguments: vec![(Type::Word, temp("v"))],
            return_ty: Some(Type::Word),
            blocks: vec![block(
                "entry",
                vec![volatile(Instr::Ret(Some(Value::Const(1))))],
            )],
        };
        let main = make_main(
            vec![(Type::Word, temp("x"))],
            vec![block("entry", vec![volatile(Instr::Ret(Some(temp("x"))))])],
        );
        let module = module_with(vec![main, invariant]);
        let assumptions = ModuleAssumptions {
            arg_invariant_assumptions: vec![FunctionArgInvariantAssumption {
                function_name: "main".to_string(),
                arg_index: 0,
                invariant_function_name: "__struct__Box__invariant".to_string(),
            }],
        };

        let smt = qbe_module_to_smt_with_assumptions(
            &module,
            "main",
            &EncodeOptions::default(),
            &assumptions,
        )
        .expect("module with argument invariant assumptions should encode");

        assert!(smt.contains("(declare-var regs_call_0"));
        assert!(smt.contains("regs_call_0 mem heap ret_call_0 mem_call_0 heap_call_0"));
        assert!(smt.contains("(distinct ret_call_0 (_ bv0 64))"));
    }

    #[test]
    fn rejects_assumptions_for_missing_function() {
        let function = make_main(
            vec![(Type::Word, temp("x"))],
            vec![block("entry", vec![volatile(Instr::Ret(Some(temp("x"))))])],
        );
        let assumptions = ModuleAssumptions {
            arg_invariant_assumptions: vec![FunctionArgInvariantAssumption {
                function_name: "missing".to_string(),
                arg_index: 0,
                invariant_function_name: "main".to_string(),
            }],
        };
        let err = encode_single_function_with_assumptions(
            &function,
            &EncodeOptions::default(),
            &assumptions,
        )
        .expect_err("assumptions for missing functions must fail closed");
        assert!(err
            .to_string()
            .contains("arg-invariant assumption target function $missing is missing from module"));
    }

    #[test]
    fn rejects_assumptions_with_out_of_range_arg_index() {
        let function = make_main(
            vec![(Type::Word, temp("x"))],
            vec![block("entry", vec![volatile(Instr::Ret(Some(temp("x"))))])],
        );
        let assumptions = ModuleAssumptions {
            arg_invariant_assumptions: vec![FunctionArgInvariantAssumption {
                function_name: "main".to_string(),
                arg_index: 1,
                invariant_function_name: "main".to_string(),
            }],
        };
        let err = encode_single_function_with_assumptions(
            &function,
            &EncodeOptions::default(),
            &assumptions,
        )
        .expect_err("out-of-range assumption index must fail closed");
        assert!(err
            .to_string()
            .contains("argument index 1 is out of range (arity=1)"));
    }

    #[test]
    fn rejects_assumptions_with_non_unary_invariant_target() {
        let invariant = Function {
            linkage: Linkage::default(),
            name: "invariant_bad_arity".to_string(),
            arguments: vec![(Type::Word, temp("a")), (Type::Word, temp("b"))],
            return_ty: Some(Type::Word),
            blocks: vec![block(
                "entry",
                vec![volatile(Instr::Ret(Some(Value::Const(1))))],
            )],
        };
        let main = make_main(
            vec![(Type::Word, temp("x"))],
            vec![block("entry", vec![volatile(Instr::Ret(Some(temp("x"))))])],
        );
        let module = module_with(vec![main, invariant]);
        let assumptions = ModuleAssumptions {
            arg_invariant_assumptions: vec![FunctionArgInvariantAssumption {
                function_name: "main".to_string(),
                arg_index: 0,
                invariant_function_name: "invariant_bad_arity".to_string(),
            }],
        };

        let err = qbe_module_to_smt_with_assumptions(
            &module,
            "main",
            &EncodeOptions::default(),
            &assumptions,
        )
        .expect_err("non-unary invariant assumptions must fail closed");
        assert!(err.to_string().contains("must have arity 1, found 2"));
    }

    #[test]
    fn assumptions_add_invariant_function_reachability() {
        let invariant = Function {
            linkage: Linkage::default(),
            name: "__struct__Payload__invariant".to_string(),
            arguments: vec![(Type::Word, temp("v"))],
            return_ty: Some(Type::Word),
            blocks: vec![block(
                "entry",
                vec![volatile(Instr::Ret(Some(Value::Const(1))))],
            )],
        };
        let helper = Function {
            linkage: Linkage::default(),
            name: "helper".to_string(),
            arguments: vec![(Type::Word, temp("x"))],
            return_ty: Some(Type::Word),
            blocks: vec![block("entry", vec![volatile(Instr::Ret(Some(temp("x"))))])],
        };
        let main = make_main(
            vec![(Type::Word, temp("a"))],
            vec![block(
                "entry",
                vec![
                    assign(
                        "r",
                        Type::Word,
                        Instr::Call("helper".to_string(), vec![(Type::Word, temp("a"))], None),
                    ),
                    volatile(Instr::Ret(Some(temp("r")))),
                ],
            )],
        );
        let assumptions = ModuleAssumptions {
            arg_invariant_assumptions: vec![FunctionArgInvariantAssumption {
                function_name: "helper".to_string(),
                arg_index: 0,
                invariant_function_name: "__struct__Payload__invariant".to_string(),
            }],
        };
        let module = module_with(vec![main, helper, invariant]);

        qbe_module_to_smt_with_assumptions(
            &module,
            "main",
            &EncodeOptions::default(),
            &assumptions,
        )
        .expect("assumptions should add invariant function to reachability closure");
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

        let smt = encode_single_function(
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

        let err = encode_single_function(
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

        let smt = encode_single_function(
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

        let err = encode_single_function(
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
