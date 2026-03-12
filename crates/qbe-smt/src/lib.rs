use std::io::{IsTerminal, Write};
use std::process::{Command, Stdio};

use ariadne::{sources, Config, Label, Report, ReportKind};
use qbe::{Function as QbeFunction, Module as QbeModule};
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

/// Assumes that a function entry satisfies a helper-defined precondition relation.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct FunctionEntryPreconditionAssumption {
    pub function_name: String,
    pub precondition_function_name: String,
}

/// Assumes that a function argument is constrained to an inclusive integer range.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct FunctionArgRangeAssumption {
    pub function_name: String,
    pub arg_index: usize,
    pub lower: u64,
    pub upper: u64,
    pub signed: bool,
}

/// Module-level assumptions injected as function-entry preconditions.
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct ModuleAssumptions {
    pub arg_invariant_assumptions: Vec<FunctionArgInvariantAssumption>,
    pub entry_precondition_assumptions: Vec<FunctionEntryPreconditionAssumption>,
    pub arg_range_assumptions: Vec<FunctionArgRangeAssumption>,
}

#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct ArtifactAnnotations {
    pub header_comments: Vec<String>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct EncodedScripts {
    pub solver_smt: String,
    pub artifact_smt: String,
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
    Ok(qbe_module_to_annotated_smt_with_assumptions(
        module,
        entry,
        options,
        assumptions,
        &ArtifactAnnotations::default(),
    )?
    .solver_smt)
}

pub fn qbe_module_to_annotated_smt_with_assumptions(
    module: &QbeModule,
    entry: &str,
    options: &EncodeOptions,
    assumptions: &ModuleAssumptions,
    annotations: &ArtifactAnnotations,
) -> Result<EncodedScripts, QbeSmtError> {
    encode::encode_module_scripts(module, entry, options, assumptions, annotations)
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
    let result = classify_solver_output(&status, &stdout, &stderr)?;

    Ok(SolverRun {
        result,
        stdout,
        stderr,
    })
}

pub fn solve_chc_script(smt: &str, timeout_seconds: u64) -> Result<SolverResult, QbeSmtError> {
    Ok(solve_chc_script_with_diagnostics(smt, timeout_seconds)?.result)
}

fn classify_solver_output(
    status: &str,
    stdout: &str,
    stderr: &str,
) -> Result<SolverResult, QbeSmtError> {
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
                status: status.to_string(),
                stdout: stdout.trim().to_string(),
                stderr: stderr.trim().to_string(),
            })
        }
    };
    Ok(result)
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
        classify_simple_loops, classify_solver_output,
        qbe_module_to_annotated_smt_with_assumptions, qbe_module_to_smt,
        qbe_module_to_smt_with_assumptions, qbe_to_smt, ArtifactAnnotations, EncodeOptions,
        FunctionArgInvariantAssumption, FunctionArgRangeAssumption,
        FunctionEntryPreconditionAssumption, LoopProofStatus, ModuleAssumptions, SolverResult,
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
        assert!(smt.contains("(declare-rel pc__main__0"));
        assert!(smt.contains("(declare-rel ret__main"));
        assert!(smt.contains("(declare-rel abort__main"));
        assert!(smt.contains("(declare-rel bad ())"));
        assert!(smt.contains("(query bad)"));
        assert!(smt.contains("(= exit_curr (_ bv1 64))"));
    }

    #[test]
    fn annotated_encoding_adds_comments_without_changing_solver_script() {
        let function = make_main(
            vec![(Type::Word, temp("x"))],
            vec![block(
                "entry",
                vec![
                    assign("y", Type::Word, Instr::Add(temp("x"), Value::Const(1))),
                    volatile(Instr::Ret(Some(temp("y")))),
                ],
            )],
        );
        let module = module_with(vec![function.clone()]);

        let scripts = qbe_module_to_annotated_smt_with_assumptions(
            &module,
            &function.name,
            &EncodeOptions::default(),
            &ModuleAssumptions::default(),
            &ArtifactAnnotations {
                header_comments: vec!["prove obligation main#0#0".to_string()],
            },
        )
        .expect("encodes");

        let solver = qbe_module_to_smt(&module, &function.name, &EncodeOptions::default())
            .expect("solver script encodes");

        assert_eq!(scripts.solver_smt, solver);
        assert!(scripts.artifact_smt.contains("; prove obligation main#0#0"));
        assert!(scripts.artifact_smt.contains("; entry function: $main"));
        assert!(scripts.artifact_smt.contains("; function $main (%x:word)"));
        assert!(scripts
            .artifact_smt
            .contains("; pc 0 in @entry: %y =w add %x, 1"));
        assert!(scripts.artifact_smt.contains("(declare-rel pc__main__0"));
    }

    #[test]
    fn artifact_header_comment_changes_do_not_change_solver_script() {
        let function = make_main(
            vec![(Type::Word, temp("x"))],
            vec![block("entry", vec![volatile(Instr::Ret(Some(temp("x"))))])],
        );
        let module = module_with(vec![function.clone()]);

        let scripts_a = qbe_module_to_annotated_smt_with_assumptions(
            &module,
            &function.name,
            &EncodeOptions::default(),
            &ModuleAssumptions::default(),
            &ArtifactAnnotations {
                header_comments: vec!["first header".to_string()],
            },
        )
        .expect("encodes");
        let scripts_b = qbe_module_to_annotated_smt_with_assumptions(
            &module,
            &function.name,
            &EncodeOptions::default(),
            &ModuleAssumptions::default(),
            &ArtifactAnnotations {
                header_comments: vec!["second header".to_string()],
            },
        )
        .expect("encodes");

        assert_eq!(scripts_a.solver_smt, scripts_b.solver_smt);
        assert_ne!(scripts_a.artifact_smt, scripts_b.artifact_smt);
    }

    #[test]
    fn error_rendering_helpers_produce_report_text() {
        let err = super::QbeSmtError::SolverUnavailable;
        let plain = err.render_report_plain("checker");
        assert!(plain.contains("qbe-smt error"));
        assert!(plain.contains("z3"));
    }

    #[test]
    fn classifies_canned_unknown_solver_outputs() {
        let unknown =
            classify_solver_output("exit code 0", "unknown\n(reason-unknown timeout)\n", "")
                .expect("classify unknown");
        assert_eq!(unknown, SolverResult::Unknown);

        let timeout =
            classify_solver_output("exit code 0", "timeout\n", "").expect("classify timeout");
        assert_eq!(timeout, SolverResult::Unknown);
    }

    #[test]
    fn rejects_unrecognized_solver_status_line() {
        let err = classify_solver_output("exit code 1", "maybe\n", "parse error")
            .expect_err("unexpected status should fail");
        assert!(err.to_string().contains("unexpected z3 output"));
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

        assert!(smt.contains("(distinct (select regs_curr (_ bv0 32)) (_ bv0 64))"));
        assert!(smt.contains(
            "(pc__main__1 regs_next mem_next heap_next exit_next regs_in mem_in heap_in)"
        ));
        assert!(smt.contains(
            "(pc__main__2 regs_next mem_next heap_next exit_next regs_in mem_in heap_in)"
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

        assert!(smt.contains(
            "(pc__main__2 regs_curr mem_curr heap_curr exit_curr regs_in mem_in heap_in)"
        ));
        assert!(smt.contains(
            "(pc__main__1 regs_next mem_next heap_next exit_next regs_in mem_in heap_in)"
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

        assert!(smt.contains("(store mem_curr"));
        assert!(smt.contains("(select mem_curr"));
        assert!(smt.contains("(bvadd heap_curr"));
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

        assert!(smt.contains("(bvsge (select regs_curr (_ bv0 32)) (_ bv0 64))"));
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

        assert!(smt.contains("(bvsge (select regs_curr (_ bv0 32)) (_ bv5 64))"));
        assert!(smt.contains("(bvsle (select regs_curr (_ bv0 32)) (_ bv9 64))"));
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

        assert!(smt.contains("(= call_exit_code (_ bv242 64))"));
        assert!(smt.contains(
            "(abort__main regs_in mem_in heap_in call_exit_code call_mem_out call_heap_out)"
        ));
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
        assert!(smt.contains("(select mem_curr"));
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

        assert!(smt.contains("(bvule (select regs_curr (_ bv2 32))"));
        assert!(smt.contains("(select mem_curr (bvadd"));
    }

    #[test]
    fn models_strlen_with_bounded_nul_scan_and_fallback_branch() {
        let function = make_main(
            vec![(Type::Long, temp("s"))],
            vec![block(
                "entry",
                vec![
                    assign(
                        "len",
                        Type::Long,
                        Instr::Call("strlen".to_string(), vec![(Type::Long, temp("s"))], None),
                    ),
                    volatile(Instr::Ret(Some(temp("len")))),
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
        .expect("strlen should encode");

        assert!(smt.contains("(_ bv15 64)"));
        assert!(smt.contains("(_ bv0 8)"));
        assert!(smt.contains("(select mem_curr (bvadd"));
    }

    #[test]
    fn models_strcmp_with_bounded_scan_and_fallback_branch() {
        let function = make_main(
            vec![(Type::Long, temp("lhs")), (Type::Long, temp("rhs"))],
            vec![block(
                "entry",
                vec![
                    assign(
                        "cmp",
                        Type::Word,
                        Instr::Call(
                            "strcmp".to_string(),
                            vec![(Type::Long, temp("lhs")), (Type::Long, temp("rhs"))],
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
        .expect("strcmp should encode");

        assert!(smt.contains("(_ bv0 8)"));
        assert!(smt.contains("(distinct (select mem_curr (bvadd"));
        assert!(smt.contains("(bvult (select mem_curr (bvadd"));
        assert!(smt.contains("(_ bv18446744073709551615 64)"));
        assert!(smt.contains("(_ bv1 64)"));
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
    fn models_strcpy_with_bounded_copy_until_nul_and_fallback_branch() {
        let function = make_main(
            vec![(Type::Long, temp("dst")), (Type::Long, temp("src"))],
            vec![block(
                "entry",
                vec![
                    volatile(Instr::Call(
                        "strcpy".to_string(),
                        vec![(Type::Long, temp("dst")), (Type::Long, temp("src"))],
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
        .expect("strcpy should encode");

        assert!(smt.contains("(_ bv0 8)"));
        assert!(smt.contains("(not"));
        assert!(smt.contains("(store"));
    }

    #[test]
    fn models_open_read_write_close_return_constraints() {
        let function = make_main(
            vec![
                (Type::Long, temp("path")),
                (Type::Word, temp("flags")),
                (Type::Long, temp("mode")),
                (Type::Word, temp("fd")),
                (Type::Long, temp("buf")),
                (Type::Long, temp("count")),
            ],
            vec![block(
                "entry",
                vec![
                    assign(
                        "opened",
                        Type::Word,
                        Instr::Call(
                            "open".to_string(),
                            vec![
                                (Type::Long, temp("path")),
                                (Type::Word, temp("flags")),
                                (Type::Long, temp("mode")),
                            ],
                            None,
                        ),
                    ),
                    assign(
                        "nread",
                        Type::Long,
                        Instr::Call(
                            "read".to_string(),
                            vec![
                                (Type::Word, temp("fd")),
                                (Type::Long, temp("buf")),
                                (Type::Long, temp("count")),
                            ],
                            None,
                        ),
                    ),
                    assign(
                        "nwritten",
                        Type::Long,
                        Instr::Call(
                            "write".to_string(),
                            vec![
                                (Type::Word, temp("fd")),
                                (Type::Long, temp("buf")),
                                (Type::Long, temp("count")),
                            ],
                            None,
                        ),
                    ),
                    assign(
                        "closed",
                        Type::Word,
                        Instr::Call("close".to_string(), vec![(Type::Word, temp("fd"))], None),
                    ),
                    volatile(Instr::Ret(Some(temp("nread")))),
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
        .expect("open/read/write/close should encode");

        assert!(smt.contains("(bvsle"));
        assert!(smt.contains("(bvsge"));
        assert!(smt.contains("(_ bv18446744073709551615 64)"));
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
        assert!(smt.contains("(declare-rel ret__main"));
        assert!(smt.contains("(declare-rel ret__helper"));
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

        assert!(smt.contains("(declare-rel ret__main"));
        assert!(smt.contains("(declare-rel abort__main"));
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
            entry_precondition_assumptions: vec![],
            arg_range_assumptions: vec![],
        };

        let smt = qbe_module_to_smt_with_assumptions(
            &module,
            "main",
            &EncodeOptions::default(),
            &assumptions,
        )
        .expect("module with argument invariant assumptions should encode");

        assert!(smt.contains("(declare-var arg_inv_regs_0"));
        assert!(smt.contains(
            "arg_inv_regs_0 mem_curr heap_curr arg_inv_ret_0 arg_inv_mem_0 arg_inv_heap_0"
        ));
        assert!(smt.contains("(distinct arg_inv_ret_0 (_ bv0 64))"));
    }

    #[test]
    fn encodes_precondition_assumption_in_entry_rule() {
        let helper = Function {
            linkage: Linkage::default(),
            name: "__pre__guarded__clause_0".to_string(),
            arguments: vec![(Type::Word, temp("x"))],
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
        let module = module_with(vec![main, helper]);
        let assumptions = ModuleAssumptions {
            arg_invariant_assumptions: vec![],
            entry_precondition_assumptions: vec![FunctionEntryPreconditionAssumption {
                function_name: "main".to_string(),
                precondition_function_name: "__pre__guarded__clause_0".to_string(),
            }],
            arg_range_assumptions: vec![],
        };

        let smt = qbe_module_to_smt_with_assumptions(
            &module,
            "main",
            &EncodeOptions::default(),
            &assumptions,
        )
        .expect("module with entry precondition assumptions should encode");

        assert!(smt.contains("(declare-var precond_regs_0"));
        assert!(smt.contains(
            "precond_regs_0 mem_curr heap_curr precond_ret_0 precond_mem_0 precond_heap_0"
        ));
        assert!(smt.contains("(select regs_curr"));
        assert!(!smt.contains("(select regs "));
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
            entry_precondition_assumptions: vec![],
            arg_range_assumptions: vec![],
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
            entry_precondition_assumptions: vec![],
            arg_range_assumptions: vec![],
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
            entry_precondition_assumptions: vec![],
            arg_range_assumptions: vec![],
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
            entry_precondition_assumptions: vec![],
            arg_range_assumptions: vec![],
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
    fn encodes_arg_range_assumption_in_entry_rule() {
        let main = make_main(
            vec![(Type::Word, temp("x"))],
            vec![block("entry", vec![volatile(Instr::Ret(Some(temp("x"))))])],
        );
        let module = module_with(vec![main]);
        let assumptions = ModuleAssumptions {
            arg_invariant_assumptions: vec![],
            entry_precondition_assumptions: vec![],
            arg_range_assumptions: vec![FunctionArgRangeAssumption {
                function_name: "main".to_string(),
                arg_index: 0,
                lower: 0,
                upper: 255,
                signed: false,
            }],
        };

        let smt = qbe_module_to_smt_with_assumptions(
            &module,
            "main",
            &EncodeOptions::default(),
            &assumptions,
        )
        .expect("module with argument range assumptions should encode");

        assert!(smt.contains("bvuge"));
        assert!(smt.contains("bvule"));
        assert!(smt.contains("(_ bv255 64)"));
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
                    assign(
                        "x",
                        Type::Word,
                        Instr::Store(Type::Word, Value::Const(0), Value::Const(2)),
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
        .expect_err("unsupported op should fail");

        assert!(err
            .to_string()
            .contains("unsupported assignment operation for assignment type Word"));
    }

    #[test]
    fn encodes_fp32_arithmetic_and_compares_with_all_logic() {
        let function = make_main(
            vec![(Type::Single, temp("a")), (Type::Single, temp("b"))],
            vec![block(
                "entry",
                vec![
                    assign("sum", Type::Single, Instr::Add(temp("a"), temp("b"))),
                    assign(
                        "is_lt",
                        Type::Word,
                        Instr::Cmp(Type::Single, Cmp::Lt, temp("sum"), temp("b")),
                    ),
                    volatile(Instr::Ret(Some(temp("is_lt")))),
                ],
            )],
        );

        let smt = encode_single_function(&function, &EncodeOptions::default())
            .expect("FP32 arithmetic and compare should encode");

        assert!(smt.contains("(set-logic ALL)"));
        assert!(smt.contains("(fp.add RNE"));
        assert!(smt.contains("(fp.lt"));
    }

    #[test]
    fn encodes_fp32_loads_and_stores() {
        let function = make_main(
            vec![(Type::Long, temp("p")), (Type::Single, temp("x"))],
            vec![block(
                "entry",
                vec![
                    volatile(Instr::Store(Type::Single, temp("p"), temp("x"))),
                    assign("loaded", Type::Single, Instr::Load(Type::Single, temp("p"))),
                    assign(
                        "eq",
                        Type::Word,
                        Instr::Cmp(Type::Single, Cmp::Eq, temp("loaded"), temp("x")),
                    ),
                    volatile(Instr::Ret(Some(temp("eq")))),
                ],
            )],
        );

        let smt = encode_single_function(&function, &EncodeOptions::default())
            .expect("FP32 load/store should encode");
        assert!(smt.contains("(set-logic ALL)"));
        assert!(smt.contains("(store mem_curr"));
        assert!(smt.contains("(select mem_curr"));
    }

    #[test]
    fn encodes_fp64_arithmetic_and_compares_with_all_logic() {
        let function = make_main(
            vec![(Type::Double, temp("a")), (Type::Double, temp("b"))],
            vec![block(
                "entry",
                vec![
                    assign("sum", Type::Double, Instr::Add(temp("a"), temp("b"))),
                    assign(
                        "is_lt",
                        Type::Word,
                        Instr::Cmp(Type::Double, Cmp::Lt, temp("sum"), temp("b")),
                    ),
                    volatile(Instr::Ret(Some(temp("is_lt")))),
                ],
            )],
        );

        let smt = encode_single_function(&function, &EncodeOptions::default())
            .expect("FP64 arithmetic and compare should encode");

        assert!(smt.contains("(set-logic ALL)"));
        assert!(smt.contains("(fp.add RNE"));
        assert!(smt.contains("(fp.lt"));
    }

    #[test]
    fn encodes_fp64_loads_and_stores() {
        let function = make_main(
            vec![(Type::Long, temp("p")), (Type::Double, temp("x"))],
            vec![block(
                "entry",
                vec![
                    volatile(Instr::Store(Type::Double, temp("p"), temp("x"))),
                    assign("loaded", Type::Double, Instr::Load(Type::Double, temp("p"))),
                    assign(
                        "eq",
                        Type::Word,
                        Instr::Cmp(Type::Double, Cmp::Eq, temp("loaded"), temp("x")),
                    ),
                    volatile(Instr::Ret(Some(temp("eq")))),
                ],
            )],
        );

        let smt = encode_single_function(&function, &EncodeOptions::default())
            .expect("FP64 load/store should encode");
        assert!(smt.contains("(set-logic ALL)"));
        assert!(smt.contains("(store mem_curr"));
        assert!(smt.contains("(select mem_curr"));
    }

    #[test]
    fn encodes_fp_conversion_ops_with_ieee_smt_rounding() {
        let function = make_main(
            vec![
                (Type::Single, temp("sf")),
                (Type::Double, temp("df")),
                (Type::Word, temp("w")),
                (Type::Long, temp("l")),
            ],
            vec![block(
                "entry",
                vec![
                    assign("ext_d", Type::Double, Instr::Exts(temp("sf"))),
                    assign("trunc_s", Type::Single, Instr::Truncd(temp("df"))),
                    assign("stosi_w", Type::Word, Instr::Stosi(temp("sf"))),
                    assign("stosi_l", Type::Long, Instr::Stosi(temp("sf"))),
                    assign("stoui_w", Type::Word, Instr::Stoui(temp("sf"))),
                    assign("stoui_l", Type::Long, Instr::Stoui(temp("sf"))),
                    assign("dtosi_w", Type::Word, Instr::Dtosi(temp("df"))),
                    assign("dtosi_l", Type::Long, Instr::Dtosi(temp("df"))),
                    assign("dtoui_w", Type::Word, Instr::Dtoui(temp("df"))),
                    assign("dtoui_l", Type::Long, Instr::Dtoui(temp("df"))),
                    assign("swtof_s", Type::Single, Instr::Swtof(temp("w"))),
                    assign("swtof_d", Type::Double, Instr::Swtof(temp("w"))),
                    assign("uwtof_s", Type::Single, Instr::Uwtof(temp("w"))),
                    assign("uwtof_d", Type::Double, Instr::Uwtof(temp("w"))),
                    assign("sltof_s", Type::Single, Instr::Sltof(temp("l"))),
                    assign("sltof_d", Type::Double, Instr::Sltof(temp("l"))),
                    assign("ultof_s", Type::Single, Instr::Ultof(temp("l"))),
                    assign("ultof_d", Type::Double, Instr::Ultof(temp("l"))),
                    volatile(Instr::Ret(Some(temp("stosi_w")))),
                ],
            )],
        );

        let smt = encode_single_function(&function, &EncodeOptions::default())
            .expect("FP conversion ops should encode");
        assert!(smt.contains("(set-logic ALL)"));
        assert!(smt.contains("((_ to_fp 11 53) RNE ((_ to_fp 8 24)"));
        assert!(smt.contains("((_ to_fp 8 24) RTZ ((_ to_fp 11 53)"));
        assert!(smt.contains("((_ fp.to_sbv 32) RTZ"));
        assert!(smt.contains("((_ fp.to_sbv 64) RTZ"));
        assert!(smt.contains("((_ fp.to_ubv 32) RTZ"));
        assert!(smt.contains("((_ fp.to_ubv 64) RTZ"));
        assert!(smt.contains("((_ to_fp_unsigned 8 24) RNE"));
        assert!(smt.contains("((_ to_fp_unsigned 11 53) RNE"));
    }

    #[test]
    fn rejects_invalid_fp_conversion_assignment_type() {
        let function = make_main(
            vec![(Type::Single, temp("x"))],
            vec![block(
                "entry",
                vec![
                    assign("y", Type::Word, Instr::Exts(temp("x"))),
                    volatile(Instr::Ret(Some(temp("y")))),
                ],
            )],
        );

        let err = encode_single_function(&function, &EncodeOptions::default())
            .expect_err("invalid conversion assignment shape should fail closed");
        assert!(err
            .to_string()
            .contains("unary operation exts requires assignment type Double"));
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

        assert!(smt.contains("(or (= pred_curr (_ bv1 32)) (= pred_curr (_ bv2 32)))"));
        assert!(smt.contains("(ite (= pred_curr (_ bv1 32))"));
        assert!(smt.contains(
            "(declare-rel pc__main__0 ((Array (_ BitVec 32) (_ BitVec 64)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64) (_ BitVec 64) (_ BitVec 32)"
        ));
    }

    #[test]
    fn omits_pred_from_pc_relations_when_function_has_no_phi() {
        let function = make_main(
            vec![(Type::Word, temp("x"))],
            vec![block(
                "entry",
                vec![
                    assign("y", Type::Word, Instr::Add(temp("x"), Value::Const(1))),
                    volatile(Instr::Ret(Some(temp("y")))),
                ],
            )],
        );

        let smt = encode_single_function(&function, &EncodeOptions::default()).expect("encodes");

        assert!(smt.contains(
            "(declare-rel pc__main__0 ((Array (_ BitVec 32) (_ BitVec 64)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 32) (_ BitVec 64))"
        ));
        assert!(!smt.contains(
            "(declare-rel pc__main__0 ((Array (_ BitVec 32) (_ BitVec 64)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64) (_ BitVec 64) (_ BitVec 32)"
        ));
    }

    #[test]
    fn mixed_module_keeps_pred_only_for_phi_bearing_functions() {
        let helper = Function {
            linkage: Linkage::default(),
            name: "helper".to_string(),
            arguments: vec![(Type::Word, temp("cond"))],
            return_ty: Some(Type::Word),
            blocks: vec![
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

        let smt = qbe_module_to_smt(
            &module_with(vec![main, helper]),
            "main",
            &EncodeOptions::default(),
        )
        .expect("mixed module encodes");

        assert!(smt.contains(
            "(declare-rel pc__helper__0 ((Array (_ BitVec 32) (_ BitVec 64)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64) (_ BitVec 64) (_ BitVec 32)"
        ) || smt.contains(
            "(declare-rel pc__main__0 ((Array (_ BitVec 32) (_ BitVec 64)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64) (_ BitVec 64) (_ BitVec 32)"
        ));
        assert!(smt.contains(
            "(declare-rel pc__helper__0 ((Array (_ BitVec 32) (_ BitVec 64)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 32) (_ BitVec 64))"
        ) || smt.contains(
            "(declare-rel pc__main__0 ((Array (_ BitVec 32) (_ BitVec 64)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 32) (_ BitVec 64))"
        ));
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
