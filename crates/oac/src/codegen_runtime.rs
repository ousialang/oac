use std::path::{Path, PathBuf};

use tracing::{debug, info};

use crate::diagnostics::{CompilerDiagnostic, CompilerDiagnosticBundle, DiagnosticStage};
use crate::{llvm_backend, CodegenOptions, RuntimeBackend};

pub(crate) struct RuntimeArtifacts {
    pub ir_artifact_path: PathBuf,
    pub linker_input_path: PathBuf,
}

pub(crate) fn emit_runtime_artifacts(
    program: &crate::ir::ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
    options: &CodegenOptions,
) -> Result<RuntimeArtifacts, CompilerDiagnosticBundle> {
    match options.backend {
        RuntimeBackend::Qbe => emit_qbe_runtime_artifacts(qbe_module, target_dir, options),
        RuntimeBackend::Llvm => emit_llvm_runtime_artifacts(program, target_dir, options),
    }
}

fn emit_qbe_runtime_artifacts(
    qbe_module: &qbe::Module,
    target_dir: &Path,
    options: &CodegenOptions,
) -> Result<RuntimeArtifacts, CompilerDiagnosticBundle> {
    let qbe_ir_path = target_dir.join("ir.qbe");
    std::fs::write(&qbe_ir_path, qbe_module.to_string()).map_err(|err| {
        CompilerDiagnosticBundle::single(
            CompilerDiagnostic::new(
                "OAC-IO-020",
                DiagnosticStage::Io,
                format!("failed to write {}", qbe_ir_path.display()),
            )
            .with_note(err.to_string()),
        )
    })?;
    info!(qbe_ir_path = %qbe_ir_path.display(), "QBE IR generated");

    let assembly_path = target_dir.join("assembly.s");
    let mut qbe_cmd = std::process::Command::new("qbe");

    if let Some(arch) = options.qbe_arch.as_deref() {
        qbe_cmd.arg("-t").arg(arch);
    }

    let qbe_output = qbe_cmd
        .arg("-o")
        .arg(&assembly_path)
        .arg(&qbe_ir_path)
        .output()
        .map_err(|err| {
            CompilerDiagnosticBundle::single(
                CompilerDiagnostic::new("OAC-QBE-002", DiagnosticStage::Qbe, "failed to run qbe")
                    .with_note(err.to_string()),
            )
        })?;

    if !qbe_output.status.success() {
        let stderr = String::from_utf8_lossy(&qbe_output.stderr)
            .trim()
            .to_string();
        let diagnostic = CompilerDiagnostic::new(
            "OAC-QBE-001",
            DiagnosticStage::Qbe,
            "compilation of QBE IR to assembly failed",
        )
        .with_note("valid archs: amd64_sysv, amd64_apple, arm64, arm64_apple, rv64")
        .with_note(stderr);
        return Err(CompilerDiagnosticBundle::single(diagnostic));
    }

    debug!(assembly_path = %assembly_path.display(), "QBE IR compiled to assembly");
    Ok(RuntimeArtifacts {
        ir_artifact_path: qbe_ir_path,
        linker_input_path: assembly_path,
    })
}

fn emit_llvm_runtime_artifacts(
    program: &crate::ir::ResolvedProgram,
    target_dir: &Path,
    options: &CodegenOptions,
) -> Result<RuntimeArtifacts, CompilerDiagnosticBundle> {
    let llvm_ir = llvm_backend::compile(program).map_err(|err| {
        CompilerDiagnosticBundle::single(
            CompilerDiagnostic::new(
                "OAC-LLVM-001",
                DiagnosticStage::Llvm,
                "failed to lower program to LLVM IR",
            )
            .with_note(err.to_string()),
        )
    })?;

    let llvm_ir_path = target_dir.join("ir.ll");
    std::fs::write(&llvm_ir_path, llvm_ir).map_err(|err| {
        CompilerDiagnosticBundle::single(
            CompilerDiagnostic::new(
                "OAC-IO-025",
                DiagnosticStage::Io,
                format!("failed to write {}", llvm_ir_path.display()),
            )
            .with_note(err.to_string()),
        )
    })?;
    info!(llvm_ir_path = %llvm_ir_path.display(), "LLVM IR generated");

    let object_path = target_dir.join("object.o");
    let mut clang = std::process::Command::new("clang");
    if let Some(target) = options.target.as_deref() {
        clang.arg(format!("--target={target}"));
    }
    let output = clang
        .arg("-x")
        .arg("ir")
        .arg("-c")
        .arg(&llvm_ir_path)
        .arg("-o")
        .arg(&object_path)
        .output()
        .map_err(|err| {
            CompilerDiagnosticBundle::single(
                CompilerDiagnostic::new(
                    "OAC-LLVM-002",
                    DiagnosticStage::Llvm,
                    "failed to invoke clang for LLVM IR compilation",
                )
                .with_note(err.to_string()),
            )
        })?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_string();
        return Err(CompilerDiagnosticBundle::single(
            CompilerDiagnostic::new(
                "OAC-LLVM-003",
                DiagnosticStage::Llvm,
                "compilation of LLVM IR to object file failed",
            )
            .with_note(format!("input: {}", llvm_ir_path.display()))
            .with_note(stderr),
        ));
    }

    debug!(object_path = %object_path.display(), "LLVM IR compiled to object file");
    Ok(RuntimeArtifacts {
        ir_artifact_path: llvm_ir_path,
        linker_input_path: object_path,
    })
}
