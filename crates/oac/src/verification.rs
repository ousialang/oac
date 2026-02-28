use std::path::Path;

use crate::ir::ResolvedProgram;

#[derive(Debug)]
pub enum VerificationError {
    Prove(anyhow::Error),
    StructInvariant(anyhow::Error),
}

pub fn verify_all_obligations_with_qbe(
    program: &ResolvedProgram,
    qbe_module: &qbe::Module,
    target_dir: &Path,
) -> Result<(), VerificationError> {
    crate::prove::verify_prove_obligations_with_qbe(program, qbe_module, target_dir)
        .map_err(VerificationError::Prove)?;
    crate::struct_invariants::verify_struct_invariants_with_qbe(program, qbe_module, target_dir)
        .map_err(VerificationError::StructInvariant)?;
    Ok(())
}
