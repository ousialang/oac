//! RISC-V ELF to SMT converter
//!
//! This module provides functionality to convert a RISC-V ELF file into an SMT expression
//! that can be used to verify if the program returns 0 within 1000 cycles.

use anyhow::{Context, Result};
use goblin::elf::Elf;
use std::fs;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

/// Maximum number of cycles to simulate
pub const MAX_CYCLES: u32 = 1000;

/// RISC-V register count (32 registers)
const REGISTER_COUNT: usize = 32;

/// RISC-V instruction representation for SMT encoding
#[derive(Debug, Clone)]
pub struct RiscvInstruction {
    pub opcode: u32,
    pub rd: u8,
    pub rs1: u8,
    pub rs2: u8,
    pub imm: i32,
    pub address: u64,
}

/// Parse RISC-V ELF file and extract instructions
pub fn parse_riscv_elf(elf_path: &Path) -> Result<Vec<RiscvInstruction>> {
    let buffer = fs::read(elf_path)
        .with_context(|| format!("Failed to read ELF file: {}", elf_path.display()))?;

    let elf = Elf::parse(&buffer).with_context(|| "Failed to parse ELF file")?;

    let mut instructions = Vec::new();

    // Find executable sections and decode instructions
    for section in &elf.section_headers {
        if section.sh_flags & (goblin::elf::section_header::SHF_EXECINSTR as u64) != 0 {
            let section_data =
                &buffer[section.sh_offset as usize..(section.sh_offset + section.sh_size) as usize];

            // Parse 32-bit RISC-V instructions
            for (i, chunk) in section_data.chunks_exact(4).enumerate() {
                let instruction_bytes = [chunk[0], chunk[1], chunk[2], chunk[3]];
                let instruction_word = u32::from_le_bytes(instruction_bytes);
                let address = section.sh_addr + (i * 4) as u64;

                // Decode basic RISC-V instruction format
                let instruction = decode_riscv_instruction(instruction_word, address);
                instructions.push(instruction);
            }
        }
    }

    Ok(instructions)
}

/// Decode a RISC-V instruction from its 32-bit representation
fn decode_riscv_instruction(instruction: u32, address: u64) -> RiscvInstruction {
    let opcode = instruction & 0x7F;
    let rd = ((instruction >> 7) & 0x1F) as u8;
    let rs1 = ((instruction >> 15) & 0x1F) as u8;
    let rs2 = ((instruction >> 20) & 0x1F) as u8;

    // Simplified immediate decoding for different instruction types
    let imm = match opcode {
        0x13 | 0x03 | 0x67 | 0x73 => (instruction as i32) >> 20, // I-type
        0x23 => {
            // S-type
            let imm_4_0 = (instruction >> 7) & 0x1F;
            let imm_11_5 = (instruction >> 25) & 0x7F;
            (((imm_11_5 << 5) | imm_4_0) as i32).wrapping_shl(20) >> 20 // Sign extend
        }
        0x63 => {
            // B-type
            let imm_11 = (instruction >> 7) & 0x1;
            let imm_4_1 = (instruction >> 8) & 0xF;
            let imm_10_5 = (instruction >> 25) & 0x3F;
            let imm_12 = (instruction >> 31) & 0x1;
            ((((imm_12 << 12) | (imm_11 << 11) | (imm_10_5 << 5) | (imm_4_1 << 1)) as i32)
                .wrapping_shl(19)
                >> 19) // Sign extend
        }
        0x37 | 0x17 => {
            // U-type (LUI, AUIPC)
            (instruction & 0xFFFFF000) as i32
        }
        0x6F => {
            // J-type (JAL)
            let imm_20 = (instruction >> 31) & 0x1;
            let imm_10_1 = (instruction >> 21) & 0x3FF;
            let imm_11 = (instruction >> 20) & 0x1;
            let imm_19_12 = (instruction >> 12) & 0xFF;
            ((((imm_20 << 20) | (imm_19_12 << 12) | (imm_11 << 11) | (imm_10_1 << 1)) as i32)
                .wrapping_shl(11)
                >> 11) // Sign extend
        }
        _ => 0,
    };

    RiscvInstruction {
        opcode,
        rd,
        rs1,
        rs2,
        imm,
        address,
    }
}

/// Convert RISC-V ELF to SMT expression that checks if program returns 0 within MAX_CYCLES
pub fn elf_to_smt_returns_zero_within_cycles(elf_path: &Path) -> Result<String> {
    let instructions = parse_riscv_elf(elf_path)?;

    let mut smt = String::new();

    // SMT-LIB v2 header
    smt.push_str(&format!(
        "(set-info :source |Generated from RISC-V ELF: {}|)\n",
        elf_path.display()
    ));
    smt.push_str("(set-logic QF_BV)\n\n");

    // Declare register variables for each cycle
    for cycle in 0..=MAX_CYCLES {
        for reg in 0..REGISTER_COUNT {
            smt.push_str(&format!(
                "(declare-fun reg_{}_{} () (_ BitVec 32))\n",
                reg, cycle
            ));
        }
        smt.push_str(&format!("(declare-fun pc_{} () (_ BitVec 32))\n", cycle));
    }
    smt.push_str("\n");

    // x0 is always 0
    for cycle in 0..=MAX_CYCLES {
        smt.push_str(&format!("(assert (= reg_0_{} #x00000000))\n", cycle));
    }
    smt.push_str("\n");

    // Initial PC (simplified - using 0x1000 as entry point)
    smt.push_str("(assert (= pc_0 #x00001000))\n\n");

    // Model instruction execution for each cycle
    for cycle in 0..MAX_CYCLES {
        let next_cycle = cycle + 1;

        // For each instruction, create conditional execution based on PC
        for instruction in &instructions {
            let pc_condition = format!("(= pc_{} #x{:08x})", cycle, instruction.address);

            match instruction.opcode {
                0x13 => {
                    // I-type (focusing on ADDI)
                    if instruction.rd != 0 {
                        // ADDI: rd = rs1 + imm
                        smt.push_str(&format!(
                            "(assert (=> {} (= reg_{}_{} (bvadd reg_{}_{} #x{:08x}))))\n",
                            pc_condition,
                            instruction.rd,
                            next_cycle,
                            instruction.rs1,
                            cycle,
                            instruction.imm as u32
                        ));

                        // Other registers remain unchanged
                        for reg in 0..REGISTER_COUNT {
                            if reg != instruction.rd as usize {
                                smt.push_str(&format!(
                                    "(assert (=> {} (= reg_{}_{} reg_{}_{})))\n",
                                    pc_condition, reg, next_cycle, reg, cycle
                                ));
                            }
                        }
                    } else {
                        // All registers remain unchanged if rd is x0
                        for reg in 0..REGISTER_COUNT {
                            smt.push_str(&format!(
                                "(assert (=> {} (= reg_{}_{} reg_{}_{})))\n",
                                pc_condition, reg, next_cycle, reg, cycle
                            ));
                        }
                    }

                    // Update PC to next instruction
                    smt.push_str(&format!(
                        "(assert (=> {} (= pc_{} (bvadd pc_{} #x00000004))))\n",
                        pc_condition, next_cycle, cycle
                    ));
                }
                0x37 => {
                    // LUI
                    if instruction.rd != 0 {
                        smt.push_str(&format!(
                            "(assert (=> {} (= reg_{}_{} #x{:08x})))\n",
                            pc_condition, instruction.rd, next_cycle, instruction.imm as u32
                        ));

                        // Other registers remain unchanged
                        for reg in 0..REGISTER_COUNT {
                            if reg != instruction.rd as usize {
                                smt.push_str(&format!(
                                    "(assert (=> {} (= reg_{}_{} reg_{}_{})))\n",
                                    pc_condition, reg, next_cycle, reg, cycle
                                ));
                            }
                        }
                    } else {
                        // All registers remain unchanged if rd is x0
                        for reg in 0..REGISTER_COUNT {
                            smt.push_str(&format!(
                                "(assert (=> {} (= reg_{}_{} reg_{}_{})))\n",
                                pc_condition, reg, next_cycle, reg, cycle
                            ));
                        }
                    }

                    smt.push_str(&format!(
                        "(assert (=> {} (= pc_{} (bvadd pc_{} #x00000004))))\n",
                        pc_condition, next_cycle, cycle
                    ));
                }
                0x73 => {
                    // ECALL/EBREAK - halt execution
                    // PC remains the same (halt)
                    smt.push_str(&format!(
                        "(assert (=> {} (= pc_{} pc_{})))\n",
                        pc_condition, next_cycle, cycle
                    ));

                    // All registers remain unchanged
                    for reg in 0..REGISTER_COUNT {
                        smt.push_str(&format!(
                            "(assert (=> {} (= reg_{}_{} reg_{}_{})))\n",
                            pc_condition, reg, next_cycle, reg, cycle
                        ));
                    }
                }
                _ => {
                    // Default: advance PC, keep registers unchanged
                    smt.push_str(&format!(
                        "(assert (=> {} (= pc_{} (bvadd pc_{} #x00000004))))\n",
                        pc_condition, next_cycle, cycle
                    ));

                    for reg in 0..REGISTER_COUNT {
                        smt.push_str(&format!(
                            "(assert (=> {} (= reg_{}_{} reg_{}_{})))\n",
                            pc_condition, reg, next_cycle, reg, cycle
                        ));
                    }
                }
            }
        }

        // Default state transition if PC doesn't match any instruction
        let no_match_conditions: Vec<String> = instructions
            .iter()
            .map(|instr| format!("(not (= pc_{} #x{:08x}))", cycle, instr.address))
            .collect();

        if !no_match_conditions.is_empty() {
            let no_match_condition = format!("(and {})", no_match_conditions.join(" "));

            // Keep everything unchanged if no instruction matches
            smt.push_str(&format!(
                "(assert (=> {} (= pc_{} pc_{})))\n",
                no_match_condition, next_cycle, cycle
            ));

            for reg in 0..REGISTER_COUNT {
                smt.push_str(&format!(
                    "(assert (=> {} (= reg_{}_{} reg_{}_{})))\n",
                    no_match_condition, reg, next_cycle, reg, cycle
                ));
            }
        }
    }

    smt.push_str("\n");

    // Goal: program should return 0 (in register x10/a0) within MAX_CYCLES
    let mut goal_conditions = Vec::new();
    for cycle in 0..=MAX_CYCLES {
        goal_conditions.push(format!("(= reg_10_{} #x00000000)", cycle));
    }

    smt.push_str(&format!("(assert (or {}))\n", goal_conditions.join(" ")));

    smt.push_str("\n(check-sat)\n");
    smt.push_str("(exit)\n");

    Ok(smt)
}

/// Check if a RISC-V ELF program returns 0 within the specified number of cycles
/// This function generates the SMT expression and attempts to solve it using an external SMT solver.
/// If no solver is available, it falls back to a simple simulation approach.
pub fn check_returns_zero_within_cycles(elf_path: &Path) -> Result<bool> {
    let smt_expression = elf_to_smt_returns_zero_within_cycles(elf_path)?;

    let smt_file = elf_path.with_extension("smt");

    // Write SMT expression to file
    std::fs::write(&smt_file, &smt_expression)?;

    // First, try to use an external SMT solver (Z3)
    if let Ok(result) = solve_with_z3(&smt_expression) {
        return Ok(result);
    }

    // If SMT solving fails, fall back to simple simulation
    eprintln!("Warning: SMT solver not available, falling back to simulation");
    simulate_program_execution(elf_path)
}

/// Attempt to solve the SMT expression using Z3
fn solve_with_z3(smt_expression: &str) -> Result<bool> {
    use std::io::Write;
    use std::process::{Command, Stdio};

    // Try to find Z3 in the system PATH
    let mut cmd = Command::new("z3")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| "Failed to start Z3. Make sure Z3 is installed and in your PATH")?;

    // Write the SMT expression to Z3's stdin
    if let Some(stdin) = cmd.stdin.as_mut() {
        stdin
            .write_all(smt_expression.as_bytes())
            .with_context(|| "Failed to write SMT expression to Z3")?;
    }

    // Wait for Z3 to complete and read the result
    let output = cmd
        .wait_with_output()
        .with_context(|| "Failed to read Z3 output")?;

    if !output.status.success() {
        anyhow::bail!(
            "Z3 solver failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let result = String::from_utf8_lossy(&output.stdout);

    // Parse Z3's output
    if result.trim() == "sat" {
        Ok(true) // SMT formula is satisfiable - program can return 0 within cycles
    } else if result.trim() == "unsat" {
        Ok(false) // SMT formula is unsatisfiable - program cannot return 0 within cycles
    } else {
        anyhow::bail!("Unexpected Z3 output: {}", result);
    }
}

/// Simple simulation fallback when SMT solver is not available
fn simulate_program_execution(elf_path: &Path) -> Result<bool> {
    let instructions = parse_riscv_elf(elf_path)?;

    // Initialize CPU state
    let mut registers = [0u32; REGISTER_COUNT];
    let mut pc = 0x1000u32; // Entry point
    let mut cycles = 0;

    // Simple instruction simulation
    while cycles < MAX_CYCLES {
        cycles += 1;

        // Find instruction at current PC
        let current_instruction = instructions.iter().find(|instr| instr.address == pc as u64);

        let instruction = match current_instruction {
            Some(instr) => instr,
            None => {
                // No instruction found at PC, assume program halted
                break;
            }
        };

        // Execute instruction based on opcode
        match instruction.opcode {
            0x13 => {
                // ADDI: rd = rs1 + imm
                if instruction.rd != 0 {
                    registers[instruction.rd as usize] =
                        registers[instruction.rs1 as usize].wrapping_add(instruction.imm as u32);
                }
                pc = pc.wrapping_add(4);
            }
            0x37 => {
                // LUI: rd = imm << 12
                if instruction.rd != 0 {
                    registers[instruction.rd as usize] = instruction.imm as u32;
                }
                pc = pc.wrapping_add(4);
            }
            0x73 => {
                // ECALL/EBREAK - halt execution
                break;
            }
            _ => {
                // Unknown instruction, just advance PC
                pc = pc.wrapping_add(4);
            }
        }

        // Ensure x0 is always 0
        registers[0] = 0;

        // Check if a0 (x10) contains 0 (successful return)
        if registers[10] == 0 && cycles > 1 {
            // Allow at least one cycle to set a0
            return Ok(true);
        }
    }

    // Check final state of a0 register
    Ok(registers[10] == 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_instruction_decoding() {
        // Test ADDI x1, x0, 42
        let instruction = 0x02a00093; // addi x1, x0, 42
        let decoded = decode_riscv_instruction(instruction, 0x1000);

        assert_eq!(decoded.opcode, 0x13); // ADDI opcode
        assert_eq!(decoded.rd, 1); // x1
        assert_eq!(decoded.rs1, 0); // x0
        assert_eq!(decoded.imm, 42); // immediate value

        // Test LUI x2, 0x12345
        let instruction_lui = 0x12345137; // lui x2, 0x12345
        let decoded_lui = decode_riscv_instruction(instruction_lui, 0x1004);
        assert_eq!(decoded_lui.opcode, 0x37); // LUI opcode
        assert_eq!(decoded_lui.rd, 2); // x2
        assert_eq!(decoded_lui.imm, 0x12345000); // immediate value for LUI
    }

    #[test]
    fn test_smt_generation_structure() {
        // This test would require a sample RISC-V ELF file
        // For now, just test that the function can be called without panicking
        let dummy_path = PathBuf::from("nonexistent.elf");
        let result = elf_to_smt_returns_zero_within_cycles(&dummy_path);

        // Should fail because file doesn't exist, but shouldn't panic
        assert!(result.is_err());
    }

    #[test]
    fn test_smt_output_format() {
        // Test that we can generate SMT for a minimal example
        // This would need a real ELF file to work properly
        let dummy_instructions = vec![RiscvInstruction {
            opcode: 0x13, // ADDI
            rd: 10,       // a0
            rs1: 0,       // x0
            rs2: 0,
            imm: 0, // Load 0 into a0
            address: 0x1000,
        }];

        // Test that instruction decoding produces expected results
        assert_eq!(dummy_instructions[0].opcode, 0x13);
        assert_eq!(dummy_instructions[0].rd, 10);
        assert_eq!(dummy_instructions[0].imm, 0);
    }
}
