// feedback.rs
// ===========
//
// Every component of the Ousia toolchain must use these messages for displaying problems to the
// end user. Some examples include:
//  - CLI usage errors;
//  - Compilation errors;
//  - I/O errors.
// The guidelines for choosing one of the available severity levels:
//  - FATAL: An unrecoverable, critical error that causes the program.
//  - ERROR: Represents a single point of failure in the program's execution. The error is
//    recoverable and doesn't interrupt the flow of the program.
//  - WARNING: A potentially harmful situation that may lead to more severe issues if not dealt
//    with.
//  - NOTE: A normal yet significant condition.

use colored::*;

lazy_static! {
    pub static ref FATAL: ColoredString = "FATAL".bright_red().bold();
    pub static ref ERROR: ColoredString = "ERROR".red().bold();
    pub static ref WARNING: ColoredString = "WARNING".yellow().bold();
    pub static ref NOTE: ColoredString = "NOTE".bold();
}
