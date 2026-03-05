use std::fmt;
use std::io::{self, Write};
use std::time::Duration;

const RESET: &str = "\x1b[0m";
const CYAN: &str = "\x1b[36m";
const GREEN: &str = "\x1b[32m";
const RED: &str = "\x1b[31m";
const DIM: &str = "\x1b[2m";
const STAGE_LABEL_WIDTH: usize = 18;
const DURATION_WIDTH: usize = 8;

pub(crate) struct CliReporter {
    quiet: bool,
    use_color: bool,
    writer: Box<dyn Write>,
}

impl CliReporter {
    pub(crate) fn stderr(quiet: bool, use_color: bool) -> Self {
        Self {
            quiet,
            use_color,
            writer: Box::new(io::stderr()),
        }
    }

    pub(crate) fn header(&mut self, command: &str) {
        if self.quiet {
            return;
        }
        self.write_line(&self.style(command, CYAN));
    }

    pub(crate) fn metadata(&mut self, key: &str, value: impl fmt::Display) {
        if self.quiet {
            return;
        }
        self.write_line(&format!(
            "  {:<9} {}",
            self.style(key, DIM),
            self.style(&value.to_string(), DIM)
        ));
    }

    pub(crate) fn stage_start(&mut self, stage: &str) {
        if self.quiet {
            return;
        }
        self.write_line(&format!(
            "  {:<4} {:<width$} {}",
            self.style("...", DIM),
            self.style(stage, CYAN),
            self.style("starting", DIM),
            width = STAGE_LABEL_WIDTH,
        ));
    }

    pub(crate) fn stage_success(&mut self, stage: &str, duration: Duration) {
        if self.quiet {
            return;
        }
        self.write_line(&format!(
            "  {:<4} {:<width$} {:>dur_width$}",
            self.style("ok", GREEN),
            self.style(stage, CYAN),
            self.style(&format_duration(duration), DIM),
            width = STAGE_LABEL_WIDTH,
            dur_width = DURATION_WIDTH,
        ));
    }

    pub(crate) fn stage_failure(&mut self, stage: &str, duration: Duration) {
        if self.quiet {
            return;
        }
        self.write_line(&format!(
            "  {:<4} {:<width$} {:>dur_width$}",
            self.style("!!", RED),
            self.style(stage, RED),
            self.style(&format_duration(duration), DIM),
            width = STAGE_LABEL_WIDTH,
            dur_width = DURATION_WIDTH,
        ));
    }

    pub(crate) fn finish_success(&mut self, total: Duration, output_path: impl fmt::Display) {
        if self.quiet {
            return;
        }
        self.write_line(&format!(
            "  {:<4} {:<width$} {:>dur_width$}",
            self.style("ok", GREEN),
            self.style("complete", CYAN),
            self.style(&format_duration(total), DIM),
            width = STAGE_LABEL_WIDTH,
            dur_width = DURATION_WIDTH,
        ));
        self.metadata("output", output_path);
    }

    pub(crate) fn finish_failure(&mut self, total: Duration) {
        if self.quiet {
            return;
        }
        self.write_line(&format!(
            "  {:<4} {:<width$} {:>dur_width$}",
            self.style("!!", RED),
            self.style("failed", RED),
            self.style(&format_duration(total), DIM),
            width = STAGE_LABEL_WIDTH,
            dur_width = DURATION_WIDTH,
        ));
    }

    pub(crate) fn finish_tests(
        &mut self,
        total: Duration,
        test_count: usize,
        output_path: impl fmt::Display,
    ) {
        if self.quiet {
            return;
        }
        self.write_line(&format!(
            "  {:<4} {:<width$} {:>dur_width$}",
            self.style("ok", GREEN),
            self.style("complete", CYAN),
            self.style(&format_duration(total), DIM),
            width = STAGE_LABEL_WIDTH,
            dur_width = DURATION_WIDTH,
        ));
        self.metadata("tests", format!("{test_count}"));
        self.metadata("output", output_path);
    }

    fn style(&self, text: &str, color: &str) -> String {
        if self.use_color {
            format!("{color}{text}{RESET}")
        } else {
            text.to_string()
        }
    }

    fn write_line(&mut self, line: &str) {
        if let Err(err) = writeln!(self.writer, "{line}") {
            // Reporting must never fail the command.
            let _ = writeln!(io::stderr(), "oac: failed to write progress output: {err}");
        }
    }
}

fn format_duration(duration: Duration) -> String {
    if duration.as_millis() < 1_000 {
        format!("{}ms", duration.as_millis())
    } else {
        format!("{:.2}s", duration.as_secs_f64())
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::io::Write;
    use std::rc::Rc;
    use std::time::Duration;

    use super::CliReporter;

    #[derive(Clone)]
    struct SharedBuffer {
        inner: Rc<RefCell<Vec<u8>>>,
    }

    impl SharedBuffer {
        fn new() -> (Self, Rc<RefCell<Vec<u8>>>) {
            let inner = Rc::new(RefCell::new(Vec::new()));
            (
                Self {
                    inner: Rc::clone(&inner),
                },
                inner,
            )
        }
    }

    impl Write for SharedBuffer {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.inner.borrow_mut().extend_from_slice(buf);
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    fn reporter_for_test(quiet: bool, use_color: bool) -> (CliReporter, Rc<RefCell<Vec<u8>>>) {
        let (buffer, sink) = SharedBuffer::new();
        (
            CliReporter {
                quiet,
                use_color,
                writer: Box::new(buffer),
            },
            sink,
        )
    }

    #[test]
    fn emits_aligned_stage_rows_without_color() {
        let (mut reporter, sink) = reporter_for_test(false, false);
        reporter.stage_start("frontend");
        reporter.stage_success("frontend", Duration::from_millis(42));

        let output = String::from_utf8(sink.borrow().clone()).expect("utf8");
        let lines = output.lines().collect::<Vec<_>>();
        assert_eq!(lines.len(), 2);
        assert!(lines[0].starts_with("  ...  frontend"));
        assert!(lines[1].starts_with("  ok   frontend"));
        assert!(lines[1].ends_with("42ms"));
    }

    #[test]
    fn no_color_mode_contains_no_ansi_sequences() {
        let (mut reporter, sink) = reporter_for_test(false, false);
        reporter.header("oac build");
        reporter.stage_success("resolve", Duration::from_millis(7));

        let output = String::from_utf8(sink.borrow().clone()).expect("utf8");
        assert!(!output.contains("\x1b["));
    }

    #[test]
    fn quiet_mode_emits_nothing() {
        let (mut reporter, sink) = reporter_for_test(true, true);
        reporter.header("oac build");
        reporter.stage_start("frontend");
        reporter.stage_success("frontend", Duration::from_millis(12));
        reporter.finish_success(Duration::from_secs(1), "target/oac/app");

        assert!(sink.borrow().is_empty());
    }

    #[test]
    fn emits_failure_rows() {
        let (mut reporter, sink) = reporter_for_test(false, false);
        reporter.stage_failure("verify.struct", Duration::from_millis(305));

        let output = String::from_utf8(sink.borrow().clone()).expect("utf8");
        assert!(output.contains("!!   verify.struct"));
        assert!(output.contains("305ms"));
    }
}
