use exitcode::{self, ExitCode};
use std::io::{self, Stdin, Stdout, Write};
use termion::clear::All as ClearAll;
use termion::cursor::Goto as CursorGoto;
use termion::event::{Event, Key};
use termion::input::{MouseTerminal, TermRead};
use termion::screen::AlternateScreen;

pub struct Ui {
    state: State,
    stdin: Stdin,
    stdout: AlternateScreen<MouseTerminal<Stdout>>,
}

impl Ui {
    pub fn new() -> Self {
        let stdin = io::stdin();
        let mut stdout = AlternateScreen::from(MouseTerminal::from(io::stdout()));
        writeln!(stdout, "{}{}", ClearAll, CursorGoto(1, 1));
        let mut ui = Ui {
            state: State::Virgin,
            stdin: io::stdin(),
            stdout: stdout,
        };
        ui.enter_loop();
        ui
    }

    fn enter_loop(&mut self) -> ExitCode {
        for e in self.stdin.events() {
            match self.handle_event(e.unwrap()) {
                Ok(_) => (),
                Err(exit_code) => {
                    return exit_code;
                }
            }
        }
        exitcode::SOFTWARE
    }

    fn handle_event(&mut self, event: Event) -> Result<(), ExitCode> {
        match event {
            Event::Key(key) => match key {
                Key::Char(c) => Ok(()),
                _ => Ok(()),
            },
            Event::Mouse(mouse_event) => Ok(()),
            Event::Unsupported(_) => Ok(()),
        }
    }
}

impl Drop for Ui {
    fn drop(&mut self) -> () {
        self.stdout.flush();
        ()
    }
}

pub enum State {
    Virgin,
    Shutdown,
}

impl State {}
