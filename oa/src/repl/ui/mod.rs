use std::io::{self, Error as IoError, Stdin, Stdout};

use exitcode::ExitCode;
use termion::clear::All as ClearAll;
use termion::cursor::Goto as CursorGoto;
use termion::event::{Event, Key};
use termion::input::MouseTerminal;
use termion::screen::AlternateScreen;

pub struct Ui {
    screen: AlternateScreen<Stdout>,
    state: State,
    stdin: Stdin,
    stdout: Stdout,
}

impl Ui {
    fn new() -> Self {
        let stdin = io::stdin();
        let mut stdout = MouseTerminal::from(io::stdout());
        let mut screen = AlternateScreen::from(stdout);
        writeln!(stdout, "{}{}", ClearAll, CursorGoto(1, 1));
        let mut ui = Ui {
            screen: screen,
            state: State::new(),
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
                    break;
                    return exit_code;
                }
            }
        }
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
    fn drop(&mut self) -> Result<(), IoError> {
        self.stdout.flush()
    }
}

enum State {
    Shutdown,
}

impl State {}
