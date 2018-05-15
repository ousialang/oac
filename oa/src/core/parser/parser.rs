pub trait CharUtils {
    fn is_symbol(self) -> bool;
    fn is_opening_bracket(self) -> bool;
    fn is_closing_bracket(self) -> bool;
    fn is_right_side_of(self, c: char) -> bool;
}

impl CharUtils for char {
    fn is_symbol(self) -> bool {
        "/+*-!|%&=?^@#.:,<>".contains(self)
    }

    fn is_opening_bracket(self) -> bool {
        "{[(".contains(self)
    }

    fn is_closing_bracket(self) -> bool {
        "}])".contains(self)
    }

    fn is_right_side_of(self, c: char) -> bool {
        match (c, self) {
            ('(', ')') | ('[', ']') | ('{', '}') => true,
            _ => false,
        }
    }
}mpl Parser {
    fn new() -> Parser {
        Parser {
            ast: Some(Ast::new()),
            feedbacks: Vec::new(),
            pedigree_of_current_scope: String::new(),
            buffer: String::new(),
            flag: false,
        }
    }

    fn parse_word(&mut self, chars: &mut Peekable<Chars>) -> char {
        loop {
            let c = chars.next().unwrap();
            if c.is_alphabetic() {
                self.buffer.push(c);
            } else {
                return c;
            }
            if chars.peek().is_none() {
                return '\0';
            }
        }
    }

    fn parse_symbol(&mut self, chars: &mut Peekable<Chars>) -> char {
        loop {
            let c = chars.next().unwrap();
            if c.is_symbol() {
                self.buffer.push(c);
            } else {
                return c;
            }
            if chars.peek().is_none() {
                return '\0';
            }
        }
    }

    fn parse_number(&mut self, chars: &mut Peekable<Chars>) -> char {
        loop {
            let c = chars.next().unwrap();
            if c.is_digit(10) {
                self.buffer.push(c);
            } else {
                self.add_token(Token {
                    location: Range { start: 0, end: 1 },
                    kind: TokenKind::Number(Number {
                        buffer: "abc".to_owned(),
                    }),
                });
                return c;
            }
            if chars.peek().is_none() {
                return '\0';
            }
        }
    }

    fn parse_string(&mut self, chars: &mut Peekable<Chars>) -> char {
        loop {
            let c = chars.next().unwrap();
            if self.flag {
                self.buffer.push(c);
            } else if c == '"' {
                chars.next().unwrap_or('\0');
            } else if c == '/' {
                self.flag = true;
            } else {
                self.buffer.push(c);
            }
            if chars.peek().is_none() {
                self.flag = true;
                return '\0';
            }
        }
    }

    fn parse_opening_bracket(&mut self, chars: &mut Peekable<Chars>) {
        self.pedigree_of_current_scope.push(chars.next().unwrap());
    }

    fn parse_closing_bracket(&mut self, chars: &mut Peekable<Chars>) {
        match self.pedigree_of_current_scope.pop() {
            Some(c) => {
                if !chars.next().unwrap().is_right_side_of(c) {
                    // TODO
                }
            }
            None => (), // TODO
        }
    }

    fn parse_whitespace(&mut self, chars: &mut Peekable<Chars>) {}

    fn add_token(&mut self, t: Token) {}

    fn peek_position(&mut self, chars: &mut Peekable<Chars>) -> Position {
        let option_c = chars.peek();
        if option_c.is_none() {
            return Position::EOF;
        }
        let c = option_c.unwrap();
        let mut with_chars = WithChars { chars: chars };
        if c.is_whitespace() {
            return Position::Whitespace;
        } else if c.is_word() {
            return Position::Word;
        } else if c.is_opening_bracket() {
            return Position::LBracket;
        } else if c.is_closing_bracket() {
            return Position::RBracket;
        } else if c.is_symbol() {
            return Position::Symbol;
        } else if c.is_string() {
            return Position::String;
        } else if c.is_number() {
            return Position::Number;
        } else {
            return Position::Unknown;
        }
    }
}

pub trait CharUtils {
    fn is_symbol(self) -> bool;
    fn is_opening_bracket(self) -> bool;
    fn is_closing_bracket(self) -> bool;
    fn is_right_side_of(self, c: char) -> bool;
}

impl CharUtils for char {
    fn is_symbol(self) -> bool {
        "/+*-!|%&=?^@#.:,<>".contains(self)
    }

    fn is_opening_bracket(self) -> bool {
        "{[(".contains(self)
    }

    fn is_closing_bracket(self) -> bool {
        "}])".contains(self)
    }

    fn is_right_side_of(self, c: char) -> bool {
        match (c, self) {
            ('(', ')') | ('[', ']') | ('{', '}') => true,
            _ => false,
        }
    }
}

impl Parser {
    fn new() -> Parser {
        Parser {
            ast: Some(Ast::new()),
            feedbacks: Vec::new(),
            pedigree_of_current_scope: String::new(),
            buffer: String::new(),
            flag: false,
        }
    }

    fn parse_word(&mut self, chars: &mut Peekable<Chars>) -> char {
        loop {
            let c = chars.next().unwrap();
            if c.is_alphabetic() {
                self.buffer.push(c);
            } else {
                return c;
            }
            if chars.peek().is_none() {
                return '\0';
            }
        }
    }

    fn parse_symbol(&mut self, chars: &mut Peekable<Chars>) -> char {
        loop {
            let c = chars.next().unwrap();
            if c.is_symbol() {
                self.buffer.push(c);
            } else {
                return c;
            }
            if chars.peek().is_none() {
                return '\0';
            }
        }
    }

    fn parse_number(&mut self, chars: &mut Peekable<Chars>) -> char {
        loop {
            let c = chars.next().unwrap();
            if c.is_digit(10) {
                self.buffer.push(c);
            } else {
                self.add_token(Token {
                    location: Range { start: 0, end: 1 },
                    kind: TokenKind::Number(Number {
                        buffer: "abc".to_owned(),
                    }),
                });
                return c;
            }
            if chars.peek().is_none() {
                return '\0';
            }
        }
    }

    fn parse_string(&mut self, chars: &mut Peekable<Chars>) -> char {
        loop {
            let c = chars.next().unwrap();
            if self.flag {
                self.buffer.push(c);
            } else if c == '"' {
                chars.next().unwrap_or('\0');
            } else if c == '/' {
                self.flag = true;
            } else {
                self.buffer.push(c);
            }
            if chars.peek().is_none() {
                self.flag = true;
                return '\0';
            }
        }
    }

    fn parse_opening_bracket(&mut self, chars: &mut Peekable<Chars>) {
        self.pedigree_of_current_scope.push(chars.next().unwrap());
    }

    fn parse_closing_bracket(&mut self, chars: &mut Peekable<Chars>) {
        match self.pedigree_of_current_scope.pop() {
            Some(c) => {
                if !chars.next().unwrap().is_right_side_of(c) {
                    // TODO
                }
            }
            None => (), // TODO
        }
    }

    fn parse_whitespace(&mut self, chars: &mut Peekable<Chars>) {}

    fn add_token(&mut self, t: Token) {}

    fn peek_position(&mut self, chars: &mut Peekable<Chars>) -> Position {
        let option_c = chars.peek();
        if option_c.is_none() {
            return Position::EOF;
        }
        let c = option_c.unwrap();
        let mut with_chars = WithChars { chars: chars };
        if c.is_whitespace() {
            return Position::Whitespace;
        } else if c.is_word() {
            return Position::Word;
        } else if c.is_opening_bracket() {
            return Position::LBracket;
        } else if c.is_closing_bracket() {
            return Position::RBracket;
        } else if c.is_symbol() {
            return Position::Symbol;
        } else if c.is_string() {
            return Position::String;
        } else if c.is_number() {
            return Position::Number;
        } else {
            return Position::Unknown;
        }
    }
}

pub trait CharUtils {
    fn is_symbol(self) -> bool;
    fn is_opening_bracket(self) -> bool;
    fn is_closing_bracket(self) -> bool;
    fn is_right_side_of(self, c: char) -> bool;
}

impl CharUtils for char {
    fn is_symbol(self) -> bool {
        "/+*-!|%&=?^@#.:,<>".contains(self)
    }

    fn is_opening_bracket(self) -> bool {
        "{[(".contains(self)
    }

    fn is_closing_bracket(self) -> bool {
        "}])".contains(self)
    }

    fn is_right_side_of(self, c: char) -> bool {
        match (c, self) {
            ('(', ')') | ('[', ']') | ('{', '}') => true,
            _ => false,
        }
    }
}
