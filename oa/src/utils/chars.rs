trait CharUtils {
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
        match (self, c) {
            (')', '(') | (']', '[') | ('}', '{') => true,
            _ => false,
        }
    }
}
