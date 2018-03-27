trait CharUtils {
    fn is_symbol(self) -> bool;
    fn is_opening_bracket(self) -> bool;
    fn is_closing_bracket(self) -> bool;
    fn is_right_side_of(self, c: char) -> bool;
    fn is_whitespace(self) -> bool;
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
        let ascii = self as u8;
        // https://www.youtube.com/watch?v=aboZctrHfK8
        c as u8 == ascii - 1 - ((ascii > 42) as u8)
    }

    fn is_whitespace(self) -> bool {
        "\n\t ".contains(self)
    }
}
