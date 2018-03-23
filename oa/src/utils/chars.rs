impl CharInsights for char {
    fn is_decimal_digit(self) -> bool {
        self.is_digit(10)
    }

    fn is_symbol(self) -> bool {
        "/+*-!|%&=?^@#.:,;<>".contains(self)
    }

    fn is_bracket(self) -> bool {
        "{[()]}".contains(self)
    }

    fn is_whitespace(self) -> bool {
        "\n ".contains(self)
    }
}
