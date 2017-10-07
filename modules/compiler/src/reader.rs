/// Tokenize a string according to Ousia's grammar.
pub fn tokenize(source: &str) -> Result<Vec<Token>, (u64, &str)> {
    let mut tokens = Vec::new();

    if source.is_empty() {
        return Ok(tokens);
    }

    let mut source_chars = source.chars();
    let first_char = source_chars.nth(0).unwrap();

    let mut current_token = Token {
        lexeme: first_char.to_string(),
        location: 0,
        meta: fetch_token_entity(first_char),
    };

    let mut flag_is_zero = false;
    let mut flag_is_period = false;
    let mut flag_is_backslash = false;

    // To keep track of opened brackets, so we catch non-matching brackets
    // errors early into the parsing process.
    let mut brackets = String::new();

    for charr in source_chars {
        current_token.lexeme.push(charr);
        match current_token.meta {
            TokenEntity::Literal {..} => {
                if !(flag_is_backslash) && charr == '"' {

                } else {
                    //current_token.data.string.push("\"");
                }
            },
            TokenEntity::Number {..} => {
            },
            TokenEntity::Word | TokenEntity::Symbol => {

            },
            TokenEntity::Other => {

            },
            _ => {}
        }
    }

    Ok(tokens)
}

#[derive(PartialEq)]
enum TokenEntity {
    Literal {string: String},
    Number {base: u8, integer_digits: String, decimal_digits: String},
    Word,
    Symbol,
    Bracket, // Might be parentheses, square brackets, or braces.
    Whitespace,
    Other,
}

pub struct Token {
    lexeme: String,
    location: u64, // The index in the source string.
    meta: TokenEntity,
}

fn fetch_token_entity(c: char) -> TokenEntity {
    // In case the token is longer than one single character, its type
    // (entity) is always determined by its first character.
    if "{}[]()".contains(c) {
        return TokenEntity::Bracket;
    } else if c.is_alphabetic() {
        return TokenEntity::Word;
    } else if "*/+-!|%&=?^@#.:,;".contains(c) {
        return TokenEntity::Symbol;
    } else if c == '"' {
        return TokenEntity::Literal {string: String::new()};
    } else if c.is_digit(10) {
        return TokenEntity::Number {base: 10, integer_digits: String::new(), decimal_digits: String::new()};
    } else {
        return TokenEntity::Other;
    }
}
