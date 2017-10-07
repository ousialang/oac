/// Tokenize a string according to Ousia's grammar.
pub fn tokenize(source: &str) -> Result<Vec<Token>, (u64, &str)> {
    let mut tokens = Vec::new();
    if source.is_empty() {
        return Ok(tokens);
    }
    let source_chars = &mut source.chars();
    let first_char = source_chars.nth(0).unwrap();
    // We already populate the token with the info of the first char.
    let current_token = &mut Token {
        lexeme: first_char.to_string(),
        location: 0,
        data: fetch_token_entity(first_char),
    };
    // If we know the current token is over, be make this true so the main loop
    // knows to create a new Token with updated info.
    let mut flag_is_new_token = false;
    // Various flags to keep track of tokenization. They all refer to the last
    // seen char.
    let mut flag_is_zero = false;
    let mut flag_is_period = false;
    let mut flag_is_backslash = false;
    // To keep track of opened brackets, so we catch non-matching brackets
    // errors early into the parsing process.
    let mut brackets = String::new();
    let mut brackets_len = 0u16;
    // Main loop does two things:
    //   1. Instantiate a new token if flag_is_new_token
    //   2. Updating the old one otherwise
    for (index, c) in source_chars.enumerate() {
        let new_data = fetch_token_entity(c);
        if flag_is_new_token || new_data != current_token.data {
            let current_token = &mut Token {
                lexeme: c.to_string(),
                location: index,
                data: new_data,
            };
            flag_is_new_token = false;
            continue;
        } else {
            current_token.lexeme.push(c);
            match current_token.data {
                TokenEntity::Literal {ref mut string} => {
                    if c == '"' {
                        if flag_is_backslash {
                            string.push('\"');
                        } else {
                            flag_is_new_token = true;
                        }
                    } else {
                        string.push(c);
                    }
                }
                // TODO
                TokenEntity::Number {..} |
                TokenEntity::Word |
                TokenEntity::Symbol |
                TokenEntity::Other |
                TokenEntity::Whitespace => {}
                TokenEntity::Bracket => {
                    let current_token_copy = (*current_token).clone();
                    tokens.push(current_token_copy);
                    tokens.push(Token {
                        lexeme: c.to_string(),
                        location: index,
                        data: TokenEntity::Bracket,
                    });
                }
            }
        }
    }
    println!("{:?}", tokens);
    Ok(tokens)
}

#[derive(PartialEq, Clone, Debug)]
enum TokenEntity {
    Literal {string: String},
    Number {base: u8, integer_digits: String, decimal_digits: String},
    Word,
    Symbol,
    Bracket, // Might be parentheses, square brackets, or braces.
    Whitespace,
    Other,
}
#[derive(Clone, Debug)]
pub struct Token {
    lexeme: String,
    location: usize, // The index in the source string.
    data: TokenEntity,
}

fn fetch_token_entity(c: char) -> TokenEntity {
    // In case the token is longer than one single character, its type
    // (entity) is always determined by its first character.
    if "{}[]()".contains(c) {
        return TokenEntity::Bracket;
    } else if c.is_alphabetic() {
        return TokenEntity::Word;
    } else if "/+*-!|%&=?^@#.:,;".contains(c) {
        return TokenEntity::Symbol;
    } else if c == '"' {
        return TokenEntity::Literal {string: String::new()};
    } else if c == '0' {
        // We put base 0 waiting for the real base to be parsed int he next
        // character.
        return TokenEntity::Number {base: 0, integer_digits: String::new(), decimal_digits: String::new()};
    } else if "123456789".contains(c) {
        return TokenEntity::Number {base: 10, integer_digits: c.to_string(), decimal_digits: String::new()};
    } else {
        return TokenEntity::Other;
    }
}
