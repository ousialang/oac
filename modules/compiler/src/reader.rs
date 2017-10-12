use errors;

/// Tokenize a string according to Ousia's grammar.
pub fn tokenize(source: &str) -> Result<Vec<Token>, errors::Message> {
    let mut tokens = Vec::new();
    if source.is_empty() {
        return Ok(tokens);
    }
    let mut source_chars = source.chars();
    let first_char = source_chars.nth(0).unwrap();
    // We already populate the token with the info of the first char.
    tokens.push(fetch_init_token(first_char, 0));
    // To keep track of opened brackets, so we catch non-matching brackets
    // errors early into the parsing process.
    let mut brackets = String::new();
    let mut brackets_len = 0u16;
    // Main loop does two things:
    //   1. Instantiate a new token if flag_is_new_token
    //   2. Updating the old one otherwise
    for (index, c) in source_chars.enumerate() {
        let mut token = &mut tokens.pop().unwrap();
        let token_clone = token.clone();
        let new_token = update_token(token, c);
        match new_token {
            Err(None) => {
                tokens.push(token_clone);
                tokens.push(fetch_init_token(c, 1+index as u64));
            }
            Ok(t) => {
                tokens.push((*t).clone());
            }
            _ => {}
        }
    }
    println!("  {:?}", tokens);
    Ok(tokens)
}

#[derive(PartialEq, Clone, Debug)]
enum TokenData {
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
    location: u64, // The index in the source string.
    data: TokenData,
}

fn fetch_init_token(c: char, location: u64) -> Token {
    let data: TokenData;
    if is_bracket(c) {
        data = TokenData::Bracket;
    } else if is_letter(c) {
        data = TokenData::Word;
    } else if is_symbol(c) {
        data = TokenData::Symbol;
    } else if c == '"' {
        data = TokenData::Literal {string: String::new()};
    } else if c == '0' {
        // We put base 0 waiting for the real base to be parsed int he next
        // character.
        data = TokenData::Number {base: 0, integer_digits: String::new(), decimal_digits: String::new()};
    } else if "123456789".contains(c) {
        data = TokenData::Number {base: 10, integer_digits: c.to_string(), decimal_digits: String::new()};
    } else if is_whitespace(c) {
        data = TokenData::Whitespace;
    } else {
        data = TokenData::Other;
    }
    Token {
        lexeme: c.to_string(),
        location: location,
        data: data,
    }
}

fn is_symbol(c: char) -> bool {
    "/+*-!|%&=?^@#.:,;".contains(c)
}
fn is_letter(c: char) -> bool {
    c.is_alphabetic()
}
fn is_bracket(c: char) -> bool {
    "{[()]}".contains(c)
}
fn is_whitespace(c: char) -> bool {
    "\n ".contains(c)
}

fn update_token(t: &mut Token, c: char) -> Result<&mut Token, Option<errors::Message>> {
    let mut condition = false;
    match t.data {
        TokenData::Literal {ref mut string} => {
            condition = t.lexeme.pop().unwrap() == '\\' || c != '"'
        }
        TokenData::Number {
            ref mut base,
            ref mut integer_digits,
            ref mut decimal_digits
        } => { /*
            if t.lexeme.len() == 1 && t.pop() == '0' {
                match c {
                    'b' => { t.data.base = 2; }
                    'o' => { t.data.base = 8; }
                    'x' => { t.data.base = 16; }
                    _ => { return Err("Expected"); }
                }
            }*/
        }
        TokenData::Word => { condition = is_letter(c); }
        TokenData::Symbol => { condition = is_symbol(c); }
        TokenData::Whitespace => { condition = is_whitespace(c); }
        TokenData::Other |
        TokenData::Bracket => { return Err(None); }
    }
    if condition {
        t.lexeme.push(c);
    } else {
        return Err(None);
    }
    Ok(t)
}
