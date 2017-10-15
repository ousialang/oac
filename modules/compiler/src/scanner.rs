use feedback::Feedback;

/// Tokenize a string according to Ousia's grammar.
pub fn scan(source: &str) -> Result<Vec<Token>, Feedback> {
    let mut tokens = Vec::new();
    if source.is_empty() {
        return Ok(tokens);
    }
    let mut source_chars = source.chars();
    let first_char = source_chars.nth(0).unwrap();
    // We already populate the token with the info of the first char.
    tokens.push(fetch_init_token(first_char, 0));
    for (index, c) in source_chars.enumerate() {
        let mut token = &mut tokens.pop().unwrap();
        let token_clone = token.clone();
        let new_token = update_token(token, c);
        match new_token {
            Err(None) => {
                tokens.push(token_clone);
                tokens.push(fetch_init_token(c, 1 + index as u64));
            }
            Ok(t) => {
                tokens.push((*t).clone());
            }
            _ => {}
        }
    }
    let tokens_clone = tokens.clone();
    match has_balanced_brackets(tokens) {
        Some(body) => {
            return Err(body);
        }
        None => {
            return Ok(tokens_clone);
        }
    }
}

fn has_balanced_brackets(tokens: Vec<Token>) -> Option<Feedback> {
    let mut brackets = String::new();
    let mut brackets_count = 0;
    for token in tokens {
        if token.data != TokenData::Bracket {
            continue;
        }
        let c = token.lexeme.chars().nth(0).unwrap();
        if "([{".contains(c) {
            brackets.push(c);
            brackets_count += 1;
        } else {
            let last = brackets.chars().last().unwrap_or('?');
            match c {
                ')' => {
                    if last == '(' {
                        brackets.pop();
                        brackets_count -= 1;
                    } else {
                        return Some(Feedback { title: "bracket".to_string(), ..Default::default() });
                    }
                }
                ']' => {
                    if last == '[' {
                        brackets.pop();
                        brackets_count -= 1;
                    } else {
                        return Some(Feedback { body: "bracket".to_string(), ..Default::default() });
                    }
                }
                '}' => {
                    if last == '{' {
                        brackets.pop();
                        brackets_count -= 1;
                    } else {
                        return Some(Feedback { body: "bracket".to_string(), ..Default::default() });
                    }
                }
                _ => {}
            }
        }
        if brackets_count < 0 {
            return Some(Feedback { body: "bracket".to_string(), ..Default::default() });
        }
    }
    None
}

#[derive(PartialEq, Clone, Debug)]
enum TokenData {
    Literal,
    Number,
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
        data = TokenData::Literal;
    } else if is_digit(c) {
        data = TokenData::Number;
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

fn is_digit(c: char) -> bool {
    c.is_digit(10)
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

fn update_token(t: &mut Token, c: char) -> Result<&mut Token, Option<Feedback>> {
    let condition: bool;
    match t.data {
        TokenData::Literal => condition = t.lexeme.pop().unwrap() == '\\' || c != '"',
        TokenData::Number => {
            condition = is_digit(c);
        }
        TokenData::Word => {
            condition = is_letter(c);
        }
        TokenData::Symbol => {
            condition = is_symbol(c);
        }
        TokenData::Whitespace => {
            condition = is_whitespace(c);
        }
        TokenData::Other | TokenData::Bracket => {
            condition = false;
        }
    }
    if condition {
        t.lexeme.push(c);
    } else {
        return Err(None);
    }
    Ok(t)
}
