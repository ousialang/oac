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
    match fetch_matching_brackets_feedback(tokens) {
        Some(body) => {
            return Err(body);
        }
        None => {
            return Ok(tokens_clone);
        }
    }
}

fn fetch_matching_brackets_feedback(tokens: Vec<Token>) -> Option<Feedback> {
    let mut brackets: Vec<char> = Vec::new();
    for token in tokens {
        if token.data != TokenData::Bracket {
            continue;
        }
        let c = token.lexeme.chars().nth(0).unwrap();
        if "([{".contains(c) {
            brackets.push(c);
            continue;
        }
        let j = c as u8;
        let ascii1 = j - 1 - (j>90) as u8;
        let ascii2 = *(brackets.last().unwrap_or(&'-')) as u8;
        // Ascii magic trick: 40 -> 41, 91 -> 93, 123 -> 125
        if ascii1 != ascii2 || brackets.pop().is_none() {
            return Some(Feedback {
                title: format!("Unexpected bracket `{}` at position {}", c, token.location),
                ..Default::default()
            });
        }
    }
    if brackets.len() > 0 {
        return Some(Feedback {
            title: "Unclosed bracket `{w` at position {w".to_string(),
            ..Default::default()
        });
    }
    None
}

fn remove_whitespace(mut tokens: Vec<Token>) -> Vec<Token> {
    tokens.retain(|t|
        t.data != TokenData::Whitespace ||
        t.lexeme.contains('\n')
    );
    tokens
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
    "/+*-!|%&=?^@#.:,;<>".contains(c)
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
        TokenData::Number => condition = is_digit(c),
        TokenData::Word => condition = is_letter(c),
        TokenData::Symbol => condition = is_symbol(c),
        TokenData::Whitespace => condition = is_whitespace(c),
        TokenData::Other | TokenData::Bracket => condition = false,
    }
    if condition {
        t.lexeme.push(c);
    } else {
        return Err(None);
    }
    Ok(t)
}
