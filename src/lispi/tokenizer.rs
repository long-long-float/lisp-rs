use std::num::ParseIntError;

use super::error::*;

impl From<ParseIntError> for Error {
    fn from(err: ParseIntError) -> Self {
        Error::Tokenize("Parse int error".to_string())
    }
}

#[derive(Debug, PartialEq)]
pub enum Token {
    LeftParen,
    RightParen,
    IntegerLiteral(i32),
    Identifier(String),
}

impl Token {
    fn is_integer(&self) -> bool {
        if let Token::IntegerLiteral(_) = self {
            true
        } else {
            false
        }
    }

    fn is_identifier(&self) -> bool {
        if let Token::Identifier(_) = self {
            true
        } else {
            false
        }
    }
}

trait CharExt {
    fn is_identifier_head(&self) -> bool;
    fn is_identifier(&self) -> bool;
}

impl CharExt for char {
    fn is_identifier_head(&self) -> bool {
        match *self {
            c if c.is_ascii_alphabetic() => true,
            '+' | '-' | '*' | '/' | '@' | '$' | '^' | '&' | '_' | '=' | '<' | '>' | '~' | '.' => {
                true
            }
            _ => false,
        }
    }

    fn is_identifier(&self) -> bool {
        self.is_identifier_head() || self.is_ascii_digit()
    }
}

fn take_while(program: &Vec<char>, index: &mut usize, pred: fn(&char) -> bool) -> Vec<String> {
    let mut buf = Vec::new();
    while let Some(ch) = program.get(*index) {
        if !pred(ch) {
            break;
        }
        buf.push(ch.to_string());

        *index += 1;
    }
    buf
}

pub fn tokenize(lines: Vec<String>) -> Result<Vec<Token>, Error> {
    let program = lines.join(" ");
    let program: Vec<char> = program.chars().collect();

    let mut result = Vec::new();

    let mut i = 0;
    while let Some(ch) = program.get(i) {
        match ch {
            '(' => {
                result.push(Token::LeftParen);
                i += 1;
            }
            ')' => {
                result.push(Token::RightParen);
                i += 1;
            }
            c if c.is_ascii_digit() => {
                let buf = take_while(&program, &mut i, |c| c.is_ascii_digit());
                let value = buf.join("").parse::<i32>()?;
                result.push(Token::IntegerLiteral(value));
            }
            c if c.is_identifier_head() => {
                i += 1;
                let mut chars = vec![c.to_string()];
                let mut rest = take_while(&program, &mut i, |c| c.is_identifier());
                chars.append(&mut rest);
                let value = chars.join("");
                result.push(Token::Identifier(value));
            }
            _ => {
                i += 1;
            }
        }
    }

    Ok(result)
}

pub fn show_tokens(tokens: Vec<Token>) -> Result<Vec<Token>, Error> {
    for token in &tokens {
        println!("{:?}", token);
    }
    Ok(tokens)
}
