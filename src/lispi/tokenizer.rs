use std::num::{ParseFloatError, ParseIntError};

use super::error::*;

impl From<ParseIntError> for Error {
    fn from(_err: ParseIntError) -> Self {
        Error::Tokenize("Parse int error".to_string())
    }
}

impl From<ParseFloatError> for Error {
    fn from(_err: ParseFloatError) -> Self {
        Error::Tokenize("Parse float error".to_string())
    }
}

#[derive(Debug, PartialEq)]
pub enum Token {
    LeftParen,
    RightParen,
    LeftSquareBracket,
    RightSquareBracket,
    Quote,
    IntegerLiteral(i32),
    FloatLiteral(f32),
    Identifier(String),
    BooleanLiteral(bool),
    CharLiteral(char),
    StringLiteral(String),
}

trait CharExt {
    fn is_identifier_head(&self) -> bool;
    fn is_identifier(&self) -> bool;
}

impl CharExt for char {
    fn is_identifier_head(&self) -> bool {
        match *self {
            c if c.is_ascii_alphabetic() => true,
            '!' | '$' | '%' | '&' | '*' | '/' | ':' | '<' | '=' | '>' | '?' | '@' | '^' | '_'
            | '~' | '+' | '-' | '.' => true,
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

fn take_expected(program: &Vec<char>, index: &mut usize, expected: char) -> Result<(), Error> {
    if let Some(c) = program.get(*index) {
        if c == &expected {
            *index += 1;
            Ok(())
        } else {
            Err(Error::Tokenize(format!("Unexpected {}", c)))
        }
    } else {
        Err(Error::Tokenize("Unexpected EOF".to_string()))
    }
}

pub fn tokenize(lines: Vec<String>) -> Result<Vec<Token>, Error> {
    let program = lines.join("\n");
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
            '[' => {
                result.push(Token::LeftSquareBracket);
                i += 1;
            }
            ']' => {
                result.push(Token::RightSquareBracket);
                i += 1;
            }
            '\'' => {
                result.push(Token::Quote);
                i += 1;
            }
            '#' => {
                i += 1;
                let ret = match program.get(i) {
                    Some('t') => Token::BooleanLiteral(true),
                    Some('f') => Token::BooleanLiteral(false),
                    Some('\\') => {
                        i += 1;
                        let c = program
                            .get(i)
                            .ok_or(Error::Tokenize("Unexpected EOF".to_string()))?;
                        Token::CharLiteral(*c)
                    }
                    Some(c) => Err(Error::Tokenize(format!("Unexpected charactor {}", c)))?,
                    None => Err(Error::Tokenize("Unexpected EOF".to_string()))?,
                };
                result.push(ret);
                i += 1;
            }
            ';' => {
                let _ = take_while(&program, &mut i, |&c| c != '\n');
                i += 1;
            }
            '"' => {
                i += 1;

                let value = take_while(&program, &mut i, |&c| c != '"');
                let value = value.join("");
                result.push(Token::StringLiteral(value));

                take_expected(&program, &mut i, '"')?;
            }
            c if c.is_ascii_digit() => {
                let int = take_while(&program, &mut i, |c| c.is_ascii_digit());
                let int = int.join("");

                if let Some('.') = program.get(i) {
                    i += 1;
                    let decimal = take_while(&program, &mut i, |c| c.is_ascii_digit());
                    let decimal = decimal.join("");
                    let float = (int + "." + &decimal).parse::<f32>()?;
                    result.push(Token::FloatLiteral(float));
                } else {
                    let int = int.parse::<i32>()?;
                    result.push(Token::IntegerLiteral(int));
                }
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

mod tests {
    use super::*;

    fn toknenize_single(value: &str) -> Token {
        tokenize(vec![value.to_string()])
            .unwrap()
            .into_iter()
            .next()
            .unwrap()
    }

    #[test]
    fn test_tokenize_float() {
        assert_eq!(toknenize_single("3.14"), Token::FloatLiteral(3.14));
        assert_eq!(toknenize_single("3.0"), Token::FloatLiteral(3.0));
    }
}
