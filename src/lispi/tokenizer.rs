use std::num::{ParseFloatError, ParseIntError};
use std::str::Chars;

use super::error::*;
use super::*;

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

impl Token {
    fn with_location(self, begin: Location, end: Location) -> TokenWithLocation {
        TokenWithLocation {
            token: self,
            location: LocationRange { begin, end },
        }
    }
}

pub struct TokenWithLocation {
    pub token: Token,
    pub location: LocationRange,
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

fn current_char(line: &Vec<char>, loc: &Location) -> Option<char> {
    if let Some(ch) = line.get(loc.column - 1) {
        return Some(*ch);
    }

    None
}

fn succ<'a>(program: &'a Vec<String>, line: &'a mut Vec<char>, loc: &mut Location) {
    loc.column += 1;
    let c = current_char(&line, loc);
    if let Some(c) = c {
        if c == '\r' || c == '\n' {
            loc.line += 1;
            if let Some(new_line) = program.get(loc.line - 1) {
                *line = new_line.chars().collect();
            }
        }
    }
}

fn tokenize_single<'a>(
    program: &'a Vec<String>,
    line: &'a mut Vec<char>,
    loc: &mut Location,
) -> Result<Option<TokenWithLocation>, Error> {
    if let Some(ch) = current_char(line, loc) {
        let begin = loc.clone();
        let result = match ch {
            '(' => {
                succ(program, line, loc);
                Token::LeftParen.with_location(begin, loc.clone())
            }
            ')' => {
                succ(program, line, loc);
                Token::RightParen.with_location(begin, loc.clone())
            }
            '[' => {
                succ(program, line, loc);
                Token::LeftSquareBracket.with_location(begin, loc.clone())
            } //             ']' => {
            //                 *index += 1;
            //                 Token::RightSquareBracket.with_location(begin, current_loc!())
            //             }
            //             '\'' => {
            //                 *index += 1;
            //                 Token::Quote.with_location(begin, current_loc!())
            //             }
            //             '#' => {
            //                 *index += 1;
            //                 let ret = match program.get(*index) {
            //                     Some('t') => Token::BooleanLiteral(true),
            //                     Some('f') => Token::BooleanLiteral(false),
            //                     Some('\\') => {
            //                         i += 1;
            //                         let c = program
            //                             .get(i)
            //                             .ok_or(Error::Tokenize("Unexpected EOF".to_string()))?;
            //                         Token::CharLiteral(*c)
            //                     }
            //                     Some(c) => Err(Error::Tokenize(format!("Unexpected charactor {}", c)))?,
            //                     None => Err(Error::Tokenize("Unexpected EOF".to_string()))?,
            //                 };
            //                 *index += 1;
            //                 ret.with_location(begin, current_loc!())
            //             }
            //             ';' => {
            //                 let _ = take_while(&program, &mut index, |&c| c != '\n');
            //                 return Ok(None)
            //             }
            //             '"' => {
            //                 *index += 1;

            //                 let value = take_while(&program, &mut index, |&c| c != '"');
            //                 let value = value.join("");

            //                 take_expected(&program, &mut index, '"')?;

            // Token::StringLiteral(value).with_location(begin, current_loc!())
            //             }
            //             c if c.is_ascii_digit() => {
            //                 let int = take_while(&program, &mut i, |c| c.is_ascii_digit());
            //                 let int = int.join("");

            //                 if let Some('.') = program.get(i) {
            //                     i += 1;
            //                     let decimal = take_while(&program, &mut i, |c| c.is_ascii_digit());
            //                     let decimal = decimal.join("");
            //                     let float = (int + "." + &decimal).parse::<f32>()?;
            //                     result.push(Token::FloatLiteral(float));
            //                 } else {
            //                     let int = int.parse::<i32>()?;
            //                     result.push(Token::IntegerLiteral(int));
            //                 }
            //             }
            //             c if c.is_identifier_head() => {
            //                 i += 1;
            //                 let mut chars = vec![c.to_string()];
            //                 let mut rest = take_while(&program, &mut i, |c| c.is_identifier());
            //                 chars.append(&mut rest);
            //                 let value = chars.join("");
            //                 result.push(Token::Identifier(value));
            //             }
            _ => return Ok(None),
        };
        Ok(Some(result))
    } else {
        Ok(None)
    }
}

pub fn tokenize(program: Vec<String>) -> Result<Vec<TokenWithLocation>, Error> {
    let mut result = Vec::new();

    if let Some(mut line) = program.get(0) {
        let mut line: Vec<char> = line.chars().collect();
        let mut loc = Location { line: 1, column: 1 };
        loop {
            let token = tokenize_single(&program, &mut line, &mut loc)?;
            if let Some(token) = token {
                result.push(token);
            } else {
                break;
            }
        }
        Ok(result)
    } else {
        Ok(Vec::new())
    }
}

pub fn show_tokens(tokens: Vec<Token>) -> Result<Vec<Token>, Error> {
    for token in &tokens {
        println!("{:?}", token);
    }
    Ok(tokens)
}

mod tests {
    use super::*;

    #[allow(dead_code)]
    fn toknenize_single(value: &str) -> TokenWithLocation {
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
