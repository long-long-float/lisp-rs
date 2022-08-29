use std::num::{ParseFloatError, ParseIntError};

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

    /// Unused token such as new line, space
    Other,
    EOF,
}

impl Token {
    fn with_location(self, begin: Location, end: Location) -> TokenWithLocation {
        TokenWithLocation {
            token: self,
            location: LocationRange { begin, end },
        }
    }
}

#[derive(PartialEq, Debug)]
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

fn take_while(
    program: &Vec<String>,
    line: &mut Vec<char>,
    loc: &mut Location,
    pred: fn(char) -> bool,
) -> Vec<String> {
    let mut buf = Vec::new();
    while let Some(ch) = current_char(line, loc) {
        if !pred(ch) {
            break;
        }
        buf.push(ch.to_string());

        succ(program, line, loc);
    }
    buf
}

fn take_expected(
    program: &Vec<String>,
    line: &mut Vec<char>,
    loc: &mut Location,
    expected: char,
) -> Result<(), Error> {
    if let Some(c) = current_char(line, loc) {
        if c == expected {
            succ(program, line, loc);
            Ok(())
        } else {
            Err(Error::Tokenize(format!("Unexpected {}", c)))
        }
    } else {
        Err(Error::Tokenize("Unexpected EOF".to_string()))
    }
}

fn current_char(line: &Vec<char>, loc: &Location) -> Option<char> {
    if let Some(ch) = line.get(loc.column) {
        Some(*ch)
    } else {
        None
    }
}

fn succ<'a>(program: &'a Vec<String>, line: &'a mut Vec<char>, loc: &mut Location) {
    loc.column += 1;
    let c = current_char(&line, loc);
    let nl = if let Some(c) = c {
        if c == '\r' || c == '\n' {
            true
        } else {
            false
        }
    } else {
        true
    };

    if nl {
        loc.newline();
        if let Some(new_line) = program.get(loc.line) {
            *line = new_line.chars().collect();
        } else {
            *line = Vec::new();
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
            }
            ']' => {
                succ(program, line, loc);
                Token::RightSquareBracket.with_location(begin, loc.clone())
            }
            '\'' => {
                succ(program, line, loc);
                Token::Quote.with_location(begin, loc.clone())
            }
            '#' => {
                succ(program, line, loc);
                let ret = match current_char(line, loc) {
                    Some('t') => Token::BooleanLiteral(true),
                    Some('f') => Token::BooleanLiteral(false),
                    Some('\\') => {
                        succ(program, line, loc);
                        let c = current_char(line, loc)
                            .ok_or(Error::Tokenize("Unexpected EOF".to_string()))?;
                        Token::CharLiteral(c)
                    }
                    Some(c) => Err(Error::Tokenize(format!("Unexpected charactor {}", c)))?,
                    None => Err(Error::Tokenize("Unexpected EOF".to_string()))?,
                };
                succ(program, line, loc);
                ret.with_location(begin, loc.clone())
            }
            ';' => {
                let _ = take_while(program, line, loc, |c| c != '\n');
                return Ok(None);
            }
            '"' => {
                succ(program, line, loc);

                let value = take_while(program, line, loc, |c| c != '"');
                let value = value.join("");

                take_expected(&program, line, loc, '"')?;

                Token::StringLiteral(value).with_location(begin, loc.clone())
            }
            c if c.is_ascii_digit() => {
                let int = take_while(program, line, loc, |c| c.is_ascii_digit());
                let int = int.join("");

                if let Some('.') = current_char(line, loc) {
                    succ(program, line, loc);
                    let decimal = take_while(program, line, loc, |c| c.is_ascii_digit());
                    let decimal = decimal.join("");
                    let float = (int + "." + &decimal).parse::<f32>()?;
                    Token::FloatLiteral(float).with_location(begin, loc.clone())
                } else {
                    let int = int.parse::<i32>()?;
                    Token::IntegerLiteral(int).with_location(begin, loc.clone())
                }
            }
            c if c.is_identifier_head() => {
                succ(program, line, loc);

                let mut chars = vec![c.to_string()];
                let mut rest = take_while(program, line, loc, |c| c.is_identifier());
                chars.append(&mut rest);

                let value = chars.join("");
                Token::Identifier(value).with_location(begin, loc.clone())
            }
            _ => {
                succ(program, line, loc);
                Token::Other.with_location(Location::head(), Location::head())
            }
        };
        Ok(Some(result))
    } else {
        let token = if loc.line < program.len() - 1 {
            succ(program, line, loc);
            Token::Other
        } else {
            Token::EOF
        };

        Ok(Some(
            token.with_location(Location::head(), Location::head()),
        ))
    }
}

pub fn tokenize(program: Vec<String>) -> Result<Vec<TokenWithLocation>, Error> {
    let mut result = Vec::new();

    if let Some(line) = program.get(0) {
        let mut line: Vec<char> = line.chars().collect();
        let mut loc = Location::head();
        loop {
            let token = tokenize_single(&program, &mut line, &mut loc)?;
            if let Some(token) = token {
                match token.token {
                    Token::Other => {}
                    Token::EOF => break,
                    _ => result.push(token),
                }
            }
        }
        Ok(result)
    } else {
        Ok(Vec::new())
    }
}

pub fn show_tokens(tokens: Vec<TokenWithLocation>) -> Result<Vec<TokenWithLocation>, Error> {
    for TokenWithLocation { token, location } in &tokens {
        println!("{:?} @ {}-{}", token, location.begin, location.end);
    }
    Ok(tokens)
}

mod tests {
    use super::*;

    #[allow(dead_code)]
    fn toknenize_single(value: &str) -> Token {
        tokenize(vec![value.to_string()])
            .unwrap()
            .into_iter()
            .next()
            .unwrap()
            .token
    }

    #[test]
    fn test_tokenize_float() {
        assert_eq!(toknenize_single("3.14"), Token::FloatLiteral(3.14));
        assert_eq!(toknenize_single("3.0"), Token::FloatLiteral(3.0));
    }
}
