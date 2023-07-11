use anyhow::Result;
use std::fmt::Display;
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
    Colon,
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

    fn push_front_to_identifier(self, str: String) -> Token {
        match self {
            Token::Identifier(id) => {
                let id = str + &id;
                Token::Identifier(id)
            }
            _ => self,
        }
    }
}

#[derive(PartialEq, Debug)]
pub struct TokenWithLocation {
    pub token: Token,
    pub location: LocationRange,
}

impl Display for TokenWithLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let LocationRange { begin, end } = &self.location;
        let loc = format!("@{}-{}", begin, end);
        write!(f, "{:?}{}", self.token, loc.dimmed())
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
            '!' | '$' | '%' | '&' | '*' | '/' | '<' | '=' | '>' | '?' | '@' | '^' | '_' | '~'
            | '+' | '-' | '.' => true,
            _ => false,
        }
    }

    fn is_identifier(&self) -> bool {
        self.is_identifier_head() || self.is_ascii_digit()
    }
}

fn take_while(
    program: &[String],
    line: &mut Vec<char>,
    loc: &mut Location,
    pred: fn(char) -> bool,
) -> Vec<String> {
    let mut buf = Vec::new();
    while let Ok(ch) = current_char(line, loc) {
        if !pred(ch) {
            break;
        }
        buf.push(ch.to_string());

        succ(program, line, loc);
    }
    buf
}

fn take_expected(
    program: &[String],
    line: &mut Vec<char>,
    loc: &mut Location,
    expected: char,
) -> Result<()> {
    let c = current_char(line, loc)?;
    if c == expected {
        succ(program, line, loc);
        Ok(())
    } else {
        Err(Error::Tokenize(format!("Unexpected {}", c))
            .with_single_location(*loc)
            .into())
    }
}

fn current_char(line: &[char], loc: &Location) -> Result<char> {
    if let Some(ch) = line.get(loc.column) {
        Ok(*ch)
    } else {
        Err(Error::Tokenize("Unexpected EOF".to_string())
            .with_single_location(*loc)
            .into())
    }
}

fn move_to_next_line<'a>(program: &'a [String], line: &'a mut Vec<char>, loc: &mut Location) {
    loc.newline();
    if let Some(new_line) = program.get(loc.line) {
        *line = new_line.chars().collect();
    } else {
        *line = Vec::new();
    }
}

/// Move loc to next location.
///
/// Returned value is moved location, however it is not next line when the column reaches the end of line.
fn succ<'a>(program: &'a [String], line: &'a mut Vec<char>, loc: &mut Location) -> Location {
    loc.column += 1;

    let result = *loc;

    let c = current_char(line, loc);
    let nl = if let Ok(c) = c {
        c == '\r' || c == '\n'
    } else {
        true
    };

    if nl {
        move_to_next_line(program, line, loc);
    }

    result
}

fn tokenize_number(
    program: &[String],
    line: &mut Vec<char>,
    loc: &mut Location,
    begin: Location,
    sign: bool,
) -> Result<TokenWithLocation> {
    let head = current_char(line, loc)?;

    match head {
        '0' => {
            // hex or binary
            succ(program, line, loc);
            let head = current_char(line, loc)?;
            match head {
                'x' | 'b' => {
                    succ(program, line, loc);

                    let int = take_while(program, line, loc, |c| c.is_ascii_hexdigit()).join("");
                    let radix = if head == 'x' { 16 } else { 2 };
                    let int = i32::from_str_radix(int.as_str(), radix)?;
                    let int = if sign { int } else { -int };

                    Ok(Token::IntegerLiteral(int).with_location(begin, *loc))
                }
                _ => {
                    // Just 0
                    Ok(Token::IntegerLiteral(0).with_location(begin, *loc))
                }
            }
        }
        _ => {
            // ordinary integer
            let int = take_while(program, line, loc, |c| c.is_ascii_digit()).join("");

            if let Ok('.') = current_char(line, loc) {
                succ(program, line, loc);
                let decimal = take_while(program, line, loc, |c| c.is_ascii_digit()).join("");
                let float = (int + "." + &decimal).parse::<f32>()?;
                let float = if sign { float } else { -float };
                Ok(Token::FloatLiteral(float).with_location(begin, *loc))
            } else {
                let int = int.parse::<i32>()?;
                let int = if sign { int } else { -int };
                Ok(Token::IntegerLiteral(int).with_location(begin, *loc))
            }
        }
    }
}

fn tokenize_identifier(
    program: &[String],
    line: &mut Vec<char>,
    loc: &mut Location,
    begin: Location,
) -> Result<TokenWithLocation> {
    let chars = take_while(program, line, loc, |c| c.is_identifier());

    let value = chars.join("");
    Ok(Token::Identifier(value).with_location(begin, *loc))
}

/// Get a single token from program and move loc to the location of next token
fn tokenize_single<'a>(
    program: &'a Vec<String>,
    line: &'a mut Vec<char>,
    loc: &mut Location,
) -> Result<Option<TokenWithLocation>> {
    if let Ok(ch) = current_char(line, loc) {
        let begin = *loc;
        let result = match ch {
            '(' => {
                let end = succ(program, line, loc);
                Token::LeftParen.with_location(begin, end)
            }
            ')' => {
                let end = succ(program, line, loc);
                Token::RightParen.with_location(begin, end)
            }
            '[' => {
                succ(program, line, loc);
                Token::LeftSquareBracket.with_location(begin, *loc)
            }
            ']' => {
                succ(program, line, loc);
                Token::RightSquareBracket.with_location(begin, *loc)
            }
            '\'' => {
                succ(program, line, loc);
                Token::Quote.with_location(begin, *loc)
            }
            '#' => {
                succ(program, line, loc);
                let ret = match current_char(line, loc)? {
                    't' => Token::BooleanLiteral(true),
                    'f' => Token::BooleanLiteral(false),
                    '\\' => {
                        succ(program, line, loc);
                        let c = current_char(line, loc)?;
                        Token::CharLiteral(c)
                    }
                    c => Err(Error::Tokenize(format!("Unexpected charactor {}", c))
                        .with_single_location(*loc))?,
                };
                succ(program, line, loc);
                ret.with_location(begin, *loc)
            }
            '\\' => {
                succ(program, line, loc);
                let ch = current_char(line, loc)?;
                succ(program, line, loc);

                Token::CharLiteral(ch).with_location(begin, *loc)
            }
            ';' => {
                move_to_next_line(program, line, loc);
                return Ok(None);
            }
            ':' => {
                succ(program, line, loc);
                Token::Colon.with_location(begin, *loc)
            }
            '"' => {
                succ(program, line, loc);

                let value = take_while(program, line, loc, |c| c != '"');
                let value = value.join("");
                let value = value.replace("\\r", "\r");
                let value = value.replace("\\n", "\n");
                let value = value.replace("\\t", "\t");

                take_expected(program, line, loc, '"')?;

                Token::StringLiteral(value).with_location(begin, *loc)
            }
            // Unary operator
            '+' | '-' => {
                let op = current_char(line, loc).unwrap();
                let end = succ(program, line, loc);

                if let Ok(ch) = current_char(line, loc) {
                    if ch.is_ascii_digit() {
                        let sign = op == '+';
                        tokenize_number(program, line, loc, begin, sign)?
                    } else {
                        let mut token = tokenize_identifier(program, line, loc, begin)?;
                        token.token = token.token.push_front_to_identifier(op.to_string());
                        token
                    }
                } else {
                    Token::Identifier(op.to_string()).with_location(begin, end)
                }
            }
            c if c.is_ascii_digit() => tokenize_number(program, line, loc, begin, true)?,
            c if c.is_identifier_head() => tokenize_identifier(program, line, loc, begin)?,
            ' ' | '\n' | '\r' => {
                succ(program, line, loc);
                Token::Other.with_location(Location::head(), Location::head())
            }
            c => {
                return Err(Error::Tokenize(format!("Unexpected charactor `{:?}`", c))
                    .with_location(TokenLocation::Range(LocationRange::new(begin, *loc)))
                    .into())
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

/// Get tokens with its location from program.
///
/// This step is to ease parsing step.
pub fn tokenize(program: Vec<String>) -> Result<Vec<TokenWithLocation>> {
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

pub fn show_tokens(tokens: Vec<TokenWithLocation>) -> Result<Vec<TokenWithLocation>> {
    for TokenWithLocation { token, location } in &tokens {
        println!("{:?} @ {}", token, location);
    }
    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tok(value: &str) -> Token {
        tokenize(vec![value.to_string()])
            .unwrap()
            .into_iter()
            .next()
            .unwrap()
            .token
    }

    #[test]
    fn test_tokenize_number_float() {
        #[allow(clippy::approx_constant)]
        let pi = 3.14;
        assert_eq!(tok("3.14"), Token::FloatLiteral(pi));
        assert_eq!(tok("3.0"), Token::FloatLiteral(3.0));
    }

    #[test]
    fn test_tokenize_number_sign() {
        assert_eq!(tok("+3"), Token::IntegerLiteral(3));
        assert_eq!(tok("-3"), Token::IntegerLiteral(-3));
    }

    #[test]
    fn test_tokenize_number_hex() {
        assert_eq!(tok("0xFF"), Token::IntegerLiteral(255));
        assert_eq!(tok("0xff"), Token::IntegerLiteral(255));

        assert_eq!(tok("-0xff"), Token::IntegerLiteral(-255));
    }

    #[test]
    fn test_tokenize_number_bin() {
        assert_eq!(tok("0b0110"), Token::IntegerLiteral(6));
        assert_eq!(tok("-0b0110"), Token::IntegerLiteral(-6));
    }

    #[test]
    fn test_tokenize_identifier() {
        assert_eq!(tok("+test"), Token::Identifier("+test".to_string()));
        assert_eq!(tok("-test"), Token::Identifier("-test".to_string()));
        assert_eq!(tok("+"), Token::Identifier("+".to_string()));
        assert_eq!(tok("-"), Token::Identifier("-".to_string()));
    }

    #[test]
    fn test_tokenize_char() {
        assert_eq!(tok("#\\a"), Token::CharLiteral('a'));
        assert_eq!(tok("#\\あ"), Token::CharLiteral('あ'));
        assert_eq!(tok("\\a"), Token::CharLiteral('a'));
    }
}
