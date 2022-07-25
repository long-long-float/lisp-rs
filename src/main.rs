use std::env;
use std::fs::File;
use std::io::{self, BufRead};
use std::num::ParseIntError;
use std::path::Path;
use std::result::Result;

#[derive(Debug)]
enum Error {
    Io(String),
    Tokenize(String),
    Parse(String),
    Eval(String),
}

impl From<ParseIntError> for Error {
    fn from(err: ParseIntError) -> Self {
        Error::Tokenize("Parse int error".to_string())
    }
}

#[derive(Debug, PartialEq)]
enum Token {
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

#[derive(Debug)]
enum Ast {
    List(Vec<Ast>),
    Integer(i32),
    Symbol(String),
}

type Program = Vec<Ast>;

#[derive(Debug)]
enum Value {
    Integer(i32),
    Symbol(String),
    Nil,
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let result = read_lines(&args[1])
        .and_then(tokenize)
        .and_then(parse)
        .and_then(show_ast)
        .and_then(|ast| eval_program(&ast))
        .unwrap_or_else(|err| {
            println!("{:?}", err);
            vec![Value::Nil]
        });

    println!("{:?}", result);
}

fn read_lines<P>(filename: P) -> Result<Vec<String>, Error>
where
    P: AsRef<Path>,
{
    if let Ok(file) = File::open(filename) {
        let lines = io::BufReader::new(file)
            .lines()
            .filter_map(|line| line.ok())
            .collect::<Vec<String>>();
        Ok(lines)
    } else {
        Err(Error::Io("Cannot open soure file".to_string()))
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

fn tokenize(lines: Vec<String>) -> Result<Vec<Token>, Error> {
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
            c if c.is_alphabetic() => {
                let buf = take_while(&program, &mut i, |c| c.is_alphabetic());
                let value = buf.join("");
                result.push(Token::Identifier(value));
            }
            _ => {
                i += 1;
            }
        }
    }

    Ok(result)
}

type ParseResult<'a, T> = Result<(T, &'a [Token]), Error>;

fn consume<'a>(tokens: &'a [Token], expected: &Token) -> Result<&'a [Token], Error> {
    if let Some((first, rest)) = tokens.split_first() {
        if first == expected {
            Ok(rest)
        } else {
            Err(Error::Parse(format!(
                "Expected {:?}, actual {:?}",
                expected, first
            )))
        }
    } else {
        Err(Error::Parse(format!("Expected {:?}, actual EOF", expected)))
    }
}

fn consume_while(
    tokens: &[Token],
    pred: fn(&Token) -> bool,
    consumer: fn(&[Token]) -> ParseResult<Ast>,
) -> Result<(&[Token], Vec<Ast>), Error> {
    if let Some((first, _)) = tokens.split_first() {
        if pred(first) {
            let (first, rest) = consumer(tokens)?;

            consume_while(rest, pred, consumer).and_then(|(rest, mut asts)| {
                let mut result = vec![first];
                result.append(&mut asts);
                Ok((rest, result))
            })
        } else {
            Ok((tokens, Vec::new()))
        }
    } else {
        Ok((tokens, Vec::new()))
    }
}

fn parse_list(tokens: &[Token]) -> ParseResult<Ast> {
    let tokens = consume(tokens, &Token::LeftParen)?;
    let (tokens, items) = consume_while(tokens, |token| token != &Token::RightParen, parse_value)?;
    let tokens = consume(tokens, &&Token::RightParen)?;
    Ok((Ast::List(items), tokens))
}

fn parse_value(tokens: &[Token]) -> ParseResult<Ast> {
    if let Some((first, rest)) = tokens.split_first() {
        match first {
            Token::Identifier(value) => Ok((Ast::Symbol(value.clone()), rest)),
            Token::IntegerLiteral(value) => Ok((Ast::Integer(*value), rest)),
            Token::LeftParen => parse_list(tokens),
            _ => Err(Error::Parse(format!("Unexpeced {:?}", &tokens[0]))),
        }
    } else {
        Err(Error::Parse("EOF".to_string()))
    }
}

fn parse_program(tokens: &[Token]) -> ParseResult<Program> {
    if tokens.is_empty() {
        Ok((Vec::new(), tokens))
    } else {
        let (value, rest) = parse_value(tokens)?;
        let mut result = vec![value];
        let (mut values, rest) = parse_program(rest)?;
        result.append(&mut values);
        Ok((result, rest))
    }
}

fn parse(tokens: Vec<Token>) -> Result<Program, Error> {
    parse_program(&tokens[..])
        .and_then(|(ast, tokens)| {
            if !tokens.is_empty() {
                Err(Error::Parse(format!("Unexpeced {:?}", &tokens[0])))
            } else {
                Ok((ast, tokens))
            }
        })
        .map(|(ast, _)| ast)
}

fn eval_ast(ast: &Ast) -> Result<Value, Error> {
    match ast {
        Ast::List(elements) => {
            if let Some((first, rest)) = elements.split_first() {
                let first = eval_ast(first)?;
                match first {
                    Value::Symbol(func_name) => {
                        let func_name = func_name.as_str();
                        let args = rest
                            .iter()
                            .map(|arg| eval_ast(arg))
                            .collect::<Result<Vec<Value>, Error>>()?;
                        match func_name {
                            "sum" => {
                                let args = args
                                    .iter()
                                    .map(|arg| {
                                        if let Value::Integer(v) = arg {
                                            Ok(*v)
                                        } else {
                                            Err(Error::Eval(format!(
                                                "{:?} is not an integer.",
                                                arg
                                            )))
                                        }
                                    })
                                    .collect::<Result<Vec<i32>, Error>>()?;

                                let sum = args.iter().sum();
                                Ok(Value::Integer(sum))
                            }
                            "print" => {
                                for arg in args {
                                    println!("{:?}", arg);
                                }
                                Ok(Value::Nil)
                            }
                            _ => Err(Error::Eval(format!("Unknown function: {}", func_name))),
                        }
                    }
                    _ => Err(Error::Eval(format!("{:?} is not function", first))),
                }
            } else {
                Ok(Value::Nil)
            }
        }
        Ast::Integer(value) => Ok(Value::Integer(*value)),
        Ast::Symbol(value) => Ok(Value::Symbol(value.clone())),
    }
}

fn eval_program(asts: &Program) -> Result<Vec<Value>, Error> {
    asts.iter()
        .map(eval_ast)
        .collect::<Result<Vec<Value>, Error>>()
}

fn show_ast(ast: Program) -> Result<Program, Error> {
    println!("{:?}", ast);
    Ok(ast)
}

fn show_tokens(tokens: Vec<Token>) -> Result<(), Error> {
    for token in tokens {
        println!("{:?}", token);
    }
    Ok(())
}
