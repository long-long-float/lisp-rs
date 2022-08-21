use super::{error::*, evaluator::Value, tokenizer::*};

#[derive(Clone, PartialEq, Debug)]
pub enum Ast {
    List(Vec<Ast>),
    Quoted(Box<Ast>),
    Integer(i32),
    Float(f32),
    Symbol(String),
    Boolean(bool),
    Char(char),
    Nil,

    // For optimizing tail recursion
    Continue(String),
}

// For evaluating macros
impl From<Value> for Ast {
    fn from(value: Value) -> Self {
        match value {
            Value::Integer(v) => Ast::Integer(v),
            Value::Float(v) => Ast::Float(v),
            Value::Symbol(v) => Ast::Symbol(v),
            Value::Boolean(v) => Ast::Boolean(v),
            Value::Char(v) => Ast::Char(v),
            Value::List(vs) => {
                if vs.len() == 0 {
                    Ast::Nil
                } else {
                    let vs = vs.into_iter().map(|v| v.value.into()).collect();
                    Ast::List(vs)
                }
            }
            Value::Function {
                name,
                args,
                body,
                is_macro: _,
            } => {
                if name == "" {
                    // Function created by lambda
                    let mut elem = vec![
                        Ast::Symbol("lambda".to_string()),
                        Ast::List(args.into_iter().map(|a| Ast::Symbol(a)).collect()),
                    ];
                    elem.append(&mut body.into_iter().map(|v| v.into()).collect());
                    Ast::List(elem)
                } else {
                    // Named function should be referenced
                    Ast::Symbol(name)
                }
            }
            Value::NativeFunction { name, func: _ } => Ast::Symbol(name),
            Value::RawAst(ast) => ast,
            Value::Continue(v) => Ast::Continue(v),
        }
    }
}

impl From<&str> for Ast {
    fn from(value: &str) -> Self {
        Ast::Symbol(value.to_string())
    }
}

pub type Program = Vec<Ast>;

pub type ParseResult<'a, T> = Result<(T, &'a [Token]), Error>;

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

fn consume_while<F>(
    tokens: &[Token],
    pred: F,
    consumer: fn(&[Token]) -> ParseResult<Ast>,
) -> Result<(&[Token], Vec<Ast>), Error>
where
    F: Fn(&Token) -> bool,
{
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
    let (left_token, right_token) = if let Some(&Token::LeftSquareBracket) = tokens.first() {
        (&Token::LeftSquareBracket, &Token::RightSquareBracket)
    } else {
        (&Token::LeftParen, &Token::RightParen)
    };
    let tokens = consume(tokens, left_token)?;
    let (tokens, items) = consume_while(tokens, |token| token != right_token, parse_value)?;
    let tokens = consume(tokens, &right_token)?;
    Ok((Ast::List(items), tokens))
}

fn parse_value(tokens: &[Token]) -> ParseResult<Ast> {
    if let Some((first, rest)) = tokens.split_first() {
        match first {
            Token::Identifier(value) => {
                let ret = if value.to_lowercase() == "nil" {
                    Ast::Nil
                } else {
                    Ast::Symbol(value.clone())
                };
                Ok((ret, rest))
            }
            Token::IntegerLiteral(value) => Ok((Ast::Integer(*value), rest)),
            Token::FloatLiteral(value) => Ok((Ast::Float(*value), rest)),
            Token::LeftParen | Token::LeftSquareBracket => parse_list(tokens),
            Token::Quote => {
                let (value, rest) = parse_value(rest)?;
                Ok((Ast::Quoted(Box::new(value)), rest))
            }
            Token::BooleanLiteral(value) => Ok((Ast::Boolean(*value), rest)),
            Token::CharLiteral(value) => Ok((Ast::Char(*value), rest)),
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

pub fn parse(tokens: Vec<Token>) -> Result<Program, Error> {
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

pub fn show_ast(ast: Program) -> Result<Program, Error> {
    println!("{:#?}", ast);
    Ok(ast)
}
