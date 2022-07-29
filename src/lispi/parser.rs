use super::{error::*, tokenizer::*};

#[derive(Clone, PartialEq, Debug)]
pub enum Ast {
    List(Vec<Ast>),
    Quoted(Box<Ast>),
    Integer(i32),
    Symbol(String),
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
            Token::Quote => {
                let (value, rest) = parse_value(rest)?;
                Ok((Ast::Quoted(Box::new(value)), rest))
            }
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
