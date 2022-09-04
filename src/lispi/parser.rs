use anyhow::Result;
use std::collections::HashMap;

use super::{error::*, evaluator::Value, tokenizer::*, LocationRange, SymbolValue, TokenLocation};

#[derive(Clone, PartialEq, Debug)]
pub enum Ast {
    List(Vec<AstWithLocation>),
    Quoted(Box<AstWithLocation>),
    Integer(i32),
    Float(f32),
    Symbol(SymbolValue),
    Boolean(bool),
    Char(char),
    String(String),
    Nil,

    // For optimizing tail recursion
    Continue(String),
}

impl Ast {
    pub fn with_location(self, location: LocationRange) -> AstWithLocation {
        AstWithLocation {
            ast: self,
            location: TokenLocation::Range(location),
        }
    }

    pub fn with_null_location(self) -> AstWithLocation {
        AstWithLocation {
            ast: self,
            location: TokenLocation::Null,
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct AstWithLocation {
    pub ast: Ast,
    pub location: TokenLocation,
}

pub struct SymbolTable {
    table: HashMap<String, u32>,
}

impl SymbolTable {
    fn new() -> SymbolTable {
        let mut table = HashMap::new();
        // ID 0 means undefined
        table.insert("".to_string(), 0);
        SymbolTable { table }
    }

    pub fn find_id_or_insert(&mut self, value: &String) -> u32 {
        if let Some(id) = self.table.get(value) {
            *id
        } else {
            let id = self.table.len() as u32;
            self.table.insert(value.clone(), id);
            id
        }
    }
}

pub struct Environment {
    pub sym_table: SymbolTable,
}

impl Environment {
    fn new() -> Environment {
        Environment {
            sym_table: SymbolTable::new(),
        }
    }
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
            Value::String(v) => Ast::String(v),
            Value::List(vs) => {
                if vs.len() == 0 {
                    Ast::Nil
                } else {
                    let vs = vs
                        .into_iter()
                        .map(|v| Ast::from(v.value).with_null_location())
                        .collect();
                    Ast::List(vs)
                }
            }
            Value::Function {
                name,
                args,
                body,
                is_macro: _,
            } => {
                if name.value == "" {
                    // Function created by lambda
                    let mut elem = vec![
                        Ast::Symbol(SymbolValue {
                            value: "lambda".to_string(),
                            id: 0,
                        })
                        .with_null_location(),
                        Ast::List(
                            args.into_iter()
                                .map(|a| Ast::Symbol(a).with_null_location())
                                .collect(),
                        )
                        .with_null_location(),
                    ];
                    elem.append(
                        &mut body
                            .into_iter()
                            .map(|v| Ast::from(v.ast).with_null_location())
                            .collect(),
                    );
                    Ast::List(elem)
                } else {
                    // Named function should be referenced
                    Ast::Symbol(name)
                }
            }
            Value::NativeFunction { name, func: _ } => Ast::Symbol(name),
            Value::RawAst(ast) => ast.ast,
            Value::Continue(v) => Ast::Continue(v),
        }
    }
}

impl From<&str> for Ast {
    fn from(value: &str) -> Self {
        Ast::Symbol(SymbolValue {
            value: value.to_string(),
            id: 0,
        })
    }
}

pub type Program = Vec<AstWithLocation>;

pub type ParseResult<'a, T> = Result<(T, &'a [TokenWithLocation])>;

fn consume<'a>(
    tokens: &'a [TokenWithLocation],
    expected: &Token,
) -> ParseResult<'a, LocationRange> {
    if let Some((first, rest)) = tokens.split_first() {
        if &first.token == expected {
            Ok((first.location.clone(), rest))
        } else {
            Err(
                Error::Parse(format!("Expected {:?}, actual {:?}", expected, first.token))
                    .with_location(TokenLocation::Range(first.location))
                    .into(),
            )
        }
    } else {
        Err(Error::Parse(format!("Expected {:?}, actual EOF", expected))
            .with_location(TokenLocation::EOF)
            .into())
    }
}

fn consume_while<F, C>(
    tokens: &[TokenWithLocation],
    pred: F,
    mut consumer: C,
) -> ParseResult<Vec<AstWithLocation>>
where
    F: Fn(&Token) -> bool,
    C: FnMut(&[TokenWithLocation]) -> ParseResult<AstWithLocation>,
{
    if let Some((first, _)) = tokens.split_first() {
        if pred(&first.token) {
            let (first, rest) = consumer(tokens)?;

            consume_while(rest, pred, consumer).and_then(|(mut asts, rest)| {
                let mut result = vec![first];
                result.append(&mut asts);
                Ok((result, rest))
            })
        } else {
            Ok((Vec::new(), tokens))
        }
    } else {
        Ok((Vec::new(), tokens))
    }
}

fn parse_list<'a>(
    tokens: &'a [TokenWithLocation],
    env: &mut Environment,
) -> ParseResult<'a, AstWithLocation> {
    let (left_token, right_token) = if let Some(&TokenWithLocation {
        token: Token::LeftSquareBracket,
        location: _,
    }) = tokens.first()
    {
        (&Token::LeftSquareBracket, &Token::RightSquareBracket)
    } else {
        (&Token::LeftParen, &Token::RightParen)
    };
    let (head_loc, tokens) = consume(tokens, left_token)?;
    let (items, tokens) = consume_while(
        tokens,
        |token| token != right_token,
        |t| parse_value(t, env),
    )?;
    let (tail_loc, tokens) = consume(tokens, &right_token)?;
    Ok((
        Ast::List(items).with_location(LocationRange::new(head_loc.begin, tail_loc.end)),
        tokens,
    ))
}

fn parse_value<'a>(
    tokens: &'a [TokenWithLocation],
    env: &mut Environment,
) -> ParseResult<'a, AstWithLocation> {
    if let Some((
        TokenWithLocation {
            token: first,
            location: loc,
        },
        rest,
    )) = tokens.split_first()
    {
        let loc = loc.clone();
        match first {
            Token::Identifier(value) => {
                let ret = if value.to_lowercase() == "nil" {
                    Ast::Nil
                } else {
                    let id = env.sym_table.find_id_or_insert(value);
                    Ast::Symbol(SymbolValue {
                        value: value.clone(),
                        id: id,
                    })
                };
                Ok((ret.with_location(loc), rest))
            }
            Token::IntegerLiteral(value) => Ok((Ast::Integer(*value).with_location(loc), rest)),
            Token::FloatLiteral(value) => Ok((Ast::Float(*value).with_location(loc), rest)),
            Token::LeftParen | Token::LeftSquareBracket => parse_list(tokens, env),
            Token::Quote => {
                let (value, rest) = parse_value(rest, env)?;
                Ok((Ast::Quoted(Box::new(value)).with_location(loc), rest))
            }
            Token::BooleanLiteral(value) => Ok((Ast::Boolean(*value).with_location(loc), rest)),
            Token::CharLiteral(value) => Ok((Ast::Char(*value).with_location(loc), rest)),
            Token::StringLiteral(value) => {
                Ok((Ast::String(value.clone()).with_location(loc), rest))
            }
            _ => Err(Error::Parse(format!("Unexpeced {:?}", &tokens[0].token))
                .with_location(TokenLocation::Range(loc))
                .into()),
        }
    } else {
        Err(Error::Parse("Unexpected EOF".to_string())
            .with_location(TokenLocation::Null)
            .into())
    }
}

fn parse_program<'a>(
    tokens: &'a [TokenWithLocation],
    env: &mut Environment,
) -> ParseResult<'a, Program> {
    if tokens.is_empty() {
        Ok((Vec::new(), tokens))
    } else {
        let (value, rest) = parse_value(tokens, env)?;
        let mut result = vec![value];
        let (mut values, rest) = parse_program(rest, env)?;
        result.append(&mut values);
        Ok((result, rest))
    }
}

pub fn parse(tokens: Vec<TokenWithLocation>) -> Result<(Program, Environment)> {
    let mut env = Environment::new();

    parse_program(&tokens, &mut env).and_then(|(ast, tokens)| {
        if !tokens.is_empty() {
            let token = &tokens[0];
            Err(Error::Parse(format!("Unexpeced {:?}", token.token))
                .with_location(TokenLocation::Range(token.location))
                .into())
        } else {
            Ok((ast, env))
        }
    })
}

pub fn show_ast(ast: Program) -> Result<Program, Error> {
    println!("{:#?}", ast);
    Ok(ast)
}
