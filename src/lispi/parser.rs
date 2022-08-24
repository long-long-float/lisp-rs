use std::{collections::HashMap, hash::Hash};

use super::{error::*, evaluator::Value, tokenizer::*, SymbolValue};

#[derive(Clone, PartialEq, Debug)]
pub enum Ast {
    List(Vec<Ast>),
    Quoted(Box<Ast>),
    Integer(i32),
    Float(f32),
    Symbol(SymbolValue),
    Boolean(bool),
    Char(char),
    Nil,

    // For optimizing tail recursion
    Continue(String),
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
                if name.value == "" {
                    // Function created by lambda
                    let mut elem = vec![
                        Ast::Symbol(SymbolValue {
                            value: "lambda".to_string(),
                            id: 0,
                        }),
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
        Ast::Symbol(SymbolValue {
            value: value.to_string(),
            id: 0,
        })
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

fn consume_while<F, C>(
    tokens: &[Token],
    pred: F,
    mut consumer: C,
) -> Result<(&[Token], Vec<Ast>), Error>
where
    F: Fn(&Token) -> bool,
    C: FnMut(&[Token]) -> ParseResult<Ast>,
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

fn parse_list<'a>(tokens: &'a [Token], env: &mut Environment) -> ParseResult<'a, Ast> {
    let (left_token, right_token) = if let Some(&Token::LeftSquareBracket) = tokens.first() {
        (&Token::LeftSquareBracket, &Token::RightSquareBracket)
    } else {
        (&Token::LeftParen, &Token::RightParen)
    };
    let tokens = consume(tokens, left_token)?;
    let (tokens, items) = consume_while(
        tokens,
        |token| token != right_token,
        |t| parse_value(t, env),
    )?;
    let tokens = consume(tokens, &right_token)?;
    Ok((Ast::List(items), tokens))
}

fn parse_value<'a>(tokens: &'a [Token], env: &mut Environment) -> ParseResult<'a, Ast> {
    if let Some((first, rest)) = tokens.split_first() {
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
                Ok((ret, rest))
            }
            Token::IntegerLiteral(value) => Ok((Ast::Integer(*value), rest)),
            Token::FloatLiteral(value) => Ok((Ast::Float(*value), rest)),
            Token::LeftParen | Token::LeftSquareBracket => parse_list(tokens, env),
            Token::Quote => {
                let (value, rest) = parse_value(rest, env)?;
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

fn parse_program<'a>(tokens: &'a [Token], env: &mut Environment) -> ParseResult<'a, Program> {
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

pub fn parse(tokens: Vec<Token>) -> Result<(Program, Environment), Error> {
    let mut env = Environment::new();

    parse_program(&tokens, &mut env).and_then(|(ast, tokens)| {
        if !tokens.is_empty() {
            Err(Error::Parse(format!("Unexpeced {:?}", &tokens[0])))
        } else {
            Ok((ast, env))
        }
    })
}

pub fn show_ast(ast: Program) -> Result<Program, Error> {
    println!("{:#?}", ast);
    Ok(ast)
}
