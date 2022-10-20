use anyhow::{anyhow, Result};
use std::collections::HashMap;

use crate::{ast_pat, match_special_args, match_special_args_with_rest};

use super::{
    ast::*, error::*, evaluator as e, tokenizer::*, LocationRange, SymbolValue, TokenLocation,
};

#[derive(Clone, PartialEq, Debug)]
/// Maps symbols such as 'x' to unique integer.
/// It contributes reduction of searching HashMap a little to use an integer instead of a string to manage variables.
pub struct SymbolTable {
    table: HashMap<String, u32>,
}

impl SymbolTable {
    pub fn new() -> SymbolTable {
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

pub type Program = Vec<AnnotatedAst>;

pub type ParseResult<'a, T> = Result<(T, &'a [TokenWithLocation])>;

/// Get a expected token or return a parse error.
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

/// Get tokens using consumer while pred returns true.
fn consume_while<F, C>(
    tokens: &[TokenWithLocation],
    pred: F,
    mut consumer: C,
) -> ParseResult<Vec<AnnotatedAst>>
where
    F: Fn(&Token) -> bool,
    C: FnMut(&[TokenWithLocation]) -> ParseResult<AnnotatedAst>,
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
    sym_table: &mut SymbolTable,
) -> ParseResult<'a, AnnotatedAst> {
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
        |t| parse_value(t, sym_table),
    )?;
    let (tail_loc, tokens) = consume(tokens, &right_token)?;

    let location = LocationRange::new(head_loc.begin, tail_loc.end);

    if let Some((
        AnnotatedAst {
            ast: Ast::Symbol(name),
            ..
        },
        args,
    )) = items.split_first()
    {
        let name = name.value.as_str();
        match name {
            "define-macro" => {
                match_special_args_with_rest!(
                    args,
                    body,
                    ast_pat!(Ast::Symbol(fun_name), _loc1),
                    ast_pat!(Ast::List(args)),
                    {
                        let args = e::get_symbol_values(args)?;
                        Ok((
                            Ast::DefineMacro(DefineMacro {
                                id: fun_name.clone(),
                                args,
                                body: body.to_vec(),
                            })
                            .with_location(location),
                            tokens,
                        ))
                    }
                )
            }
            "define" => {
                match_special_args!(args, ast_pat!(Ast::Symbol(id), _loc), init, {
                    Ok((
                        Ast::Define(Define {
                            id: id.clone(),
                            init: Box::new(init.clone()),
                        })
                        .with_location(location),
                        tokens,
                    ))
                })
            }
            "lambda" => {
                match_special_args_with_rest!(args, body, ast_pat!(Ast::List(args), _loc), {
                    let args = e::get_symbol_values(args)?;
                    Ok((
                        Ast::Lambda(Lambda {
                            args,
                            body: body.to_vec(),
                        })
                        .with_location(location),
                        tokens,
                    ))
                })
            }
            "set!" => {
                match_special_args!(args, ast_pat!(Ast::Symbol(name), loc), value, {
                    Ok((
                        Ast::Assign(Assign {
                            var: name.clone(),
                            var_loc: *loc,
                            value: Box::new(value.clone()),
                        })
                        .with_location(location),
                        tokens,
                    ))
                })
            }
            "if" => {
                if let (Some(cond), Some(then_ast)) = (args.get(0), args.get(1)) {
                    let if_expr = if let Some(else_ast) = args.get(2) {
                        IfExpr {
                            cond: Box::new(cond.clone()),
                            then_ast: Box::new(then_ast.clone()),
                            else_ast: Some(Box::new(else_ast.clone())),
                        }
                    } else {
                        IfExpr {
                            cond: Box::new(cond.clone()),
                            then_ast: Box::new(then_ast.clone()),
                            else_ast: None,
                        }
                    };
                    Ok((Ast::IfExpr(if_expr).with_location(location), tokens))
                } else {
                    Err(
                        Error::Parse("'if' is formed as (if cond then else)".to_string())
                            .with_location(TokenLocation::Range(location))
                            .into(),
                    )
                }
            }
            _ => Ok((Ast::List(items).with_location(location), tokens)),
        }
    } else {
        Ok((Ast::List(items).with_location(location), tokens))
    }
}

fn parse_value<'a>(
    tokens: &'a [TokenWithLocation],
    sym_table: &mut SymbolTable,
) -> ParseResult<'a, AnnotatedAst> {
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
                if value.to_lowercase() == "nil" {
                    Ok((Ast::Nil.with_location(loc), rest))
                } else {
                    let id = sym_table.find_id_or_insert(value);
                    let sym = SymbolValue {
                        value: value.clone(),
                        id,
                    };
                    if let Some((
                        TokenWithLocation {
                            token: Token::Colon,
                            ..
                        },
                        rest,
                    )) = rest.split_first()
                    {
                        if let Some((
                            TokenWithLocation {
                                token: Token::Identifier(ty),
                                location: tyloc,
                            },
                            rest,
                        )) = rest.split_first()
                        {
                            // TODO: Restrict type annotation in specific location

                            let id = sym_table.find_id_or_insert(ty);
                            let ty = SymbolValue {
                                value: ty.clone(),
                                id,
                            };
                            Ok((
                                Ast::SymbolWithType(sym, ty).with_location(loc.merge(tyloc)),
                                rest,
                            ))
                        } else {
                            Ok((Ast::Symbol(sym).with_location(loc), rest))
                        }
                    } else {
                        Ok((Ast::Symbol(sym).with_location(loc), rest))
                    }
                }
            }
            Token::IntegerLiteral(value) => Ok((Ast::Integer(*value).with_location(loc), rest)),
            Token::FloatLiteral(value) => Ok((Ast::Float(*value).with_location(loc), rest)),
            Token::LeftParen | Token::LeftSquareBracket => parse_list(tokens, sym_table),
            Token::Quote => {
                let (value, rest) = parse_value(rest, sym_table)?;
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
    sym_table: &mut SymbolTable,
) -> ParseResult<'a, Program> {
    if tokens.is_empty() {
        Ok((Vec::new(), tokens))
    } else {
        let (value, rest) = parse_value(tokens, sym_table)?;
        let mut result = vec![value];
        let (mut values, rest) = parse_program(rest, sym_table)?;
        result.append(&mut values);
        Ok((result, rest))
    }
}

/// Get AST from tokens.
/// This uses recursive descent parsing and is simple implementation thanks to the syntax of LISP.
pub fn parse(tokens: Vec<TokenWithLocation>) -> Result<(Program, SymbolTable)> {
    let mut sym_table = SymbolTable::new();
    let ast = parse_with_env(tokens, &mut sym_table)?;
    Ok((ast, sym_table))
}

pub fn parse_with_env(
    tokens: Vec<TokenWithLocation>,
    sym_table: &mut SymbolTable,
) -> Result<Program> {
    parse_program(&tokens, sym_table).and_then(|(ast, tokens)| {
        if !tokens.is_empty() {
            let token = &tokens[0];
            Err(Error::Parse(format!("Unexpeced {:?}", token.token))
                .with_location(TokenLocation::Range(token.location))
                .into())
        } else {
            Ok(ast)
        }
    })
}

pub fn show_ast(ast: Program) -> Result<Program, Error> {
    println!("{:#?}", ast);
    Ok(ast)
}
