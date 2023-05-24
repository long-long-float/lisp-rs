use anyhow::{anyhow, Result};

use crate::{ast_pat, match_special_args, match_special_args_with_rest};

use super::{
    ast::*, error::*, evaluator as e, tokenizer::*, LocationRange, SymbolValue, TokenLocation,
};

pub type Program = Vec<AnnotatedAst>;

pub type ParseResult<'a, T> = Result<(T, &'a [TokenWithLocation])>;

/// Get a expected token or return a parse error.
fn consume<'a>(
    tokens: &'a [TokenWithLocation],
    expected: &Token,
) -> ParseResult<'a, LocationRange> {
    if let Some((first, rest)) = tokens.split_first() {
        if &first.token == expected {
            Ok((first.location, rest))
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

            consume_while(rest, pred, consumer).map(|(mut asts, rest)| {
                let mut result = vec![first];
                result.append(&mut asts);
                (result, rest)
            })
        } else {
            Ok((Vec::new(), tokens))
        }
    } else {
        Ok((Vec::new(), tokens))
    }
}

pub fn parse_special_form(asts: &[AnnotatedAst], location: TokenLocation) -> Result<Ast> {
    if let Some((
        AnnotatedAst {
            ast: Ast::Symbol(name),
            ..
        },
        args,
    )) = asts.split_first()
    {
        let name = name.as_str();
        match name {
            "define-macro" => {
                match_special_args_with_rest!(
                    args,
                    body,
                    ast_pat!(Ast::Symbol(fun_name), _loc1),
                    ast_pat!(Ast::List(args)),
                    {
                        let args = e::get_symbol_values(args)?;
                        Ok(Ast::DefineMacro(DefineMacro {
                            id: fun_name.clone(),
                            args,
                            body: body.to_vec(),
                        }))
                    }
                )
            }
            "define" => {
                match_special_args!(args, ast_pat!(Ast::Symbol(id), _loc), init, {
                    Ok(Ast::Define(Define {
                        id: id.clone(),
                        init: Box::new(init.clone()),
                    }))
                })
            }
            "lambda" => {
                match_special_args_with_rest!(args, body, ast_pat!(Ast::List(args), _loc), {
                    let args = args
                        .iter()
                        .map(|arg| match arg.ast.clone() {
                            Ast::SymbolWithType(id, ty) => Ok((id, Some(ty))),
                            Ast::Symbol(id) => Ok((id, None)),
                            _ => Err(Error::Eval(format!("{:?} is not an symbol", arg.ast))
                                .with_location(arg.location)
                                .into()),
                        })
                        .collect::<Result<Vec<_>>>()?;
                    let (args, arg_types) = args.into_iter().unzip();
                    Ok(Ast::Lambda(Lambda {
                        args,
                        arg_types,
                        body: body.to_vec(),
                    }))
                })
            }
            "set!" => {
                match_special_args!(args, ast_pat!(Ast::Symbol(name), loc), value, {
                    Ok(Ast::Assign(Assign {
                        var: name.clone(),
                        var_loc: *loc,
                        value: Box::new(value.clone()),
                    }))
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
                    Ok(Ast::IfExpr(if_expr))
                } else {
                    Err(
                        Error::Parse("'if' is formed as (if cond then else)".to_string())
                            .with_location(location)
                            .into(),
                    )
                }
            }
            "let" | "let*" => {
                let err = Error::Eval(
                    "'let' is formed as (let ([id expr] ...) body ...) or named let (let proc-id ([id expr] ...) body ...)".to_string(),
                ).with_location(location);

                let sequential = name == "let*";

                let parse_inits =
                    |inits: &[AnnotatedAst]| -> Result<Vec<(SymbolValue, AnnotatedAst)>> {
                        inits
                            .iter()
                            .map(|init| {
                                if let ast_pat!(Ast::List(init)) = init {
                                    match_special_args!(init, ast_pat!(Ast::Symbol(id)), expr, {
                                        Ok((id.clone(), expr.clone()))
                                    })
                                } else {
                                    Err(err.clone().into())
                                }
                            })
                            .collect::<Result<Vec<_>>>()
                    };

                let let_expr =
                    if let Some((ast_pat!(Ast::List(inits), _loc), body)) = args.split_first() {
                        let inits = parse_inits(inits)?;

                        Let {
                            sequential,
                            proc_id: None,
                            inits,
                            body: body.to_vec(),
                        }
                    } else if let (
                        Some(ast_pat!(Ast::Symbol(proc_id))),
                        Some(ast_pat!(Ast::List(inits))),
                        (_, body),
                    ) = (args.get(0), args.get(1), args.split_at(2))
                    {
                        // named let

                        let inits = parse_inits(inits)?;

                        Let {
                            sequential,
                            proc_id: Some(proc_id.clone()),
                            inits,
                            body: body.to_vec(),
                        }
                    } else {
                        return Err(err.into());
                    };

                Ok(Ast::Let(let_expr))
            }
            "begin" => Ok(Ast::Begin(Begin {
                body: args.to_vec(),
            })),
            "list" => Ok(Ast::BuildList(args.to_vec())),
            "cond" => {
                let err = Error::Eval("'cond' is formed as (cond (cond body ...) ...)".to_string())
                    .with_location(location);

                let clauses = args
                    .iter()
                    .map(|clause| {
                        if let ast_pat!(Ast::List(arm)) = clause {
                            if let Some((cond, body)) = arm.split_first() {
                                Ok(CondClause {
                                    cond: Box::new(cond.clone()),
                                    body: body.to_vec(),
                                })
                            } else {
                                Err(err.clone().into())
                            }
                        } else {
                            Err(err.clone().into())
                        }
                    })
                    .collect::<Result<Vec<_>>>()?;

                Ok(Ast::Cond(Cond { clauses }))
            }
            _ => Ok(Ast::List(asts.to_vec())),
        }
    } else {
        Ok(Ast::List(asts.to_vec()))
    }
}

fn parse_list(tokens: &[TokenWithLocation]) -> ParseResult<AnnotatedAst> {
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
    let (items, tokens) = consume_while(tokens, |token| token != right_token, parse_value)?;
    let (tail_loc, tokens) = consume(tokens, right_token)?;

    let location = LocationRange::new(head_loc.begin, tail_loc.end);

    Ok((
        parse_special_form(&items, TokenLocation::Range(location))?.with_location(location),
        tokens,
    ))
}

fn parse_value(tokens: &[TokenWithLocation]) -> ParseResult<AnnotatedAst> {
    if let Some((
        TokenWithLocation {
            token: first,
            location: loc,
        },
        rest,
    )) = tokens.split_first()
    {
        let loc = *loc;
        match first {
            Token::Identifier(value) => {
                if value.to_lowercase() == "nil" {
                    Ok((Ast::Nil.with_location(loc), rest))
                } else {
                    let sym = value.clone();
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

                            Ok((
                                Ast::SymbolWithType(sym, ty.clone())
                                    .with_location(loc.merge(tyloc)),
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
            Token::LeftParen | Token::LeftSquareBracket => parse_list(tokens),
            Token::Quote => {
                let (value, rest) = parse_value(rest)?;
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

fn parse_program(tokens: &[TokenWithLocation]) -> ParseResult<Program> {
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

/// Get AST from tokens.
/// This uses recursive descent parsing and is simple implementation thanks to the syntax of LISP.
pub fn parse(tokens: Vec<TokenWithLocation>) -> Result<Program> {
    let ast = parse_with_env(tokens)?;
    Ok(ast)
}

pub fn parse_with_env(tokens: Vec<TokenWithLocation>) -> Result<Program> {
    parse_program(&tokens).and_then(|(ast, tokens)| {
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
