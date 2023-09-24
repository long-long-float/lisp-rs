use anyhow::{anyhow, Result};
use itertools::Itertools;

use crate::{ast_pat, lispi::ty::Type, match_special_args, match_special_args_with_rest};

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
fn consume_while<F, C, R>(
    tokens: &[TokenWithLocation],
    pred: F,
    mut consumer: C,
) -> ParseResult<Vec<R>>
where
    F: Fn(&Token) -> bool,
    C: FnMut(&[TokenWithLocation]) -> ParseResult<R>,
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
            "as" => {
                match_special_args!(args, expr, ast_pat!(Ast::Symbol(ty), _loc), {
                    Ok(Ast::As(Box::new(expr.clone()), ty.clone()))
                })
            }
            "ref" => {
                match_special_args!(args, expr, { Ok(Ast::Ref(Box::new(expr.clone()))) })
            }
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
            "struct" => {
                match_special_args_with_rest!(args, fields, ast_pat!(Ast::Symbol(name), _loc), {
                    let fields = fields
                        .iter()
                        .map(|field| {
                            if let ast_pat!(Ast::SymbolWithType(name, ty)) = field {
                                Ok(StructField {
                                    name: name.to_owned(),
                                    ty: ty.to_owned(),
                                })
                            } else {
                                let err = Error::Parse(
                                    "'struct' is formed as (struct id id:type ...)".to_string(),
                                )
                                .with_location(location);
                                Err(err.into())
                            }
                        })
                        .collect::<Result<Vec<_>>>()?;
                    Ok(Ast::DefineStruct(DefineStruct {
                        name: name.clone(),
                        fields,
                    }))
                })
            }
            // TODO: Restrict "include" to top-level only
            "include" => {
                match_special_args!(args, ast_pat!(Ast::String(path), _loc), {
                    Ok(Ast::Include(path.clone()))
                })
            }
            "define" => {
                match_special_args!(args, ast_pat!(Ast::Symbol(id), _loc), init, {
                    Ok(Ast::Define(Define {
                        id: id.clone(),
                        init: Box::new(init.clone()),
                    }))
                })
            }
            "fn" => {
                match_special_args_with_rest!(
                    args,
                    body,
                    ast_pat!(Ast::Symbol(id), _loc),
                    ast_pat!(Ast::List(args), _loc),
                    {
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
                        Ok(Ast::DefineFunction(DefineFunction {
                            id: id.clone(),
                            lambda: Lambda {
                                args,
                                arg_types,
                                body: body.to_vec(),
                            },
                            lambda_type: Type::None,
                        }))
                    }
                )
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
            "list" => Ok(Ast::ListLiteral(args.to_vec())),
            "array" => Ok(Ast::ArrayLiteral(args.to_vec(), false)),
            "fixed-array" => Ok(Ast::ArrayLiteral(args.to_vec(), true)),
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
    let (head_loc, tokens) = consume(tokens, &Token::LeftParen)?;
    let (items, tokens) = consume_while(tokens, |token| token != &Token::RightParen, parse_value)?;
    let (tail_loc, tokens) = consume(tokens, &Token::RightParen)?;

    let location = LocationRange::new(head_loc.begin, tail_loc.end);

    Ok((
        parse_special_form(&items, TokenLocation::Range(location))?.with_location(location),
        tokens,
    ))
}

fn parse_type<'a>(
    rest: &'a [TokenWithLocation],
    prev_loc: &LocationRange,
) -> ParseResult<'a, Type> {
    if let Some((
        TokenWithLocation {
            token,
            location: tyloc,
        },
        rest,
    )) = rest.split_first()
    {
        let (inner_types, rest) = if let Some((
            TokenWithLocation {
                token: Token::LeftSquareBracket,
                location: _,
            },
            rest,
        )) = rest.split_first()
        {
            let (inner_types, rest) = consume_while(
                rest,
                |token| token != &Token::RightSquareBracket,
                |t| parse_type(t, tyloc),
            )?;
            let (_, rest) = consume(rest, &Token::RightSquareBracket)?;

            let inner_types = inner_types.into_iter().map(|t| Box::new(t)).collect_vec();

            (inner_types, rest)
        } else {
            (Vec::new(), rest)
        };

        let ty = match token {
            Token::Identifier(ty) => match ty.as_str() {
                "int" => Type::Int,
                "float" => Type::Float,
                "bool" => Type::Boolean,
                "char" => Type::Char,
                "void" => Type::Void,
                "fixed-array" => {
                    let (Some(inner), Some(len)) = (inner_types.get(0), inner_types.get(1)) else {
                        return Err(
                            Error::Parse("fixed-array takes type and number".to_string()).into(),
                        );
                    };
                    let Type::ConstantInt(len) = *len.as_ref() else {
                        return Err(
                            Error::Parse("fixed-array takes type and number".to_string()).into(),
                        );
                    };

                    Type::FixedArray(inner.clone(), len as usize)
                }
                ty => Type::Composite {
                    name: ty.to_string(),
                    inner: inner_types,
                },
            },
            Token::IntegerLiteral(n) => Type::ConstantInt(*n),
            _ => {
                return Err(Error::Parse(format!("Unexpected {:?}", token))
                    .with_location(TokenLocation::Range(*tyloc))
                    .into());
            }
        };

        Ok((ty, rest))
    } else {
        let loc = if let Some(token) = rest.first() {
            &token.location
        } else {
            prev_loc
        };
        Err(Error::Parse("Expeced type".to_string())
            .with_location(TokenLocation::Range(loc.clone()))
            .into())
    }
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
                            location: colon_loc,
                        },
                        rest)) = rest.split_first()
                    {
                        // TODO: Restrict type annotation in specific location

                        let (ty, rest) = parse_type(rest, colon_loc)?;

                        Ok((
                            Ast::SymbolWithType(sym, ty).with_location(loc),
                            rest,
                        ))
                    } else {
                        Ok((Ast::Symbol(sym).with_location(loc), rest))
                    }
                }
            }
            Token::IntegerLiteral(value) => Ok((Ast::Integer(*value).with_location(loc), rest)),
            Token::FloatLiteral(value) => Ok((Ast::Float(*value).with_location(loc), rest)),
            Token::LeftParen /* | Token::LeftSquareBracket */ => parse_list(tokens),
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
