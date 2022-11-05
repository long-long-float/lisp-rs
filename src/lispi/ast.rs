use anyhow::{anyhow, Result};
use std::fmt::Display;

use crate::{ast_pat, match_special_args, match_special_args_with_rest};

use super::{
    error::Error, evaluator as e, evaluator::Value, typer::Type, LocationRange, SymbolValue,
    TokenLocation,
};

#[derive(Clone, PartialEq, Debug)]
pub enum Ast {
    List(Vec<AnnotatedAst>),
    Quoted(Box<AnnotatedAst>),
    Integer(i32),
    Float(f32),
    Symbol(SymbolValue),
    SymbolWithType(SymbolValue, SymbolValue),
    Boolean(bool),
    Char(char),
    String(String),
    Nil,

    // Special forms
    DefineMacro(DefineMacro),
    Define(Define),
    Lambda(Lambda),
    Assign(Assign),
    IfExpr(IfExpr),
    Cond(Cond),
    Let(Let),
    Begin(Begin),
    BuildList(Vec<AnnotatedAst>),

    /// For optimizing tail recursion
    Continue(String),
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
                    let args = e::get_symbol_values(args)?;
                    Ok(Ast::Lambda(Lambda {
                        args,
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

impl Ast {
    pub fn from_value(value: Value) -> Result<Self> {
        match value {
            Value::Integer(v) => Ok(Ast::Integer(v)),
            Value::Float(v) => Ok(Ast::Float(v)),
            Value::Symbol(v) => Ok(Ast::Symbol(v)),
            Value::Boolean(v) => Ok(Ast::Boolean(v)),
            Value::Char(v) => Ok(Ast::Char(v)),
            Value::String(v) => Ok(Ast::String(v)),
            Value::List(vs) => {
                let vs = vs
                    .into_iter()
                    .map(|v| Ok(Ast::from_value(v)?.with_null_location()))
                    .collect::<Result<Vec<_>>>()?;

                parse_special_form(&vs, TokenLocation::Null)
            }
            Value::Function {
                name, args, body, ..
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
                    Ok(Ast::List(elem))
                } else {
                    // Named function should be referenced
                    Ok(Ast::Symbol(name))
                }
            }
            Value::NativeFunction { name, func: _ } => Ok(Ast::Symbol(name)),
            Value::RawAst(ast) => Ok(ast.ast),
            Value::Continue(v) => Ok(Ast::Continue(v)),
        }
    }

    pub fn with_location(self, location: LocationRange) -> AnnotatedAst {
        AnnotatedAst::new(self, TokenLocation::Range(location))
    }

    pub fn with_token_location(self, location: TokenLocation) -> AnnotatedAst {
        AnnotatedAst::new(self, location)
    }

    pub fn with_null_location(self) -> AnnotatedAst {
        AnnotatedAst::new(self, TokenLocation::Null)
    }

    pub fn get_symbol_value(&self) -> Option<&SymbolValue> {
        match self {
            Ast::Symbol(sym) => Some(sym),
            Ast::SymbolWithType(sym, _) => Some(sym),
            _ => None,
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

#[derive(Clone, PartialEq, Debug)]
pub struct DefineMacro {
    pub id: SymbolValue,
    /// Arguments of macro don't have types.
    pub args: Vec<SymbolValue>,
    pub body: Vec<AnnotatedAst>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Define {
    pub id: SymbolValue,
    pub init: Box<AnnotatedAst>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Lambda {
    pub args: Vec<SymbolValue>,
    pub body: Vec<AnnotatedAst>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Assign {
    pub var: SymbolValue,
    pub var_loc: TokenLocation,
    pub value: Box<AnnotatedAst>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct IfExpr {
    pub cond: Box<AnnotatedAst>,
    pub then_ast: Box<AnnotatedAst>,
    pub else_ast: Option<Box<AnnotatedAst>>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Cond {
    pub clauses: Vec<CondClause>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct CondClause {
    pub cond: Box<AnnotatedAst>,
    pub body: Vec<AnnotatedAst>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Let {
    pub sequential: bool,
    pub proc_id: Option<SymbolValue>,
    pub inits: Vec<(SymbolValue, AnnotatedAst)>,
    pub body: Vec<AnnotatedAst>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Begin {
    pub body: Vec<AnnotatedAst>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct AnnotatedAst {
    pub ast: Ast,
    pub location: TokenLocation,
    pub ty: Type,
}

impl AnnotatedAst {
    fn new(ast: Ast, location: TokenLocation) -> Self {
        Self {
            ast,
            location,
            ty: Type::None,
        }
    }

    pub fn with_new_ast(self, new_ast: Ast) -> Self {
        Self {
            ast: new_ast,
            ..self
        }
    }

    pub fn with_new_type(self, new_ty: Type) -> Self {
        Self { ty: new_ty, ..self }
    }

    pub fn with_new_ast_and_type(self, new_ast: Ast, new_ty: Type) -> Self {
        Self {
            ast: new_ast,
            ty: new_ty,
            ..self
        }
    }
}

fn write_values<T: Display>(f: &mut std::fmt::Formatter<'_>, vs: &[T]) -> std::fmt::Result {
    if let Some((last, vs)) = vs.split_last() {
        for v in vs {
            write!(f, "{} ", v)?;
        }
        write!(f, "{}", last)?;
    }

    Ok(())
}

impl Display for AnnotatedAst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.ast {
            Ast::List(vs) => {
                write!(f, "(")?;
                write_values(f, vs)?;
                write!(f, ")")?;
                Ok(())
            }
            Ast::Quoted(v) => write!(f, "'{}", v),
            Ast::Integer(v) => write!(f, "{}", v),
            Ast::Float(v) => write!(f, "{}", v),
            Ast::Symbol(v) => write!(f, "{}", v.value),
            Ast::SymbolWithType(v, t) => write!(f, "{}:{}", v.value, t.value),
            Ast::Boolean(v) => {
                if *v {
                    write!(f, "#t")
                } else {
                    write!(f, "#f")
                }
            }
            Ast::Char(v) => write!(f, "'{}'", v),
            Ast::String(v) => write!(f, "\"{}\"", v),
            Ast::Nil => write!(f, "()"),
            Ast::DefineMacro(DefineMacro { id, args, body }) => {
                write!(f, "(define-macro {} (", id.value)?;
                write_values(f, &args.iter().map(|arg| &arg.value).collect::<Vec<_>>())?;
                write!(f, ") ")?;
                write_values(f, body)?;
                write!(f, ")")
            }
            Ast::Define(Define { id, init }) => {
                write!(f, "(define {} {})", id.value, *init)
            }
            Ast::Lambda(Lambda { args, body }) => {
                write!(f, "(lambda (")?;
                write_values(f, &args.iter().map(|arg| &arg.value).collect::<Vec<_>>())?;
                write!(f, ") ")?;
                write_values(f, body)?;
                write!(f, ")")
            }
            Ast::Assign(Assign {
                var,
                var_loc: _,
                value,
            }) => {
                write!(f, "(set! {} {})", var.value, value)
            }
            Ast::IfExpr(IfExpr {
                cond,
                then_ast,
                else_ast,
            }) => {
                write!(f, "(if {} {}", cond, then_ast)?;
                if let Some(else_ast) = else_ast {
                    write!(f, " {}", else_ast)?;
                }
                write!(f, ")")
            }
            Ast::Cond(Cond { clauses }) => {
                writeln!(f, "(cond ")?;
                for CondClause { cond, body } in clauses {
                    write!(f, "  ({} ", cond)?;
                    write_values(f, body)?;
                    write!(f, ")")?;
                }
                write!(f, ")")
            }
            Ast::Let(Let {
                inits,
                body,
                sequential,
                proc_id,
            }) => {
                let star = if *sequential { "*" } else { "" };
                write!(f, "(let{} ", star)?;
                if let Some(proc_id) = proc_id {
                    write!(f, "{} ", proc_id.value)?;
                }
                write!(f, "(")?;
                let inits = inits
                    .iter()
                    .map(|(k, v)| format!("[{} {}]", k.value, v))
                    .collect::<Vec<_>>();
                write_values(f, &inits)?;
                write!(f, ") ")?;

                write_values(f, body)?;
                write!(f, ")")
            }
            Ast::Begin(Begin { body }) => {
                write!(f, "(begin ")?;
                write_values(f, body)?;
                write!(f, ")")
            }
            Ast::BuildList(values) => {
                write!(f, "(begin ")?;
                write_values(f, values)?;
                write!(f, ")")
            }
            Ast::Continue(_) => write!(f, "CONTINUE"),
        }?;

        if self.ty != Type::None {
            // write!(f, ": {}", self.ty)
            Ok(())
        } else {
            Ok(())
        }
    }
}
