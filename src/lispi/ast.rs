use anyhow::{anyhow, Result};
use std::fmt::Display;

use super::{
    console::printlnuw, evaluator::Value, parser::parse_special_form, typer::Type, LocationRange,
    SymbolValue, TokenLocation,
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
    Loop(Loop),
    Continue(String),
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
                if name.value.is_empty() {
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
                            .map(|v| v.ast.with_null_location())
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
    pub arg_types: Vec<Option<SymbolValue>>,
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
pub struct Loop {
    pub inits: Vec<(SymbolValue, AnnotatedAst)>,
    pub label: String,
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

    pub fn traverse<F, A>(self, ctx: &mut A, func: F) -> Result<Self>
    where
        F: Fn(Self, &mut A) -> Result<Self>,
    {
        let AnnotatedAst { ast, location, ty } = self;
        let ast = match ast {
            Ast::Integer(_)
            | Ast::Float(_)
            | Ast::Symbol(_)
            | Ast::SymbolWithType(_, _)
            | Ast::Boolean(_)
            | Ast::Char(_)
            | Ast::String(_)
            | Ast::Nil
            | Ast::Continue(_) => ast,
            Ast::List(vs) => {
                let vs = vs
                    .iter()
                    .map(|v| func(v.clone(), ctx))
                    .collect::<Result<Vec<_>>>()?;
                Ast::List(vs)
            }
            Ast::Quoted(v) => Ast::Quoted(Box::new(func(*v, ctx)?)),
            Ast::DefineMacro(DefineMacro { id, args, body }) => {
                let body = body
                    .into_iter()
                    .map(|v| func(v, ctx))
                    .collect::<Result<Vec<_>>>()?;
                Ast::DefineMacro(DefineMacro { id, args, body })
            }
            Ast::Define(Define { id, init }) => {
                let init = Box::new(func(*init, ctx)?);
                Ast::Define(Define { id, init })
            }
            Ast::Lambda(Lambda {
                args,
                arg_types,
                body,
            }) => {
                let body = body
                    .into_iter()
                    .map(|v| func(v, ctx))
                    .collect::<Result<Vec<_>>>()?;
                Ast::Lambda(Lambda {
                    args,
                    arg_types,
                    body,
                })
            }
            Ast::Assign(Assign {
                var,
                var_loc,
                value,
            }) => {
                let value = Box::new(func(*value, ctx)?);
                Ast::Assign(Assign {
                    var,
                    var_loc,
                    value,
                })
            }
            Ast::IfExpr(IfExpr {
                cond,
                then_ast,
                else_ast,
            }) => {
                let cond = Box::new(func(*cond, ctx)?);
                let then_ast = Box::new(func(*then_ast, ctx)?);
                if let Some(else_ast) = else_ast {
                    let else_ast = Box::new(func(*else_ast, ctx)?);
                    Ast::IfExpr(IfExpr {
                        cond,
                        then_ast,
                        else_ast: Some(else_ast),
                    })
                } else {
                    Ast::IfExpr(IfExpr {
                        cond,
                        then_ast,
                        else_ast: None,
                    })
                }
            }
            Ast::Cond(Cond { clauses }) => {
                let clauses = clauses
                    .into_iter()
                    .map(|CondClause { cond, body }| {
                        let cond = Box::new(func(*cond, ctx)?);
                        let body = body
                            .into_iter()
                            .map(|v| func(v, ctx))
                            .collect::<Result<Vec<_>>>()?;
                        Ok(CondClause { cond, body })
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ast::Cond(Cond { clauses })
            }
            Ast::Let(Let {
                sequential,
                proc_id,
                inits,
                body,
            }) => {
                let inits = inits
                    .into_iter()
                    .map(|(var, val)| Ok((var, func(val, ctx)?)))
                    .collect::<Result<Vec<_>>>()?;
                let body = body
                    .into_iter()
                    .map(|v| func(v, ctx))
                    .collect::<Result<Vec<_>>>()?;
                Ast::Let(Let {
                    sequential,
                    proc_id,
                    inits,
                    body,
                })
            }
            Ast::Begin(Begin { body }) => {
                let body = body
                    .into_iter()
                    .map(|v| func(v, ctx))
                    .collect::<Result<Vec<_>>>()?;
                Ast::Begin(Begin { body })
            }
            Ast::Loop(Loop { inits, label, body }) => {
                let inits = inits
                    .into_iter()
                    .map(|(var, val)| Ok((var, func(val, ctx)?)))
                    .collect::<Result<Vec<_>>>()?;
                let body = body
                    .into_iter()
                    .map(|v| func(v, ctx))
                    .collect::<Result<Vec<_>>>()?;
                Ast::Loop(Loop { inits, label, body })
            }
            Ast::BuildList(vs) => {
                let vs = vs
                    .into_iter()
                    .map(|v| func(v, ctx))
                    .collect::<Result<Vec<_>>>()?;
                Ast::BuildList(vs)
            }
        };

        Ok(AnnotatedAst { ast, location, ty })
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
            Ast::Lambda(Lambda {
                args,
                arg_types,
                body,
            }) => {
                write!(f, "(lambda (")?;
                write_values(
                    f,
                    &args
                        .iter()
                        .zip(arg_types)
                        .map(|(arg, ty)| {
                            if let Some(ty) = ty {
                                format!("{}: {}", arg.value, ty.value)
                            } else {
                                arg.value.to_owned()
                            }
                        })
                        .collect::<Vec<_>>(),
                )?;
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
            Ast::Loop(Loop { inits, label, body }) => {
                write!(f, "(loop:{} ", label)?;
                for (id, expr) in inits {
                    write!(f, "(define {} {}) ", id.value, expr)?;
                }
                write_values(f, body)?;
                write!(f, ")")
            }
            Ast::BuildList(values) => {
                write!(f, "(list ")?;
                write_values(f, values)?;
                write!(f, ")")
            }
            Ast::Continue(label) => write!(f, "(continue {})", label),
        }?;

        if self.ty != Type::None {
            // write!(f, ": {}", self.ty)
            Ok(())
        } else {
            Ok(())
        }
    }
}

pub fn dump_asts(asts: &Vec<AnnotatedAst>) {
    for ast in asts {
        printlnuw(&format!("{}", ast));
    }
}
