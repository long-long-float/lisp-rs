use anyhow::Result;
use colored::*;
use rustc_hash::FxHashSet;
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
    ListLiteral(Vec<AnnotatedAst>),
    ArrayLiteral(Vec<AnnotatedAst>),

    /// For optimizing tail recursion
    Loop(Loop),
    Continue(Continue),
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
                if name.is_empty() {
                    // Function created by lambda
                    let mut elem = vec![
                        Ast::Symbol("lambda".to_string()).with_null_location(),
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
            Value::Continue(_) => todo!(),
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
        Ast::Symbol(value.to_string())
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

impl Lambda {}

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
pub struct Continue {
    /// Corresponds to [`Loop::label`]
    pub label: String,
    /// Each elements correspond to [`Loop::inits`]
    pub updates: Vec<AnnotatedAst>,
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
            Ast::ListLiteral(vs) => {
                let vs = vs
                    .into_iter()
                    .map(|v| func(v, ctx))
                    .collect::<Result<Vec<_>>>()?;
                Ast::ListLiteral(vs)
            }
            Ast::ArrayLiteral(vs) => {
                let vs = vs
                    .into_iter()
                    .map(|v| func(v, ctx))
                    .collect::<Result<Vec<_>>>()?;
                Ast::ArrayLiteral(vs)
            }
        };

        Ok(AnnotatedAst { ast, location, ty })
    }

    pub fn traverse_ref<F, A>(&self, ctx: &mut A, func: F) -> Result<()>
    where
        F: Fn(&Self, &mut A) -> Result<()>,
    {
        let AnnotatedAst { ast, .. } = self;
        match ast {
            Ast::Integer(_)
            | Ast::Float(_)
            | Ast::Symbol(_)
            | Ast::SymbolWithType(_, _)
            | Ast::Boolean(_)
            | Ast::Char(_)
            | Ast::String(_)
            | Ast::Nil => {}
            Ast::List(vs) => {
                for v in vs {
                    func(v, ctx)?;
                }
            }
            Ast::Quoted(v) => {
                func(v, ctx)?;
            }
            Ast::DefineMacro(DefineMacro { body, .. }) => {
                for v in body {
                    func(v, ctx)?;
                }
            }
            Ast::Define(Define { init, .. }) => {
                func(init, ctx)?;
            }
            Ast::Lambda(Lambda { body, .. }) => {
                for v in body {
                    func(v, ctx)?;
                }
            }
            Ast::Assign(Assign { value, .. }) => {
                func(value, ctx)?;
            }
            Ast::IfExpr(IfExpr {
                cond,
                then_ast,
                else_ast,
            }) => {
                func(cond, ctx)?;
                func(then_ast, ctx)?;
                if let Some(else_ast) = else_ast {
                    func(else_ast, ctx)?;
                }
            }
            Ast::Cond(Cond { clauses }) => {
                for CondClause { cond, body } in clauses {
                    func(cond, ctx)?;
                    for v in body {
                        func(v, ctx)?;
                    }
                }
            }
            Ast::Let(Let { inits, body, .. }) => {
                for (_, val) in inits {
                    func(val, ctx)?;
                }
                for v in body {
                    func(v, ctx)?;
                }
            }
            Ast::Begin(Begin { body }) => {
                for v in body {
                    func(v, ctx)?;
                }
            }
            Ast::Loop(Loop { inits, body, .. }) => {
                for (_, val) in inits {
                    func(val, ctx)?;
                }
                for v in body {
                    func(v, ctx)?;
                }
            }
            Ast::Continue(Continue { updates, .. }) => {
                for ast in updates {
                    func(ast, ctx)?;
                }
            }
            Ast::ListLiteral(vs) => {
                for v in vs {
                    func(v, ctx)?;
                }
            }
            Ast::ArrayLiteral(vs) => {
                for v in vs {
                    func(v, ctx)?;
                }
            }
        }

        Ok(())
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
            Ast::Symbol(v) => write!(f, "{}", v),
            Ast::SymbolWithType(v, t) => write!(f, "{}:{}", v, t),
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
                write!(f, "(define-macro {} (", id)?;
                write_values(f, args)?;
                write!(f, ") ")?;
                write_values(f, body)?;
                write!(f, ")")
            }
            Ast::Define(Define { id, init }) => {
                write!(f, "(define {} {})", id, *init)
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
                                format!("{}: {}", arg, ty)
                            } else {
                                arg.to_owned()
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
                write!(f, "(set! {} {})", var, value)
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
                    write!(f, "{} ", proc_id)?;
                }
                write!(f, "(")?;
                let inits = inits
                    .iter()
                    .map(|(k, v)| format!("[{} {}]", k, v))
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
                    write!(f, "(define {} {}) ", id, expr)?;
                }
                write_values(f, body)?;
                write!(f, ")")
            }
            Ast::ListLiteral(values) => {
                write!(f, "(list ")?;
                write_values(f, values)?;
                write!(f, ")")
            }
            Ast::ArrayLiteral(values) => {
                write!(f, "(array ")?;
                write_values(f, values)?;
                write!(f, ")")
            }
            Ast::Continue(Continue { label, updates }) => {
                write!(f, "(continue:{} (", label)?;
                for update in updates {
                    write!(f, "{} ", update)?;
                }
                write!(f, ")")
            }
        }?;

        match &self.ty {
            Type::Function { .. } | Type::None => Ok(()),

            _ => {
                let str = format!(":{}", self.ty);
                write!(f, "{}", str.dimmed())
            }
        }
    }
}

pub fn dump_asts(asts: &Vec<AnnotatedAst>) {
    for ast in asts {
        printlnuw(&format!("{}", ast));
    }
}

/// Collect free variables from asts with binds
pub fn collect_free_vars(asts: &[AnnotatedAst], binds: Vec<SymbolValue>) -> FxHashSet<SymbolValue> {
    struct Context {
        binds: Vec<SymbolValue>,
        frees: FxHashSet<SymbolValue>,
    }

    fn collect_free_vars_inner(ast: &AnnotatedAst, ctx: &mut Context) -> Result<()> {
        match &ast.ast {
            Ast::Symbol(sym) | Ast::SymbolWithType(sym, _) => {
                if !ctx.binds.iter().any(|var| var == sym) {
                    ctx.frees.insert(sym.clone());
                }
            }
            _ => ast.traverse_ref(ctx, collect_free_vars_inner)?,
        }

        Ok(())
    }

    let mut ctx = Context {
        binds,
        frees: FxHashSet::default(),
    };

    for ast in asts {
        let _ = ast.traverse_ref(&mut ctx, collect_free_vars_inner);
    }

    ctx.frees
}
