use std::fmt::Display;

use super::{evaluator::Value, typer::Type, LocationRange, SymbolValue, TokenLocation};

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
    Let(Let),

    /// For optimizing tail recursion
    Continue(String),
}

impl Ast {
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

/// For evaluating macros
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
                        .map(|v| Ast::from(v).with_null_location())
                        .collect();
                    Ast::List(vs)
                }
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
pub struct Let {
    pub sequential: bool,
    pub proc_id: Option<SymbolValue>,
    pub inits: Vec<(SymbolValue, AnnotatedAst)>,
    pub body: Vec<AnnotatedAst>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct AnnotatedAst {
    pub ast: Ast,
    pub location: TokenLocation,
    pub ty: Option<Type>,
}

impl AnnotatedAst {
    fn new(ast: Ast, location: TokenLocation) -> Self {
        Self {
            ast,
            location,
            ty: None,
        }
    }

    pub fn with_new_ast(self, new_ast: Ast) -> Self {
        Self {
            ast: new_ast,
            ..self
        }
    }

    pub fn with_new_type(self, new_ty: Type) -> Self {
        Self {
            ty: Some(new_ty),
            ..self
        }
    }

    pub fn with_new_ast_and_type(self, new_ast: Ast, new_ty: Type) -> Self {
        Self {
            ast: new_ast,
            ty: Some(new_ty),
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
            Ast::Continue(_) => write!(f, "CONTINUE"),
        }?;

        if let Some(ty) = &self.ty {
            write!(f, ": {}", ty)
        } else {
            Ok(())
        }
    }
}
