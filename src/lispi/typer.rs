use anyhow::{anyhow, Result};
use rustc_hash::FxHashMap;

use crate::{ast_pat, match_special_args};

use super::{environment::*, error::*, evaluator::*, parser::*};

#[derive(Clone, PartialEq, Debug)]
pub enum Type {
    Numeric,
    Int,
    Float,
    Boolean,
    Char,
    String,

    Scala(String),
    Composite {
        name: String,
        inner: Vec<Box<Type>>,
    },
    Function {
        args: Vec<Box<Type>>,
        result: Box<Type>,
    },
    Any,
}

impl Type {
    fn scala(name: &str) -> Type {
        Type::Scala(name.to_string())
    }

    pub fn int() -> Type {
        Type::Int
    }

    pub fn symbol() -> Type {
        Type::scala("symbol")
    }

    pub fn list() -> Type {
        Type::Composite {
            name: "list".to_string(),
            inner: Vec::new(),
        }
    }

    pub fn function(args: Vec<Type>, result: Type) -> Type {
        Type::Function {
            args: args.iter().map(|a| Box::new(a.clone())).collect(),
            result: Box::new(result),
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Type::Numeric => write!(f, "numeric"),
            Type::Int => write!(f, "int"),
            Type::Float => write!(f, "float"),
            Type::Boolean => write!(f, "boolean"),
            Type::Char => write!(f, "char"),
            Type::String => write!(f, "string"),
            Type::Scala(name) => write!(f, "{}", name),
            Type::Composite { name, inner } => {
                let inner = inner
                    .iter()
                    .map(|t| format!("{}", *t))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{}({})", name, inner)
            }
            Type::Function { args, result } => {
                let args = args
                    .iter()
                    .map(|t| format!("{}", *t))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({}) -> {}", args, *result)
            }
            Type::Any => write!(f, "any"),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
struct TypeEnv {
    table: FxHashMap<String, Type>,
}

impl TypeEnv {
    fn new() -> Self {
        Self {
            table: FxHashMap::default(),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
struct TypeVariable {}

#[derive(Clone, PartialEq, Debug)]
struct TypeAssignment {
    left: TypeVariable,
    right: Type,
}

fn type_list(vs: &[AnnotatedAst], env: &mut TypeEnv) -> Result<()> {
    // if let Some((name, args)) = vs.split_first() {
    //     if let Ast::Symbol(name) = &name.ast {
    //         match name.value.as_str() {
    //             "define" => {
    //                 match_special_args!(args, ast_pat!(Ast::Symbol(id), _), mut init, {
    //                     type_ast(&mut init, env)?;
    //                     env.table.insert(id.value.clone(), init.ty.unwrap().clone());
    //                     Ok(())
    //                 })?;
    //             }
    //             _ => {}
    //         }
    //     }
    // }

    Ok(())
}

fn collect_constraints(ast: &mut AnnotatedAst, env: &mut TypeEnv) -> Result<Vec<TypeAssignment>> {
    match &ast.ast {
        Ast::List(vs) => {
            type_list(&vs, env)?;
        }
        Ast::Quoted(_) => todo!(),
        Ast::Integer(_) => {
            ast.ty = Some(Type::Int);
        }
        Ast::Float(_) => {
            ast.ty = Some(Type::Float);
        }
        Ast::Symbol(id) => if let Some(var) = env.table.get(&id.value) {},
        Ast::SymbolWithType(_, _) => todo!(),
        Ast::Boolean(_) => todo!(),
        Ast::Char(_) => todo!(),
        Ast::String(_) => todo!(),
        Ast::Nil => todo!(),
        Ast::Continue(_) => todo!(),
        Ast::DefineMacro(_) => todo!(),
        Ast::Define(Define { id, init }) => {}
    }

    Ok(Vec::new())
}

pub fn check_and_inference_type(
    mut asts: Program,
    mut env: Environment<()>,
) -> Result<(Program, Environment<()>)> {
    let mut ty_env = TypeEnv::new();
    for ast in asts.iter_mut() {
        collect_constraints(ast, &mut ty_env)?;
    }
    Ok((asts, env))
}
