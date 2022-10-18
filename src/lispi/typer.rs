use std::fmt::write;

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
    Nil,

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

    Variable(String),
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
            Type::Nil => write!(f, "nil"),
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
            Type::Variable(v) => write!(f, "{}", v),
        }
    }
}

type TypeEnv = Environment<Type>;

#[derive(Clone, PartialEq, Debug)]
struct TypeVariable {
    name: String,
}

#[derive(Clone, PartialEq, Debug)]
struct TypeAssignment {
    left: TypeVariable,
    right: Type,
}

impl TypeAssignment {
    fn new(left: TypeVariable, right: Type) -> Self {
        Self { left, right }
    }
}

#[derive(Clone, PartialEq, Debug)]
struct TypeVarGenerator(u32);

impl TypeVarGenerator {
    fn new() -> Self {
        Self(0)
    }

    fn gen_string(&mut self) -> String {
        let id = self.0;
        self.0 += 1;
        format!("T{}", id)
    }

    fn gen_tv(&mut self) -> Type {
        Type::Variable(self.gen_string())
    }
}

struct Context {
    env: TypeEnv,
    tv_gen: TypeVarGenerator,
}

fn type_list(vs: &[AnnotatedAst], ctx: &mut Context) -> Result<()> {
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

fn collect_constraints(
    ast: AnnotatedAst,
    ctx: &mut Context,
) -> Result<(AnnotatedAst, Vec<TypeAssignment>)> {
    match &ast.ast {
        Ast::List(vs) => Ok((ast, Vec::new())),
        Ast::Quoted(inner) => {
            let (inner, c) = collect_constraints(*inner.clone(), ctx)?;
            Ok((ast.with_new_type(inner.ty.unwrap()), c))
        }
        Ast::Integer(_) => Ok((ast.with_new_type(Type::Int), Vec::new())),
        Ast::Float(_) => Ok((ast.with_new_type(Type::Float), Vec::new())),
        Ast::Boolean(_) => Ok((ast.with_new_type(Type::Boolean), Vec::new())),
        Ast::Char(_) => Ok((ast.with_new_type(Type::Char), Vec::new())),
        Ast::String(_) => Ok((ast.with_new_type(Type::String), Vec::new())),
        Ast::Nil => Ok((ast.with_new_type(Type::Nil), Vec::new())),
        Ast::Symbol(id) | Ast::SymbolWithType(id, _) => {
            if let Some(ty) = ctx.env.find_var(&id) {
                Ok((ast.with_new_type(ty), Vec::new()))
            } else {
                Err(Error::UndefindVariable(id.value.clone())
                    .with_location(ast.location)
                    .into())
            }
        }
        // Ast::SymbolWithType(id, anot_ty) => {
        //     if let Some(ty) = ctx.env.find_var(&id) {
        //         ast.ty = Some(ty);
        //         Ok(vec![TypeAssignment::new()])
        //     }
        //     else {
        //     }
        // },
        Ast::Define(Define { id, init }) => {
            let (init, c) = collect_constraints(*init.clone(), ctx)?;
            println!("{}", init);
            // init must have a type.
            ctx.env
                .insert_var(id.clone(), init.ty.as_ref().unwrap().clone());
            Ok((init, c))
        }
        Ast::Lambda(Lambda { args, body }) => {
            let fun_ty = Type::Function {
                args: args.iter().map(|_| Box::new(ctx.tv_gen.gen_tv())).collect(),
                result: Box::new(ctx.tv_gen.gen_tv()),
            };
            Ok((ast.with_new_type(fun_ty), Vec::new()))
        }
        Ast::Continue(_) | Ast::DefineMacro(_) => Ok((ast, Vec::new())),
    }
}

// fn collect_constraints(ast: &mut AnnotatedAst, ctx: &mut Context) -> Result<Vec<TypeAssignment>> {
//     match &ast.ast {
//         Ast::List(vs) => {
//             Ok(Vec::new())
//         }
//         Ast::Quoted(inner) => {
//             let ret = collect_constraints(inner.as_mut(), ctx)?;
//             ast.ty = inner.ty.clone();
//             Ok(ret)
//         }
//         Ast::Integer(v) => {
//             ast.ty = Some(Type::Int);
//             Ok(Vec::new())
//         }
//         Ast::Float(_) => {
//             ast.ty = Some(Type::Float);
//             Ok(Vec::new())
//         }
//         Ast::Boolean(_) => {
//             ast.ty = Some(Type::Boolean);
//             Ok(Vec::new())
//         }
//         Ast::Char(_) => {
//             ast.ty = Some(Type::Char);
//             Ok(Vec::new())
//         }
//         Ast::String(_) => {
//             ast.ty = Some(Type::String);
//             Ok(Vec::new())
//         }
//         Ast::Nil => {
//             ast.ty = Some(Type::Nil);
//             Ok(Vec::new())
//         }
//         Ast::Symbol(id) | Ast::SymbolWithType(id, _) => {
//             if let Some(ty) = ctx.env.find_var(&id) {
//                 ast.ty = Some(ty);
//                 Ok(Vec::new())
//             } else {
//                 Err(Error::UndefindVariable(id.value.clone())
//                     .with_location(ast.location)
//                     .into())
//             }
//         }
//         // Ast::SymbolWithType(id, anot_ty) => {
//         //     if let Some(ty) = ctx.env.find_var(&id) {
//         //         ast.ty = Some(ty);
//         //         Ok(vec![TypeAssignment::new()])
//         //     }
//         //     else {
//         //     }
//         // },

//         Ast::Define(Define { id, init }) => {
//             let ret = collect_constraints(&mut init, ctx)?;
//             // init must have a type.
//             ctx.env.insert_var(id.clone(), init.ty.unwrap());
//             Ok(ret)
//         }
//         Ast::Continue(_) |
//         Ast::DefineMacro(_) => {
//             Ok(Vec::new())
//         }
//     }
// }

pub fn check_and_inference_type(asts: Program, mut env: Environment<()>) -> Result<Program> {
    let mut ctx = Context {
        env: TypeEnv::new(),
        tv_gen: TypeVarGenerator::new(),
    };

    let mut tv_asts = Vec::new();
    let mut constraints = Vec::new();
    for ast in asts {
        let (ast, mut subc) = collect_constraints(ast, &mut ctx)?;
        constraints.append(&mut subc);
        tv_asts.push(ast);
    }

    Ok(tv_asts)
}
