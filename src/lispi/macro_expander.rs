use std::collections::HashMap;

use super::{ast::*, environment::Environment, evaluator::*, parser::*};
use anyhow::Result;

type MacroEnv = HashMap<String, DefineMacro>;

pub fn expand_macros_asts(
    asts: Vec<AnnotatedAst>,
    menv: &mut MacroEnv,
) -> Result<Vec<AnnotatedAst>> {
    asts.into_iter()
        .map(|ast| expand_macros_ast(ast, menv))
        .collect::<Result<Vec<_>>>()
}

pub fn expand_macros_ast(ast: AnnotatedAst, menv: &mut MacroEnv) -> Result<AnnotatedAst> {
    let AnnotatedAst { ast, location, ty } = ast;

    let result = match ast {
        Ast::DefineMacro(ref mac) => {
            menv.insert(mac.id.to_owned(), mac.clone());
            ast
        }
        Ast::Define(mut def) => {
            def.init = Box::new(expand_macros_ast(*def.init, menv)?);
            Ast::Define(def)
        }
        Ast::DefineFunction(DefineFunction {
            id,
            lambda:
                Lambda {
                    args,
                    arg_types,
                    body,
                },
        }) => {
            let body = body
                .into_iter()
                .map(|ast| expand_macros_ast(ast, menv))
                .collect::<Result<Vec<_>>>()?;
            Ast::DefineFunction(DefineFunction {
                id,
                lambda: Lambda {
                    args,
                    arg_types,
                    body,
                },
            })
        }
        Ast::Assign(mut assign) => {
            assign.value = Box::new(expand_macros_ast(*assign.value, menv)?);
            Ast::Assign(assign)
        }
        Ast::IfExpr(mut if_expr) => {
            if_expr.cond = Box::new(expand_macros_ast(*if_expr.cond, menv)?);
            if_expr.then_ast = Box::new(expand_macros_ast(*if_expr.then_ast, menv)?);
            if let Some(else_ast) = if_expr.else_ast {
                if_expr.else_ast = Some(Box::new(expand_macros_ast(*else_ast, menv)?))
            }

            Ast::IfExpr(if_expr)
        }
        Ast::Cond(mut cond) => {
            cond.clauses = cond
                .clauses
                .into_iter()
                .map(|CondClause { cond, body }| {
                    Ok(CondClause {
                        cond: Box::new(expand_macros_ast(*cond, menv)?),
                        body: expand_macros_asts(body, menv)?,
                    })
                })
                .collect::<Result<Vec<_>>>()?;

            Ast::Cond(cond)
        }
        Ast::Let(Let {
            sequential,
            proc_id,
            inits,
            body,
        }) => {
            let inits = inits
                .into_iter()
                .map(|(k, v)| {
                    let v = expand_macros_ast(v, menv)?;
                    Ok((k, v))
                })
                .collect::<Result<Vec<_>>>()?;
            let body = body
                .into_iter()
                .map(|body| expand_macros_ast(body, menv))
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
                .map(|body| expand_macros_ast(body, menv))
                .collect::<Result<Vec<_>>>()?;
            Ast::Begin(Begin { body })
        }
        Ast::Loop(Loop { inits, label, body }) => {
            let inits = inits
                .into_iter()
                .map(|(k, v)| {
                    let v = expand_macros_ast(v, menv)?;
                    Ok((k, v))
                })
                .collect::<Result<Vec<_>>>()?;
            let body = body
                .into_iter()
                .map(|body| expand_macros_ast(body, menv))
                .collect::<Result<Vec<_>>>()?;
            Ast::Loop(Loop { inits, label, body })
        }
        Ast::ListLiteral(values) => {
            let values = values
                .into_iter()
                .map(|value| expand_macros_ast(value, menv))
                .collect::<Result<Vec<_>>>()?;
            Ast::ListLiteral(values)
        }
        Ast::ArrayLiteral(values) => {
            let values = values
                .into_iter()
                .map(|value| expand_macros_ast(value, menv))
                .collect::<Result<Vec<_>>>()?;
            Ast::ArrayLiteral(values)
        }
        Ast::List(vs) => {
            if let Some((
                AnnotatedAst {
                    ast: Ast::Symbol(name),
                    location: name_loc,
                    ty: name_ty,
                },
                args,
            )) = vs.split_first()
            {
                let mut args = args
                    .iter()
                    .map(|arg| expand_macros_ast(arg.clone(), menv))
                    .collect::<Result<Vec<_>>>()?;

                if let Some(mac) = menv.get(name) {
                    let mut env = Environment::default();
                    let mut ty_env = Environment::default();

                    init_env(&mut env, &mut ty_env);

                    for (name, value) in mac.args.iter().zip(args) {
                        env.insert_var(name.clone(), Value::RawAst(value.clone()));
                    }

                    let result = eval_asts(&mac.body, &mut env);

                    env.pop_local();

                    let result = get_last_result(result?);
                    Ast::from_value(result)?
                } else {
                    let name = AnnotatedAst {
                        ast: Ast::Symbol(name.clone()),
                        location: *name_loc,
                        ty: name_ty.clone(),
                    };

                    let mut vs = vec![name];
                    vs.append(&mut args);
                    Ast::List(vs)
                }
            } else {
                let vs = vs
                    .into_iter()
                    .map(|v| expand_macros_ast(v, menv))
                    .collect::<Result<Vec<_>>>()?;
                Ast::List(vs)
            }
        }
        Ast::Lambda(Lambda {
            args,
            arg_types,
            body,
        }) => {
            let body = body
                .into_iter()
                .map(|ast| expand_macros_ast(ast, menv))
                .collect::<Result<Vec<_>>>()?;
            Ast::Lambda(Lambda {
                args,
                arg_types,
                body,
            })
        }
        Ast::As(expr, ty) => Ast::As(Box::new(expand_macros_ast(*expr, menv)?), ty),
        Ast::Ref(expr) => Ast::Ref(Box::new(expand_macros_ast(*expr, menv)?)),
        Ast::Symbol(_)
        | Ast::SymbolWithType(_, _)
        | Ast::Quoted(_)
        | Ast::Integer(_)
        | Ast::Float(_)
        | Ast::Boolean(_)
        | Ast::Char(_)
        | Ast::String(_)
        | Ast::Nil
        | Ast::Continue(_)
        | Ast::Include(_)
        | Ast::DefineStruct(_) => ast,
    };
    Ok(AnnotatedAst {
        ast: result,
        location,
        ty,
    })
}

pub fn expand_macros(asts: Program) -> Result<Program> {
    let mut menv = MacroEnv::new();

    let asts = asts
        .into_iter()
        .map(|ast| expand_macros_ast(ast, &mut menv))
        .collect::<Result<Vec<_>>>()?;

    Ok(asts)
}
