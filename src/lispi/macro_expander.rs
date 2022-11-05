use std::collections::HashMap;

use super::{ast::*, environment::Environment, evaluator::*, parser::*};
use anyhow::Result;

type MacroEnv = HashMap<u32, DefineMacro>;

pub fn expand_macros_asts(
    asts: Vec<AnnotatedAst>,
    menv: &mut MacroEnv,
    sym_env: &mut SymbolTable,
) -> Result<Vec<AnnotatedAst>> {
    asts.into_iter()
        .map(|ast| expand_macros_ast(ast, menv, sym_env))
        .collect::<Result<Vec<_>>>()
}

pub fn expand_macros_ast(
    ast: AnnotatedAst,
    menv: &mut MacroEnv,
    sym_env: &mut SymbolTable,
) -> Result<AnnotatedAst> {
    let AnnotatedAst { ast, location, ty } = ast;

    let result = match ast {
        Ast::DefineMacro(ref mac) => {
            menv.insert(mac.id.id, mac.clone());
            ast
        }
        Ast::Define(mut def) => {
            def.init = Box::new(expand_macros_ast(*def.init, menv, sym_env)?);
            Ast::Define(def)
        }
        Ast::Assign(mut assign) => {
            assign.value = Box::new(expand_macros_ast(*assign.value, menv, sym_env)?);
            Ast::Assign(assign)
        }
        Ast::IfExpr(mut if_expr) => {
            if_expr.cond = Box::new(expand_macros_ast(*if_expr.cond, menv, sym_env)?);
            if_expr.then_ast = Box::new(expand_macros_ast(*if_expr.then_ast, menv, sym_env)?);
            if let Some(else_ast) = if_expr.else_ast {
                if_expr.else_ast = Some(Box::new(expand_macros_ast(*else_ast, menv, sym_env)?))
            }

            Ast::IfExpr(if_expr)
        }
        Ast::Cond(mut cond) => {
            cond.clauses = cond
                .clauses
                .into_iter()
                .map(|CondClause { cond, body }| {
                    Ok(CondClause {
                        cond: Box::new(expand_macros_ast(*cond, menv, sym_env)?),
                        body: expand_macros_asts(body, menv, sym_env)?,
                    })
                })
                .collect::<Result<Vec<_>>>()?;

            Ast::Cond(cond)
        }
        Ast::Let(mut let_expr) => {
            let_expr.inits = let_expr
                .inits
                .into_iter()
                .map(|(k, v)| {
                    let v = expand_macros_ast(v, menv, sym_env)?;
                    Ok((k, v))
                })
                .collect::<Result<Vec<_>>>()?;
            let_expr.body = let_expr
                .body
                .into_iter()
                .map(|body| expand_macros_ast(body, menv, sym_env))
                .collect::<Result<Vec<_>>>()?;

            Ast::Let(let_expr)
        }
        Ast::Begin(Begin { body }) => {
            let body = body
                .into_iter()
                .map(|body| expand_macros_ast(body, menv, sym_env))
                .collect::<Result<Vec<_>>>()?;
            Ast::Begin(Begin { body })
        }
        Ast::BuildList(values) => {
            let values = values
                .into_iter()
                .map(|value| expand_macros_ast(value, menv, sym_env))
                .collect::<Result<Vec<_>>>()?;
            Ast::BuildList(values)
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
                    .into_iter()
                    .map(|arg| expand_macros_ast(arg.clone(), menv, sym_env))
                    .collect::<Result<Vec<_>>>()?;

                if let Some(mac) = menv.get(&name.id) {
                    let mut env = Environment::new();
                    let mut ty_env = Environment::new();

                    init_env(&mut env, &mut ty_env, sym_env);

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
                        location: name_loc.clone(),
                        ty: name_ty.clone(),
                    };

                    let mut vs = vec![name];
                    vs.append(&mut args);
                    Ast::List(vs)
                }
            } else {
                let vs = vs
                    .into_iter()
                    .map(|v| expand_macros_ast(v, menv, sym_env))
                    .collect::<Result<Vec<_>>>()?;
                Ast::List(vs)
            }
        }
        Ast::Lambda(Lambda { args, body }) => {
            let body = body
                .into_iter()
                .map(|ast| expand_macros_ast(ast, menv, sym_env))
                .collect::<Result<Vec<_>>>()?;
            Ast::Lambda(Lambda { args, body })
        }
        Ast::Symbol(_)
        | Ast::SymbolWithType(_, _)
        | Ast::Quoted(_)
        | Ast::Integer(_)
        | Ast::Float(_)
        | Ast::Boolean(_)
        | Ast::Char(_)
        | Ast::String(_)
        | Ast::Nil
        | Ast::Continue(_) => ast,
    };
    Ok(AnnotatedAst {
        ast: result,
        location,
        ty,
    })
}

pub fn expand_macros(asts: Program, sym_table: &mut SymbolTable) -> Result<Program> {
    let mut menv = MacroEnv::new();

    let asts = asts
        .into_iter()
        .map(|ast| expand_macros_ast(ast, &mut menv, sym_table))
        .collect::<Result<Vec<_>>>()?;

    Ok(asts)
}
