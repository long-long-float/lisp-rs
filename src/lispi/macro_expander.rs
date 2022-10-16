use std::collections::HashMap;

use super::{environment::Environment, evaluator::*, parser::*};
use anyhow::Result;

type MacroEnv = HashMap<u32, DefineMacro>;

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

                    init_env(&mut env, sym_env);

                    for (name, value) in mac.args.iter().zip(args) {
                        env.insert_var(name.clone(), Value::RawAst(value.clone()).with_type());
                    }

                    let result = eval_asts(&mac.body, &mut env);

                    env.pop_local();

                    let result = get_last_result(result?);
                    Ast::from(result.value)
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
