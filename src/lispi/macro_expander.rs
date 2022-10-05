use std::collections::HashMap;

use super::{console::*, error::*, parser::*, typer::*, SymbolValue, TokenLocation};
use anyhow::{anyhow, Result};

type MacroEnv = HashMap<u32, DefineMacro>;

pub fn expand_macros_ast(ast: AnnotatedAst, menv: &mut MacroEnv) -> Result<AnnotatedAst> {
    let AnnotatedAst { ast, location, ty } = ast;

    let result = match ast {
        Ast::DefineMacro(ref mac) => {
            menv.insert(mac.id.id, mac.clone());
            ast
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
                    .map(|arg| expand_macros_ast(arg.clone(), menv))
                    .collect::<Result<Vec<_>>>()?;

                let name = if let Some(mac) = menv.get(&name.id) {
                    // TODO: expand macro here
                    AnnotatedAst {
                        ast: Ast::Symbol(name.clone()),
                        location: name_loc.clone(),
                        ty: name_ty.clone(),
                    }
                } else {
                    AnnotatedAst {
                        ast: Ast::Symbol(name.clone()),
                        location: name_loc.clone(),
                        ty: name_ty.clone(),
                    }
                };

                let mut vs = vec![name];
                vs.append(&mut args);
                Ast::List(vs)
            } else {
                let vs = vs
                    .into_iter()
                    .map(|v| expand_macros_ast(v, menv))
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

pub fn expand_macros(asts: Program) -> Result<Program> {
    let mut menv = MacroEnv::new();

    let asts = asts
        .into_iter()
        .map(|ast| expand_macros_ast(ast, &mut menv))
        .collect::<Result<Vec<_>>>()?;

    Ok(asts)
}
