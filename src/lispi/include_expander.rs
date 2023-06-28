use anyhow::Result;
use itertools::Itertools;

use super::{ast::*, common::read_lines, parser as p, tokenizer as t};

fn expand_includes_ast(ast: AnnotatedAst) -> Result<p::Program> {
    let AnnotatedAst { ast, location, ty } = ast;

    let prog = match ast {
        Ast::Include(path) => {
            // TODO: Interpret path as a relative path from the program location
            let lines = read_lines(path)?;
            let tokens = t::tokenize(lines)?;
            let program = p::parse(tokens)?;
            expand_includes(program)?
        }
        _ => vec![AnnotatedAst { ast, location, ty }],
    };

    Ok(prog)
}

pub fn expand_includes(asts: p::Program) -> Result<p::Program> {
    let asts = asts
        .into_iter()
        .map(expand_includes_ast)
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .flatten()
        .collect_vec();

    Ok(asts)
}
