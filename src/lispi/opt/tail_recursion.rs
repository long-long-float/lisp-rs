use anyhow::Result;

use super::super::{ast::*, parser::*, SymbolValue, TokenLocation};

/// Try to optimize tail recursion for body.
///
/// This removes tail recursion such as following forms.
///
/// ```lisp
/// (let loop ((i 0)) (if (< i 1000
///  (begin
///   (loop (+ i 1)))))
/// ```
///
/// This is converted to like following expressions.
///
/// ```lisp
/// (define i 0)
/// (internal-loop (if (< i 1000
///  (begin
///   (set! i (+ i 1))
///   continue))))
/// ```
///
/// A `internal-loop` behaves like `while(true)`. However it breaks without continue.
/// A `continue` is special value used only in this interpreter.
/// If the evaluator meets `continue`, the process goes a head of `internal-loop`.
///
/// This optimization is followed by https://people.csail.mit.edu/jaffer/r5rs/Proper-tail-recursion.html .
///
// TOOD: Support body what the function is assigned other variable
fn optimize_tail_recursion(
    func_name: &String,
    locals: &[SymbolValue],
    body: &[AnnotatedAst],
) -> Option<Vec<AnnotatedAst>> {
    fn _optimize_tail_recursion(
        func_name: &String,
        locals: &[SymbolValue],
        ast: &AnnotatedAst,
    ) -> Option<AnnotatedAst> {
        match &ast.ast {
            Ast::List(vs) => {
                if let Some((name_ast, args)) = vs.split_first() {
                    if let Ast::Symbol(name) = &name_ast.ast {
                        let name = name.value.as_str();
                        let mut args = {
                            let not_in_args =
                                args.iter().all(|arg| !includes_symbol(func_name, &arg.ast));

                            if name == func_name && not_in_args {
                                let mut body = args
                                    .iter()
                                    .zip(locals)
                                    .map(|(arg, sym)| {
                                        Ast::Assign(Assign {
                                            var: sym.clone(),
                                            var_loc: TokenLocation::Null,
                                            value: Box::new(arg.clone()),
                                        })
                                        .with_null_location()
                                    })
                                    .collect::<Vec<_>>();

                                body.push(Ast::Continue(name.to_string()).with_null_location());

                                return Some(Ast::Begin(Begin { body }).with_null_location());
                            } else {
                                None
                            }
                        };
                        args.as_mut().map(|args| {
                            let mut whole = vec![name_ast.clone()];
                            whole.append(args);
                            Ast::List(whole).with_null_location()
                        })
                    } else {
                        // This is not valid ast
                        None
                    }
                } else {
                    Some(ast.clone())
                }
            }
            Ast::Assign(assign) => Some(ast.clone().with_new_ast(Ast::Assign(Assign {
                value: Box::new(_optimize_tail_recursion(
                    func_name,
                    locals,
                    assign.value.as_ref(),
                )?),
                ..assign.clone()
            }))),
            Ast::IfExpr(if_expr) => {
                if includes_symbol(func_name, &if_expr.cond.ast) {
                    return None;
                }

                let cond = if_expr.cond.clone();
                let then_ast = Box::new(_optimize_tail_recursion(
                    func_name,
                    locals,
                    if_expr.then_ast.as_ref(),
                )?);

                let if_expr = if let Some(else_ast) = &if_expr.else_ast {
                    let else_ast = Some(Box::new(_optimize_tail_recursion(
                        func_name,
                        locals,
                        else_ast.as_ref(),
                    )?));
                    IfExpr {
                        cond,
                        then_ast,
                        else_ast,
                    }
                } else {
                    IfExpr {
                        cond,
                        then_ast,
                        else_ast: None,
                    }
                };

                Some(ast.clone().with_new_ast(Ast::IfExpr(if_expr)))
            }
            Ast::Let(Let {
                sequential,
                proc_id,
                inits,
                body,
            }) => {
                let sequential = *sequential;
                let proc_id = proc_id.clone();

                let includes_sym_in_inits = inits
                    .iter()
                    .any(|(_k, v)| includes_symbol(func_name, &v.ast));

                if includes_sym_in_inits {
                    return None;
                }

                let body = optimize_tail_recursion(func_name, locals, body)?;

                Some(ast.clone().with_new_ast(Ast::Let(Let {
                    sequential,
                    proc_id,
                    inits: inits.clone(),
                    body,
                })))
            }
            Ast::Begin(Begin { body }) => {
                let body = optimize_tail_recursion(func_name, locals, body)?;
                Some(ast.clone().with_new_ast(Ast::Begin(Begin { body })))
            }
            Ast::Loop(Loop { inits, label, body }) => {
                let includes_sym_in_inits = inits
                    .iter()
                    .any(|(_k, v)| includes_symbol(func_name, &v.ast));

                if includes_sym_in_inits {
                    return None;
                }

                let body = optimize_tail_recursion(func_name, locals, body)?;
                Some(ast.clone().with_new_ast(Ast::Loop(Loop {
                    inits: inits.clone(),
                    label: label.to_string(),
                    body,
                })))
            }
            Ast::BuildList(vs) => {
                let vs = optimize_tail_recursion(func_name, locals, vs)?;
                Some(ast.clone().with_new_ast(Ast::BuildList(vs)))
            }
            Ast::Cond(Cond { clauses }) => {
                let clauses = clauses
                    .into_iter()
                    .map(|CondClause { cond, body }| {
                        Some(CondClause {
                            cond: Box::new(_optimize_tail_recursion(func_name, locals, cond)?),
                            body: optimize_tail_recursion(func_name, locals, body)?,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(ast.clone().with_new_ast(Ast::Cond(Cond { clauses })))
            }
            Ast::Quoted(v) => _optimize_tail_recursion(func_name, locals, &v),
            Ast::Symbol(_)
            | Ast::SymbolWithType(_, _)
            | Ast::Integer(_)
            | Ast::Float(_)
            | Ast::Boolean(_)
            | Ast::Char(_)
            | Ast::String(_)
            | Ast::Nil
            | Ast::DefineMacro(_)
            | Ast::Define(_)
            | Ast::Lambda(_)
            | Ast::Continue(_) => Some(ast.clone()),
        }
    }

    fn includes_symbol(sym: &String, ast: &Ast) -> bool {
        match ast {
            Ast::List(vs) => vs.iter().any(|v| includes_symbol(sym, &v.ast)),
            Ast::Quoted(v) => includes_symbol(sym, &v.ast),
            Ast::Symbol(v) => &v.value == sym,
            Ast::SymbolWithType(v, _) => &v.value == sym,
            Ast::Assign(assign) => {
                &assign.var.value == sym || includes_symbol(sym, &assign.value.ast)
            }
            Ast::IfExpr(IfExpr {
                cond,
                then_ast,
                else_ast,
            }) => {
                includes_symbol(sym, &cond.ast)
                    || includes_symbol(sym, &then_ast.ast)
                    || else_ast
                        .as_ref()
                        .map(|else_ast| includes_symbol(sym, &else_ast.ast))
                        .unwrap_or(false)
            }
            Ast::Let(Let { inits, body, .. }) => {
                inits.iter().any(|(_k, v)| includes_symbol(sym, &v.ast))
                    | body.iter().any(|b| includes_symbol(sym, &b.ast))
            }
            Ast::Begin(Begin { body }) => body.iter().any(|b| includes_symbol(sym, &b.ast)),
            Ast::Loop(Loop { inits, body , ..}) => {
                inits.iter().any(|(_k, v)| includes_symbol(sym, &v.ast))
                    | body.iter().any(|b| includes_symbol(sym, &b.ast))
            }
            Ast::BuildList(vs) => vs.iter().any(|v| includes_symbol(sym, &v.ast)),
            Ast::Cond(Cond { clauses }) => clauses.iter().any(|CondClause { cond, body }| {
                includes_symbol(sym, &cond.ast) || body.iter().any(|b| includes_symbol(sym, &b.ast))
            }),
            Ast::Integer(_)
            | Ast::Float(_)
            | Ast::Boolean(_)
            | Ast::Char(_)
            | Ast::String(_)
            | Ast::Nil
            | Ast::DefineMacro(_)
            | Ast::Define(_)
            | Ast::Lambda(_)
            | Ast::Continue(_) => false,
        }
    }

    let len = body.len();
    match len {
        0 => None,
        _ => {
            let (last, body) = body.split_last().unwrap();
            for ast in body {
                if includes_symbol(func_name, &ast.ast) {
                    return None;
                }
            }
            _optimize_tail_recursion(func_name, locals, last).map(|last| {
                let mut body = body.to_vec();
                body.push(last);
                body
            })
        }
    }
}

fn opt_tail_recursion_ast(ast: AnnotatedAst, _: &()) -> Result<AnnotatedAst> {
    let AnnotatedAst { ast, location, ty } = ast;

    match ast {
        Ast::Let(Let {
            sequential,
            proc_id,
            inits,
            body,
        }) => {
            let inits = inits
                .into_iter()
                .map(|(id, expr)| Ok((id, opt_tail_recursion_ast(expr, &())?)))
                .collect::<Result<Vec<_>>>()?;

            let body = body
                .into_iter()
                .map(|ast| opt_tail_recursion_ast(ast, &()))
                .collect::<Result<Vec<_>>>()?;

            if let Some(proc_id) = &proc_id {
                // named let

                let args = inits.iter().map(|(id, _)| id.clone()).collect::<Vec<_>>();
                if let Some(optimized) = optimize_tail_recursion(&proc_id.value, &args, &body) {
                    return Ok(AnnotatedAst {
                        ast: Ast::Loop(Loop {
                            inits,
                            label: proc_id.value.clone(),
                            body: optimized,
                        }),
                        location,
                        ty,
                    });
                }
            }

            Ok(AnnotatedAst {
                ast: Ast::Let(Let {
                    sequential,
                    proc_id,
                    inits,
                    body,
                }),
                location,
                ty,
            })
        }
        _ => {
            let annot = AnnotatedAst { ast, location, ty };
            annot.traverse(&(), opt_tail_recursion_ast)
        }
    }
}

pub fn optimize(asts: Program) -> Result<Program> {
    asts.into_iter()
        .map(|ast| opt_tail_recursion_ast(ast, &()))
        .collect::<Result<Vec<_>>>()
}
