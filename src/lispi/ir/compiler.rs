use std::{fmt::Display, vec};

use anyhow::Result;

use super::super::{
    ast::*, environment::Environment, error::Error, parser::*, typer::Type,
    unique_generator::UniqueGenerator,
};
use crate::{bug, unimplemented};

use super::instruction::*;

struct Context {
    env: Environment<Variable>,
    sym_table: SymbolTable,
    func_env: Environment<(Label, Function)>,
    var_gen: UniqueGenerator,
}

impl Context {
    fn gen_var(&mut self) -> Variable {
        Variable {
            name: format!("var{}", self.var_gen.gen()),
        }
    }

    fn gen_label(&mut self) -> Label {
        Label {
            name: format!("label{}", self.var_gen.gen()),
        }
    }
}

fn get_last_instr(insts: &Instructions) -> AnnotatedInstr {
    insts.last().unwrap().clone()
}

fn compile_and_add(
    result: &mut Vec<AnnotatedInstr>,
    ast: AnnotatedAst,
    ctx: &mut Context,
) -> Result<AnnotatedInstr> {
    let mut insts = compile_ast(ast, ctx)?;
    let inst = get_last_instr(&insts);
    result.append(&mut insts);
    Ok(inst)
}

fn add_instr(result: &mut Vec<AnnotatedInstr>, ctx: &mut Context, inst: Instruction, ty: Type) {
    result.push(AnnotatedInstr {
        result: ctx.gen_var(),
        inst,
        ty,
    });
}

fn compile_ast(ast: AnnotatedAst, ctx: &mut Context) -> Result<Instructions> {
    use Instruction as I;

    let AnnotatedAst {
        ast,
        location: _,
        ty: ast_ty,
    } = ast;

    let mut result = Vec::new();

    match ast {
        Ast::List(vs) => {
            if let Some((fun_ast, args)) = vs.split_first() {
                let args = args
                    .iter()
                    .map(|arg| compile_and_add(&mut result, arg.clone(), ctx))
                    .collect::<Result<Vec<_>>>()?;

                // result.append(&mut args.clone().into_iter().flatten().collect::<Vec<_>>());

                if let AnnotatedAst {
                    ast: Ast::Symbol(fun),
                    ..
                } = fun_ast
                {
                    let name = fun.value.as_str();
                    match name {
                        "+" | "-" | "*" | "<=" | "or" => {
                            let AnnotatedInstr {
                                result: left,
                                inst: _inst,
                                ty: _ty,
                            } = args[0].clone();
                            let right = args[1].result.clone();

                            let left = Operand::Variable(left);
                            let right = Operand::Variable(right);

                            let inst = match name {
                                "+" => I::Add(left, right),
                                "-" => I::Sub(left, right),
                                "*" => I::Mul(left, right),
                                "<=" => I::Cmp(CmpOperator::SGE, left, right),
                                "or" => I::Or(left, right),
                                _ => return Err(bug!()),
                            };
                            add_instr(&mut result, ctx, inst, ast_ty);
                        }
                        "io-write" => {
                            add_instr(
                                &mut result,
                                ctx,
                                I::Store(
                                    Operand::Variable(args[0].result.clone()),
                                    Operand::Variable(args[1].result.clone()),
                                ),
                                ast_ty,
                            );
                        }
                        _ => {
                            let fun = compile_and_add(&mut result, fun_ast.clone(), ctx)?;
                            // let fun_label = ctx.func_env.find_var(fun).unwrap();
                            let args = args
                                .into_iter()
                                .map(|arg| Operand::Variable(arg.result))
                                .collect();
                            add_instr(
                                &mut result,
                                ctx,
                                I::Call {
                                    fun: Operand::Variable(fun.result),
                                    args,
                                },
                                ast_ty,
                            );
                        }
                    }
                }
            } else {
                return Err(unimplemented!());
            }
        }
        Ast::Quoted(_) => todo!(),
        Ast::Integer(v) => add_instr(
            &mut result,
            ctx,
            I::Operand(Operand::Immediate(Immediate::Integer(v))),
            ast_ty,
        ),
        Ast::Float(_) => todo!(),
        Ast::Symbol(sym) => {
            if let Some((label, _)) = ctx.func_env.find_var(&sym) {
                add_instr(
                    &mut result,
                    ctx,
                    I::Operand(Operand::Immediate(Immediate::Label(label))),
                    ast_ty,
                );
            } else if let Some(var) = ctx.env.find_var(&sym) {
                add_instr(&mut result, ctx, I::Operand(Operand::Variable(var)), ast_ty);
            } else {
                return Err(Error::UndefinedVariable(sym.value)
                    .with_null_location()
                    .into());
            }
        }
        Ast::SymbolWithType(_, _) => todo!(),
        Ast::Boolean(v) => add_instr(
            &mut result,
            ctx,
            I::Operand(Operand::Immediate(Immediate::Boolean(v))),
            ast_ty,
        ),
        Ast::Char(_) => todo!(),
        Ast::String(_) => todo!(),
        Ast::Nil => todo!(),
        Ast::DefineMacro(_) => todo!(),
        Ast::Define(Define { id, init }) => {
            let inst = compile_and_add(&mut result, *init, ctx)?;
            ctx.env.insert_var(id.clone(), inst.result);
        }
        Ast::Assign(Assign {
            var,
            var_loc: _,
            value,
        }) => {
            let value = compile_and_add(&mut result, *value, ctx)?;
            ctx.env.update_var(var, &value.result)?;
        }
        Ast::IfExpr(IfExpr {
            cond,
            then_ast,
            else_ast,
        }) => {
            let cond = compile_and_add(&mut result, *cond, ctx)?;
            let then_label = ctx.gen_label();
            let else_label = ctx.gen_label();
            let end_label = ctx.gen_label();

            add_instr(
                &mut result,
                ctx,
                I::Branch {
                    cond: Operand::Variable(cond.result),
                    then_label: then_label.clone(),
                    else_label: else_label.clone(),
                },
                Type::None,
            );

            add_instr(&mut result, ctx, I::Label(then_label.clone()), Type::None);
            let then_res = compile_and_add(&mut result, *then_ast, ctx)?;
            add_instr(&mut result, ctx, I::Jump(end_label.clone()), Type::None);

            add_instr(&mut result, ctx, I::Label(else_label.clone()), Type::None);
            let else_res = if let Some(else_ast) = else_ast {
                Some(compile_and_add(&mut result, *else_ast, ctx)?)
            } else {
                None
            };
            add_instr(&mut result, ctx, I::Jump(end_label.clone()), Type::None);

            add_instr(&mut result, ctx, I::Label(end_label), Type::None);
            if let Some(else_res) = else_res {
                add_instr(
                    &mut result,
                    ctx,
                    I::Phi(vec![
                        (Operand::Variable(then_res.result), then_label),
                        (Operand::Variable(else_res.result), else_label),
                    ]),
                    ast_ty,
                );
            }
        }
        Ast::Cond(_) => todo!(),
        Ast::Let(Let {
            sequential: _,
            proc_id: _,
            inits,
            body,
        }) => {
            for (id, init) in inits {
                // sequential
                let inst = compile_and_add(&mut result, init, ctx)?;
                ctx.env.insert_var(id, inst.result);
            }

            result.append(&mut compile_asts(body, ctx)?);
        }
        Ast::Begin(_) => todo!(),
        Ast::BuildList(_) => todo!(),
        Ast::Loop(_) => todo!(),
        Ast::Continue(_) => todo!(),

        Ast::Lambda(_) => {}
    }

    Ok(result)
}

fn compile_lambdas_ast(ast: AnnotatedAst, ctx: &mut Context) -> Result<AnnotatedAst> {
    let AnnotatedAst { ast, location, ty } = ast;

    match ast {
        Ast::Lambda(Lambda { args, body }) => {
            let args = args
                .into_iter()
                .map(|arg| {
                    let name = arg.value.clone();
                    ctx.env.insert_var(arg, Variable { name: name.clone() });

                    (name, Type::None)
                })
                .collect::<Vec<_>>();

            let name = ctx
                .sym_table
                .create_symbol_value(format!("fun{}", ctx.var_gen.gen_string()));
            let label = Label {
                name: name.value.clone(),
            };

            ctx.env.push_local();

            let insts = compile_asts(body, ctx)?;

            ctx.env.pop_local();

            let fun = Function {
                name: name.value.clone(),
                args,
                body: insts,
                ty: ty.clone(),
            };

            ctx.func_env.insert_var(name.clone(), (label, fun));

            Ok(AnnotatedAst {
                ast: Ast::Symbol(name),
                location,
                ty,
            })
        }
        Ast::Let(Let {
            sequential,
            proc_id,
            inits,
            body,
        }) => {
            if let Some(proc_id) = proc_id {
                let mut aargs = Vec::new();
                let mut fargs = Vec::new();
                for (id, init) in inits {
                    ctx.env.insert_var(
                        id.clone(),
                        Variable {
                            name: id.value.clone(),
                        },
                    );
                    fargs.push((id.value, init.ty.clone()));
                    aargs.push(init);
                }

                let label = Label {
                    name: proc_id.value.clone(),
                };

                ctx.env.push_local();

                let mut fun = Function {
                    name: proc_id.value.clone(),
                    args: fargs,
                    body: Vec::new(),
                    ty: Type::None,
                };

                ctx.func_env
                    .insert_var(proc_id.clone(), (label.clone(), fun.clone()));

                let insts = compile_asts(body, ctx)?;

                ctx.env.pop_local();

                fun.body = insts;
                ctx.func_env.update_var(proc_id.clone(), &(label, fun))?;

                let mut apply = vec![Ast::Symbol(proc_id).with_null_location()];
                apply.append(&mut aargs);

                Ok(AnnotatedAst {
                    ast: Ast::List(apply),
                    location,
                    ty,
                })
            } else {
                AnnotatedAst {
                    ast: Ast::Let(Let {
                        sequential,
                        proc_id,
                        inits,
                        body,
                    }),
                    location,
                    ty,
                }
                .traverse(ctx, compile_lambdas_ast)
            }
        }
        _ => AnnotatedAst { ast, location, ty }.traverse(ctx, compile_lambdas_ast),
    }
}

fn compile_asts(asts: Vec<AnnotatedAst>, ctx: &mut Context) -> Result<Instructions> {
    let mut result = Vec::new();
    for ast in asts {
        let mut insts = compile_ast(ast, ctx)?;
        result.append(&mut insts);
    }
    Ok(result)
}

pub fn compile(asts: Program, sym_table: SymbolTable) -> Result<Functions> {
    let mut result = Vec::new();

    let mut ctx = Context {
        env: Environment::new(),
        sym_table,
        func_env: Environment::new(),
        var_gen: UniqueGenerator::new(),
    };

    let asts = asts
        .into_iter()
        .map(|ast| compile_lambdas_ast(ast, &mut ctx))
        .collect::<Result<Vec<_>>>()?;

    let fun_vars = ctx.func_env.current_local().variables.clone();
    for (_, (_, mut fun)) in fun_vars {
        let res = get_last_instr(&fun.body);
        add_instr(
            &mut fun.body,
            &mut ctx,
            Instruction::Ret(Operand::Variable(res.result)),
            Type::None,
        );

        result.push(fun);
    }

    {
        // 'main' function
        let mut body = Vec::new();

        for ast in asts {
            let mut insts = compile_ast(ast, &mut ctx)?;
            body.append(&mut insts);
        }

        let res = get_last_instr(&body);
        add_instr(
            &mut body,
            &mut ctx,
            Instruction::Ret(Operand::Variable(res.result)),
            Type::None,
        );

        result.push(Function {
            name: "main".to_string(),
            args: Vec::new(),
            body,
            ty: Type::None,
        });
    }

    Ok(result)
}
