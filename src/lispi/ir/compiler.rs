use std::vec;

use anyhow::Result;
use id_arena::{Arena, Id};
use rustc_hash::FxHashMap;

use super::{
    super::{
        ast::*, environment::Environment, error::Error, evaluator as e, parser::*, typer::Type,
        unique_generator::UniqueGenerator,
    },
    basic_block::BasicBlock,
    tag::LoopPhiFunctionSite,
    IrContext,
};
use crate::{
    bug,
    lispi::{ir::tag::Tag, SymbolValue},
    unimplemented,
};

use super::instruction::*;

struct Context<'a> {
    env: Environment<Variable>,

    /// Pre-defined global functions
    preludes: Environment<e::Value>,

    /// Used to reference functions
    /// TODO: This can be removed.
    func_labels: Environment<Label>,
    /// Used to list functions
    funcs: Environment<Function>,

    /// Free variables of a function
    func_fvs: Environment<Vec<SymbolValue>>,

    var_gen: UniqueGenerator,

    /// Map loop label to loop label and basic block
    loop_label_map: FxHashMap<String, (Label, Id<BasicBlock>)>,

    /// TODO: Remove this
    loop_inits_map: FxHashMap<String, Vec<AnnotatedInstr>>,
    loop_updates_map: FxHashMap<String, Vec<(AnnotatedInstr, String)>>,

    /// Arena for Function
    arena: &'a mut Arena<BasicBlock>,

    basic_blocks: Vec<Id<BasicBlock>>,
}

impl<'a> Context<'a> {
    fn new(arena: &'a mut Arena<BasicBlock>) -> Self {
        let mut preludes = e::Env::default();
        e::init_env(&mut preludes, &mut Environment::default());

        let mut func_fvs = Environment::default();
        func_fvs.push_local();

        Self {
            env: Environment::default(),
            preludes,
            func_labels: Environment::default(),
            funcs: Environment::default(),
            func_fvs,
            var_gen: UniqueGenerator::new(),
            arena,
            basic_blocks: Vec::new(),
            loop_label_map: FxHashMap::default(),
            loop_inits_map: FxHashMap::default(),
            loop_updates_map: FxHashMap::default(),
        }
    }

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

    fn current_bb(&mut self) -> &mut BasicBlock {
        let id = *self.basic_blocks.last().unwrap();
        self.arena.get_mut(id).unwrap()
    }

    fn push_inst(&mut self, inst: AnnotatedInstr) {
        self.current_bb().push_inst(inst);
    }

    fn new_bb(&mut self, label: String) -> Id<BasicBlock> {
        self.arena.alloc(BasicBlock::new(label))
    }

    fn add_bb(&mut self, bb: Id<BasicBlock>) {
        self.basic_blocks.push(bb);
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
    let inst = ctx.current_bb().insts.last().unwrap().clone();
    result.append(&mut insts);
    Ok(inst)
}

fn add_instr(
    result: &mut Vec<AnnotatedInstr>,
    ctx: &mut Context,
    inst: Instruction,
    ty: Type,
) -> AnnotatedInstr {
    let inst = AnnotatedInstr::new(ctx.gen_var(), inst, ty);
    result.push(inst.clone());
    ctx.push_inst(inst.clone());
    inst
}

fn add_instr_with_tags(
    result: &mut Vec<AnnotatedInstr>,
    ctx: &mut Context,
    inst: Instruction,
    ty: Type,
    tags: Vec<Tag>,
) -> AnnotatedInstr {
    let mut inst = AnnotatedInstr::new(ctx.gen_var(), inst, ty);
    inst.tags = tags;
    result.push(inst.clone());
    ctx.push_inst(inst.clone());
    inst
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
                    ast: Ast::Symbol(fun_sym),
                    ..
                } = fun_ast
                {
                    let name = fun_sym.as_str();
                    match name {
                        "+" | "-" | "*" | "<=" | "<" | ">" | "or" | "<<" | ">>" => {
                            let left = args[0].result.clone();
                            let right = args[1].result.clone();

                            let left = Operand::Variable(left);
                            let right = Operand::Variable(right);

                            let inst = match name {
                                "+" => I::Add(left, right),
                                "-" => I::Sub(left, right),
                                "*" => I::Mul(left, right),
                                "<=" => I::Cmp(CmpOperator::SGE, left, right),
                                "<" => I::Cmp(CmpOperator::SGT, left, right),
                                ">" => I::Cmp(CmpOperator::SLT, left, right),
                                "or" => I::Or(left, right),
                                "<<" => I::Shift(ShiftOperator::LogicalLeft, left, right),
                                ">>" => I::Shift(ShiftOperator::LogicalRight, left, right),
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
                        "not" => {
                            let value = args[0].result.clone();
                            add_instr(&mut result, ctx, I::Not(Operand::Variable(value)), ast_ty);
                        }
                        _ => {
                            let fun = compile_and_add(&mut result, fun_ast.clone(), ctx)?;

                            let mut args = args
                                .into_iter()
                                .map(|arg| Operand::Variable(arg.result))
                                .collect::<Vec<_>>();

                            // if let Some(func_fv) = ctx.func_fvs.find_var(fun_sym) {
                            //     for fv in func_fv {
                            //         // TODO: We should find the variable fv from the context which called function is 'defined'.
                            //         // However we find it from the context which the function is 'called'.
                            //         if let Some(fv) = ctx.env.find_var(&fv) {
                            //             args.push(Operand::Variable(fv));
                            //         }
                            //     }
                            // }

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
        Ast::Integer(v) => {
            add_instr(
                &mut result,
                ctx,
                I::Operand(Operand::Immediate(Immediate::Integer(v))),
                ast_ty,
            );
        }
        Ast::Float(_) => todo!(),
        Ast::Symbol(sym) => {
            if let Some(label) = ctx.func_labels.find_var(&sym) {
                add_instr(
                    &mut result,
                    ctx,
                    I::Operand(Operand::Immediate(Immediate::Label(label))),
                    ast_ty,
                );
            } else if let Some(var) = ctx.env.find_var(&sym) {
                add_instr(&mut result, ctx, I::Operand(Operand::Variable(var)), ast_ty);
            } else {
                return Err(Error::UndefinedVariable(sym, "compiling")
                    .with_null_location()
                    .into());
            }
        }
        Ast::SymbolWithType(_, _) => todo!(),
        Ast::Boolean(v) => {
            add_instr(
                &mut result,
                ctx,
                I::Operand(Operand::Immediate(Immediate::Boolean(v))),
                ast_ty,
            );
        }
        Ast::Char(_) => todo!(),
        Ast::String(_) => todo!(),
        Ast::Nil => todo!(),
        Ast::DefineMacro(_) => todo!(),
        Ast::Define(Define { id, init }) => {
            let inst = compile_and_add(&mut result, *init, ctx)?;

            // If inst was a Function here, register the id and FV as a pair to fun_fvs.
            // Get the required FV from fun_fvs at Call time and pass the FV in addition to the argument
            if let AnnotatedInstr {
                inst: I::Operand(Operand::Immediate(Immediate::Label(fname))),
                ty: Type::Function { .. },
                ..
            } = inst
            {
                let fname = fname.name;
                let fun = ctx.funcs.find_var(&fname);
                if let Some(fun) = fun {
                    ctx.func_fvs.insert_var(id.clone(), fun.free_vars);
                }
            }

            ctx.env.insert_var(id, inst.result);
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

            let then_bb = ctx.new_bb(then_label.name.clone());
            let else_bb = ctx.new_bb(else_label.name.clone());

            add_instr(
                &mut result,
                ctx,
                I::Branch {
                    cond: Operand::Variable(cond.result),
                    then_label: then_label.clone(),
                    else_label: else_label.clone(),
                    then_bb,
                    else_bb,
                },
                Type::None,
            );

            let end_bb = ctx.new_bb(end_label.name.clone());

            ctx.add_bb(then_bb);
            let then_res = compile_and_add(&mut result, *then_ast, ctx)?;
            add_instr(
                &mut result,
                ctx,
                I::Jump(end_label.clone(), end_bb),
                Type::None,
            );

            ctx.add_bb(else_bb);
            let else_res = if let Some(else_ast) = else_ast {
                Some(compile_and_add(&mut result, *else_ast, ctx)?)
            } else {
                None
            };
            add_instr(&mut result, ctx, I::Jump(end_label, end_bb), Type::None);

            ctx.add_bb(end_bb);
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
            } else {
                add_instr(
                    &mut result,
                    ctx,
                    I::Operand(Operand::Variable(then_res.result)),
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
        Ast::Begin(Begin { body }) => {
            for inst in body {
                compile_and_add(&mut result, inst, ctx)?;
            }
        }
        Ast::BuildList(_) => todo!(),
        Ast::Loop(Loop { inits, label, body }) => {
            ctx.loop_inits_map.insert(label.clone(), Vec::new());
            ctx.loop_updates_map.insert(label.clone(), Vec::new());

            let header_label = ctx.gen_label();
            let header_bb = ctx.new_bb(header_label.name.clone());
            ctx.add_bb(header_bb);

            let mut init_vars = Vec::new();
            for (_id, value) in &inits {
                let inst = compile_and_add(&mut result, value.clone(), ctx)?;
                ctx.loop_inits_map
                    .get_mut(&label)
                    .unwrap()
                    .push(inst.clone());
                init_vars.push(inst.clone());
            }

            let loop_label = ctx.gen_label();
            let end_label = ctx.gen_label();

            let loop_bb = ctx.new_bb(loop_label.name.clone());
            let end_bb = ctx.new_bb(end_label.name);

            ctx.add_bb(loop_bb);

            for (index, ((id, _value), init)) in inits.into_iter().zip(init_vars).enumerate() {
                let inst = add_instr_with_tags(
                    &mut result,
                    ctx,
                    Instruction::Operand(Operand::Variable(init.result)),
                    init.ty,
                    vec![Tag::LoopPhiFunctionSite(LoopPhiFunctionSite {
                        label: label.clone(),
                        index,
                        header_label: header_label.clone(),
                        loop_label: loop_label.clone(), // TODO: Use the label updating vars instead of loop_label
                    })],
                );
                ctx.env.insert_var(id, inst.result);
            }

            ctx.loop_label_map
                .insert(label.clone(), (loop_label, loop_bb));

            for inst in body {
                compile_and_add(&mut result, inst, ctx)?;
            }

            ctx.add_bb(end_bb);
        }
        Ast::Continue(Continue { label, updates }) => {
            let (loop_label, loop_bb) = ctx.loop_label_map.get(&label).unwrap().clone();

            let updated_vars = updates
                .into_iter()
                .map(|update| {
                    Ok((
                        compile_and_add(&mut result, update, ctx)?,
                        ctx.current_bb().label.to_owned(),
                    ))
                })
                .collect::<Result<Vec<_>>>()?;
            ctx.loop_updates_map.insert(label, updated_vars);

            add_instr(&mut result, ctx, I::Jump(loop_label, loop_bb), Type::None);
        }

        Ast::Lambda(Lambda {
            args,
            arg_types: _,
            body,
        }) => {
            let name = format!("fun{}", ctx.var_gen.gen_string());
            let label = Label { name: name.clone() };

            let mut free_vars = collect_free_vars(&body, args.clone());
            for id in ctx.preludes.current_local().variables.keys() {
                free_vars.remove(id);
            }
            let free_vars = free_vars.into_iter().collect::<Vec<_>>();

            let args = args
                .into_iter()
                .map(|arg| (arg, Type::None))
                .collect::<Vec<_>>();

            let bb = ctx.new_bb(label.name);

            let mut old_bbs = ctx.basic_blocks.drain(0..).collect();

            ctx.env.push_local();

            for (arg, _) in &args {
                ctx.env
                    .insert_var(arg.clone(), Variable { name: arg.clone() });
            }

            // for fv in &free_vars {
            //     ctx.env
            //         .insert_var(fv.clone(), Variable { name: fv.clone() });
            // }

            ctx.add_bb(bb);
            compile_asts(body, ctx)?;
            ctx.env.pop_local();

            let fun = Function::new(
                name.clone(),
                args,
                free_vars,
                ast_ty.clone(),
                ctx.basic_blocks.drain(0..).collect(),
            );

            ctx.basic_blocks.append(&mut old_bbs);

            ctx.funcs.insert_var(name.clone(), fun);

            add_instr(
                &mut result,
                ctx,
                I::Operand(Operand::Immediate(Immediate::Label(Label { name }))),
                ast_ty,
            );
        }
    }

    Ok(result)
}

// fn compile_lambdas_ast(ast: AnnotatedAst, ctx: &mut Context) -> Result<AnnotatedAst> {
//     let AnnotatedAst { ast, location, ty } = ast;

//     match ast {
//         Ast::Let(Let {
//             sequential,
//             proc_id,
//             inits,
//             body,
//         }) => {
//             if let Some(proc_id) = proc_id {
//                 let label = Label {
//                     name: proc_id.value.clone(),
//                 };

//                 let mut aargs = Vec::new();
//                 let mut fargs = Vec::new();
//                 for (id, init) in inits {
//                     ctx.env.insert_var(
//                         id.clone(),
//                         Variable {
//                             name: id.value.clone(),
//                         },
//                     );
//                     fargs.push((id.value, init.ty.clone()));
//                     aargs.push(init);
//                 }

//                 ctx.env.push_local();

//                 let bb = ctx.new_bb(label.name.clone());

//                 ctx.basic_blocks.clear();
//                 ctx.add_bb(bb);

//                 // ctx.func_labels.insert_var(proc_id.clone(), label);

//                 // let insts = compile_asts(body, ctx)?;

//                 let fun = Function::new(
//                     proc_id.value.clone(),
//                     fargs,
//                     Type::None,
//                     ctx.basic_blocks.drain(0..).collect(),
//                 );

//                 ctx.env.pop_local();

//                 ctx.funcs.insert_var(proc_id.clone(), fun);

//                 let mut apply = vec![Ast::Symbol(proc_id).with_null_location()];
//                 apply.append(&mut aargs);

//                 Ok(AnnotatedAst {
//                     ast: Ast::List(apply),
//                     location,
//                     ty,
//                 })
//             } else {
//                 AnnotatedAst {
//                     ast: Ast::Let(Let {
//                         sequential,
//                         proc_id,
//                         inits,
//                         body,
//                     }),
//                     location,
//                     ty,
//                 }
//                 .traverse(ctx, compile_lambdas_ast)
//             }
//         }
//         _ => AnnotatedAst { ast, location, ty }.traverse(ctx, compile_lambdas_ast),
//     }
// }

fn compile_asts(asts: Vec<AnnotatedAst>, ctx: &mut Context) -> Result<Instructions> {
    let mut result = Vec::new();
    for ast in asts {
        let mut insts = compile_ast(ast, ctx)?;
        result.append(&mut insts);
    }
    Ok(result)
}

fn compile_main_function(
    asts: Program,
    result: &mut Vec<Function>,
    main_bb: Id<BasicBlock>,
    ctx: &mut Context,
) -> Result<()> {
    let mut body = Vec::new();

    ctx.basic_blocks.clear();
    ctx.add_bb(main_bb);

    for ast in asts {
        let mut insts = compile_ast(ast, ctx)?;
        body.append(&mut insts);
    }

    let res = get_last_instr(&body);
    add_instr(
        &mut body,
        ctx,
        Instruction::Ret(Operand::Variable(res.result)),
        Type::None,
    );

    result.push(Function::new(
        "main".to_string(),
        Vec::new(),
        Vec::new(),
        Type::None,
        ctx.basic_blocks.drain(0..).collect(),
    ));

    Ok(())
}

/// Insert phi nodes beginning of the loops
fn insert_phi_nodes_for_loops(funcs: Functions, ctx: &mut Context) -> Functions {
    // Moving is necessary because ctx is used in the following closure.
    let loop_updates_map: FxHashMap<String, Vec<(AnnotatedInstr, String)>> =
        ctx.loop_updates_map.drain().collect();

    funcs
        .into_iter()
        .map(
            |Function {
                 name,
                 args,
                 free_vars,
                 ty,
                 basic_blocks,
             }| {
                for bb in &basic_blocks {
                    let bb = ctx.arena.get_mut(*bb).unwrap();

                    let mut result = Vec::new();

                    for AnnotatedInstr {
                        result: var,
                        inst,
                        ty,
                        tags,
                    } in bb.insts.clone()
                    {
                        let inst = match inst {
                            Instruction::Operand(Operand::Variable(init)) => {
                                let tag = tags.iter().find_map(|tag| {
                                    if let Tag::LoopPhiFunctionSite(tag) = tag {
                                        Some(tag)
                                    } else {
                                        None
                                    }
                                });

                                if let Some(tag) = tag {
                                    // Translate
                                    // %var = %init
                                    // to
                                    // %var = phi [%init, header_label], [%update, loop_label]
                                    // Variable %update is taken from ctx.loop_updates_map

                                    let (update, loop_label) =
                                        loop_updates_map[&tag.label][tag.index].clone();
                                    Instruction::Phi(vec![
                                        (Operand::Variable(init), tag.header_label.to_owned()),
                                        (
                                            Operand::Variable(update.result.clone()),
                                            Label {
                                                name: loop_label.clone(),
                                            },
                                        ),
                                    ])
                                } else {
                                    Instruction::Operand(Operand::Variable(init))
                                }
                            }
                            _ => inst,
                        };

                        result.push(AnnotatedInstr {
                            result: var,
                            inst,
                            ty,
                            tags,
                        })
                    }

                    bb.insts = result;
                }

                Function {
                    name,
                    args,
                    free_vars,
                    ty,
                    basic_blocks,
                }
            },
        )
        .collect()
}

pub fn compile(asts: Program, ir_ctx: &mut IrContext) -> Result<Functions> {
    let mut result = Vec::new();

    let main_bb = ir_ctx.bb_arena.alloc(BasicBlock::new("main".to_string()));

    let mut ctx = Context::new(&mut ir_ctx.bb_arena);

    // let asts = asts
    //     .into_iter()
    //     .map(|ast| compile_lambdas_ast(ast, &mut ctx))
    //     .collect::<Result<Vec<_>>>()?;

    compile_main_function(asts, &mut result, main_bb, &mut ctx)?;

    let fun_vars = ctx.funcs.current_local().variables.clone();
    for (_, fun) in fun_vars {
        let last_bb = fun.basic_blocks.iter().rev().find_map(|bb| {
            let bb = ctx.arena.get(*bb).unwrap();
            if !bb.insts.is_empty() {
                Some(bb)
            } else {
                None
            }
        });

        if let Some(last_bb) = last_bb {
            let res = last_bb.insts.last().unwrap().clone();

            let inst = AnnotatedInstr::new(
                ctx.gen_var(),
                Instruction::Ret(Operand::Variable(res.result)),
                Type::None,
            );
            ctx.arena
                .get_mut(*fun.basic_blocks.last().unwrap())
                .unwrap()
                .push_inst(inst);
            result.push(fun);
        }
    }

    let result = insert_phi_nodes_for_loops(result, &mut ctx);

    Ok(result)
}
