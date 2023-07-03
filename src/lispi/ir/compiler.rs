use std::vec;

use anyhow::Result;
use id_arena::{Arena, Id};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};

use super::{
    super::{
        ast::*, environment::Environment, error::Error, evaluator as e, parser::*, typer as t,
        unique_generator::UniqueGenerator,
    },
    basic_block as bb,
    basic_block::{BasicBlock, Function, Functions},
    tag::LoopPhiFunctionSite,
    IrContext,
};
use crate::{
    bug,
    lispi::{
        cli_option::CliOption,
        ir::{
            basic_block::BasicBlockIdExtension,
            tag::{LoopPhiFunctionSiteIndex, Tag},
        },
        SymbolValue,
    },
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

    /// Map loop label to loop label and basic block.
    /// This is for calcurate back labels of Continue.
    loop_label_map: FxHashMap<String, (Label, Id<BasicBlock>)>,

    /// Map loop label to updated loop variables.
    loop_updates_map: FxHashMap<String, Vec<(AnnotatedInstr, Id<BasicBlock>)>>,
    /// Map variable to assigned variables.
    assigned_map: FxHashMap<String, (AnnotatedInstr, Id<BasicBlock>)>,

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
            var_gen: UniqueGenerator::default(),
            arena,
            basic_blocks: Vec::new(),
            loop_label_map: FxHashMap::default(),
            loop_updates_map: FxHashMap::default(),
            assigned_map: FxHashMap::default(),
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

    fn current_bb(&self) -> &BasicBlock {
        let id = *self.basic_blocks.last().unwrap();
        self.arena.get(id).unwrap()
    }

    fn current_bb_mut(&mut self) -> &mut BasicBlock {
        let id = *self.basic_blocks.last().unwrap();
        self.arena.get_mut(id).unwrap()
    }

    fn current_bb_id(&mut self) -> Id<BasicBlock> {
        *self.basic_blocks.last().unwrap()
    }

    fn push_inst(&mut self, inst: AnnotatedInstr) {
        self.current_bb_mut().push_inst(inst);
    }

    /// Get the last inserted instruction.
    /// This function must be called after inserting instructions.
    fn last_inst(&self) -> Result<AnnotatedInstr> {
        if let Some(last) = self.current_bb().insts.last() {
            Ok(last.clone())
        } else if let Some(last_bb) = self.current_bb().preceding_bb {
            let last_bb = self.arena.get(last_bb).unwrap();
            let last_inst = last_bb
                .insts
                .last()
                .cloned()
                .expect("Current and preceding BB have no instructions.");
            Ok(last_inst)
        } else {
            panic!("Current BB is at the head and has no instructions.")
        }
    }

    fn new_bb(&mut self, label: String) -> Id<BasicBlock> {
        self.arena
            .alloc(BasicBlock::new(label, self.basic_blocks.last().copied()))
    }

    fn add_bb(&mut self, bb: Id<BasicBlock>) {
        self.basic_blocks.push(bb);
    }
}

fn compile_and_add(ast: AnnotatedAst, ctx: &mut Context) -> Result<AnnotatedInstr> {
    compile_ast(ast, ctx)?;
    ctx.last_inst()
}

fn add_instr(ctx: &mut Context, inst: Instruction, ty: t::Type) -> AnnotatedInstr {
    let inst = AnnotatedInstr::new(ctx.gen_var(), inst, ty);
    ctx.push_inst(inst.clone());
    inst
}

fn add_instr_with_tags(
    ctx: &mut Context,
    inst: Instruction,
    ty: t::Type,
    tags: Vec<Tag>,
) -> AnnotatedInstr {
    let mut inst = AnnotatedInstr::new(ctx.gen_var(), inst, ty);
    inst.tags = tags;
    ctx.push_inst(inst.clone());
    inst
}

fn collect_updated_vars(asts: &[AnnotatedAst]) -> Vec<SymbolValue> {
    fn collect_updated_vars_inner(ast: &AnnotatedAst, ctx: &mut Vec<SymbolValue>) -> Result<()> {
        match &ast.ast {
            Ast::Assign(Assign { var, value, .. }) => {
                ctx.push(var.clone());
                let _ = value.traverse_ref(ctx, collect_updated_vars_inner);
            }
            _ => ast.traverse_ref(ctx, collect_updated_vars_inner)?,
        }

        Ok(())
    }

    let mut fvs = Vec::new();
    for ast in asts {
        let _ = collect_updated_vars_inner(ast, &mut fvs);
    }
    fvs
}

fn compile_apply_lambda(
    lambda_ast: AnnotatedAst,
    args: Vec<AnnotatedInstr>,
    ast_ty: t::Type,
    ctx: &mut Context,
) -> Result<()> {
    let fun = compile_and_add(lambda_ast, ctx)?;

    let args = args
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
        ctx,
        Instruction::Call {
            fun: Operand::Variable(fun.result),
            args,
        },
        ast_ty,
    );

    Ok(())
}

fn compile_apply(vs: Vec<AnnotatedAst>, ast_ty: t::Type, ctx: &mut Context) -> Result<()> {
    use Instruction as I;

    if let Some((fun_ast, args)) = vs.split_first() {
        let args = args
            .iter()
            .map(|arg| compile_and_add(arg.clone(), ctx))
            .collect::<Result<Vec<_>>>()?;

        match &fun_ast.ast {
            Ast::Symbol(fun_sym) => {
                let name = fun_sym.as_str();
                match name {
                    "+" | "-" | "*" | "/" | "=" | "<=" | "<" | ">" | "or" | "<<" | ">>" => {
                        let left = args[0].result.clone();
                        let right = args[1].result.clone();

                        let left = Operand::Variable(left);
                        let right = Operand::Variable(right);

                        let inst = match name {
                            "+" => I::Add(left, right),
                            "-" => I::Sub(left, right),
                            "*" => I::Mul(left, right),
                            "/" => I::Div(left, right),
                            "=" => I::Cmp(CmpOperator::Eq, left, right),
                            "<=" => I::Cmp(CmpOperator::SGE, left, right),
                            ">" => I::Cmp(CmpOperator::SGT, left, right),
                            "<" => I::Cmp(CmpOperator::SLT, left, right),
                            "or" => I::Or(left, right),
                            "<<" => I::Shift(ShiftOperator::LogicalLeft, left, right),
                            ">>" => I::Shift(ShiftOperator::LogicalRight, left, right),
                            _ => return Err(bug!()),
                        };
                        add_instr(ctx, inst, ast_ty);
                    }
                    "io-write" => {
                        add_instr(
                            ctx,
                            I::Store(args[0].result.clone().into(), args[1].result.clone().into()),
                            ast_ty,
                        );
                    }
                    "array->get" => {
                        let ary = args[0].result.clone().into();
                        let index = args[1].result.clone().into();

                        let index = add_instr(ctx, I::Add(index, 1.into()), t::Type::None)
                            .result
                            .into();

                        add_instr(
                            ctx,
                            I::LoadElement {
                                addr: ary,
                                ty: Type::I32,
                                index,
                            },
                            ast_ty,
                        );
                    }
                    "array->set" => {
                        let ary = args[0].result.clone().into();
                        let index = args[1].result.clone().into();
                        let value = args[2].result.clone().into();

                        let index = add_instr(ctx, I::Add(index, 1.into()), t::Type::None)
                            .result
                            .into();

                        add_instr(
                            ctx,
                            I::StoreElement {
                                addr: ary,
                                ty: Type::I32,
                                index,
                                value,
                            },
                            ast_ty,
                        );
                    }
                    "array->len" => {
                        let ary = args[0].result.clone().into();
                        add_instr(
                            ctx,
                            I::LoadElement {
                                addr: ary,
                                ty: Type::I32,
                                index: 0.into(),
                            },
                            ast_ty,
                        );
                    }
                    "not" => {
                        let value = args[0].result.clone();
                        add_instr(ctx, I::Not(Operand::Variable(value)), ast_ty);
                    }
                    _ => compile_apply_lambda(fun_ast.clone(), args, ast_ty, ctx)?,
                }
                Ok(())
            }
            Ast::Lambda(_) => compile_apply_lambda(fun_ast.clone(), args, ast_ty, ctx),
            _ => Err(unimplemented!()),
        }
    } else {
        Err(unimplemented!())
    }
}

fn compile_lambda(
    name: String,
    args: Vec<String>,
    body: Vec<AnnotatedAst>,
    ast_ty: t::Type,
    ctx: &mut Context,
) -> Result<()> {
    let label = Label { name: name.clone() };

    let mut free_vars = collect_free_vars(&body, args.clone());
    for id in ctx.preludes.current_local().variables.keys() {
        free_vars.remove(id);
    }
    let free_vars = free_vars.into_iter().collect::<Vec<_>>();

    let args = args
        .into_iter()
        .map(|arg| (arg, t::Type::None))
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
        ast_ty,
        ctx.basic_blocks.drain(0..).collect(),
    );

    ctx.basic_blocks.append(&mut old_bbs);

    ctx.funcs.insert_var(name, fun);

    Ok(())
}

fn compile_ast(ast: AnnotatedAst, ctx: &mut Context) -> Result<()> {
    use Instruction as I;

    let AnnotatedAst {
        ast,
        location: _,
        ty: ast_ty,
    } = ast;

    match ast {
        Ast::List(vs) => compile_apply(vs, ast_ty, ctx)?,
        Ast::Quoted(_) => todo!(),
        Ast::Integer(v) => {
            add_instr(
                ctx,
                I::Operand(Operand::Immediate(Immediate::Integer(v))),
                ast_ty,
            );
        }
        Ast::Float(_) => todo!(),
        Ast::Symbol(sym) => {
            if let Some(label) = ctx.func_labels.find_var(&sym) {
                add_instr(
                    ctx,
                    I::Operand(Operand::Immediate(Immediate::Label(label))),
                    ast_ty,
                );
            } else if let Some(var) = ctx.env.find_var(&sym) {
                add_instr(ctx, I::Operand(Operand::Variable(var)), ast_ty);
            } else {
                return Err(Error::UndefinedVariable(sym, "compiling")
                    .with_null_location()
                    .into());
            }
        }
        Ast::SymbolWithType(_, _) => todo!(),
        Ast::Boolean(v) => {
            add_instr(
                ctx,
                I::Operand(Operand::Immediate(Immediate::Boolean(v))),
                ast_ty,
            );
        }
        Ast::Char(v) => {
            add_instr(ctx, I::Operand((v as i32).into()), ast_ty);
        }
        Ast::String(_) => todo!(),
        Ast::Nil => todo!(),
        Ast::Include(_) => todo!(),
        Ast::DefineMacro(_) => {
            // Do nothing
        }
        Ast::Define(Define { id, init }) => {
            let inst = compile_and_add(*init, ctx)?;

            // If inst was a Function here, register the id and FV as a pair to fun_fvs.
            // Get the required FV from fun_fvs at Call time and pass the FV in addition to the argument
            if let AnnotatedInstr {
                inst: I::Operand(Operand::Immediate(Immediate::Label(fname))),
                ty: t::Type::Function { .. },
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
            let value = compile_and_add(*value, ctx)?;
            ctx.env.update_var(var.clone(), &value.result)?;

            let bb = ctx.current_bb_id();
            ctx.assigned_map.insert(var, (value, bb));
        }
        Ast::IfExpr(IfExpr {
            cond,
            then_ast,
            else_ast,
        }) => {
            let cond = compile_and_add(*cond, ctx)?;
            let then_label = ctx.gen_label();
            let else_label = ctx.gen_label();
            let end_label = ctx.gen_label();

            let then_bb = ctx.new_bb(then_label.name.clone());
            let else_bb = ctx.new_bb(else_label.name.clone());

            add_instr(
                ctx,
                I::Branch {
                    cond: Operand::Variable(cond.result),
                    then_label: then_label.clone(),
                    else_label: else_label.clone(),
                    then_bb,
                    else_bb,
                },
                t::Type::None,
            );

            let end_bb = ctx.new_bb(end_label.name.clone());

            ctx.add_bb(then_bb);
            let then_res = compile_and_add(*then_ast, ctx)?;
            add_instr(ctx, I::Jump(end_label.clone(), end_bb), t::Type::None);

            ctx.add_bb(else_bb);
            let else_res = if let Some(else_ast) = else_ast {
                Some(compile_and_add(*else_ast, ctx)?)
            } else {
                None
            };
            add_instr(ctx, I::Jump(end_label, end_bb), t::Type::None);

            ctx.add_bb(end_bb);
            if let Some(else_res) = else_res {
                add_instr(
                    ctx,
                    I::Phi(vec![
                        (Operand::Variable(then_res.result), then_label),
                        (Operand::Variable(else_res.result), else_label),
                    ]),
                    ast_ty,
                );
            } else {
                add_instr(ctx, I::Operand(Operand::Variable(then_res.result)), ast_ty);
            }
        }
        Ast::As(expr, _) => {
            compile_and_add(*expr, ctx)?;
        }
        Ast::Cond(_) => todo!(),
        Ast::Let(Let {
            sequential,
            proc_id,
            inits,
            body,
        }) => {
            if let Some(proc_id) = proc_id {
                // Define the body as a function
                ctx.env.insert_var(
                    proc_id.clone(),
                    Variable {
                        name: proc_id.clone(),
                    },
                );
                let (lambda_args, passed_args): (Vec<_>, Vec<_>) = inits.into_iter().unzip();
                // TODO: Set the type
                let lambda_ty = t::Type::None;
                compile_lambda(proc_id.clone(), lambda_args, body, lambda_ty.clone(), ctx)?;

                let lambda = ctx.funcs.find_var(&proc_id).unwrap();
                let mut free_vars = lambda.free_vars;
                free_vars.push(proc_id.clone());
                ctx.func_fvs.insert_var(proc_id.clone(), free_vars);

                // This is needed for constants folding.
                let lambda_label = Operand::Immediate(Immediate::Label(Label {
                    name: proc_id.clone(),
                }));
                ctx.push_inst(AnnotatedInstr::new(
                    Variable {
                        name: proc_id.clone(),
                    },
                    I::Operand(lambda_label.clone()),
                    lambda_ty,
                ));

                // Call it with initial values and its function name
                let passed_args = passed_args
                    .into_iter()
                    .map(|arg| Ok(Operand::Variable(compile_and_add(arg, ctx)?.result)))
                    .collect::<Result<Vec<_>>>()?;
                add_instr(
                    ctx,
                    Instruction::Call {
                        fun: lambda_label,
                        args: passed_args,
                    },
                    ast_ty,
                );
            } else {
                ctx.env.push_local();

                if sequential {
                    for (id, init) in inits {
                        let inst = compile_and_add(init, ctx)?;
                        ctx.env.insert_var(id, inst.result);
                    }
                } else {
                    return Err(unimplemented!());
                }

                compile_asts(body, ctx)?;

                ctx.env.pop_local();
            }
        }
        Ast::Begin(Begin { body }) => {
            for inst in body {
                compile_and_add(inst, ctx)?;
            }
        }
        Ast::ListLiteral(_) => todo!(),
        Ast::ArrayLiteral(vs) => {
            let ary = Operand::Variable(
                add_instr(
                    ctx,
                    I::Alloca {
                        ty: Type::I32,
                        count: (vs.len() as i32 + 1).into(),
                    },
                    ast_ty.clone(),
                )
                .result,
            );

            let len = add_instr(ctx, I::Operand((vs.len() as i32).into()), t::Type::Nil).result;

            add_instr(
                ctx,
                I::StoreElement {
                    addr: ary.clone(),
                    ty: Type::I32, // TODO: Set the element type
                    index: 0.into(),
                    value: len.into(),
                },
                t::Type::Nil,
            );

            for (idx, v) in vs.into_iter().enumerate() {
                let value = Operand::Variable(compile_and_add(v, ctx)?.result);
                add_instr(
                    ctx,
                    I::StoreElement {
                        addr: ary.clone(),
                        ty: Type::I32, // TODO: Set the element type
                        index: (idx as i32 + 1).into(),
                        value,
                    },
                    t::Type::Nil,
                );
            }

            add_instr(ctx, I::Operand(ary), ast_ty);
        }
        Ast::Loop(Loop { inits, label, body }) => {
            ctx.loop_updates_map.insert(label.clone(), Vec::new());

            let header_label = ctx.gen_label();
            let header_bb = ctx.new_bb(header_label.name.clone());
            ctx.add_bb(header_bb);

            let mut init_vars = Vec::new();
            for (_id, value) in &inits {
                let inst = compile_and_add(value.clone(), ctx)?;
                init_vars.push(inst.clone());
            }

            let loop_label = ctx.gen_label();
            let end_label = ctx.gen_label();

            let loop_bb = ctx.new_bb(loop_label.name.clone());
            let end_bb = ctx.new_bb(end_label.name);

            ctx.add_bb(loop_bb);

            let binds = inits.iter().map(|(id, _)| id.clone()).collect_vec();

            for (index, ((id, _value), init)) in inits.into_iter().zip(init_vars).enumerate() {
                let inst = add_instr_with_tags(
                    ctx,
                    Instruction::Operand(Operand::Variable(init.result)),
                    init.ty,
                    vec![Tag::LoopPhiFunctionSite(LoopPhiFunctionSite {
                        label: label.clone(),
                        index: LoopPhiFunctionSiteIndex::Loop(index),
                        header_label: header_label.clone(),
                    })],
                );
                ctx.env.insert_var(id, inst.result);
            }

            let updated_vars = FxHashSet::from_iter(collect_updated_vars(&body));
            let free_vars = FxHashSet::from_iter(collect_free_vars(&body, binds));
            let updated_free_vars = updated_vars.intersection(&free_vars);
            for fv_id in updated_free_vars {
                let fv = ctx.env.find_var(fv_id).unwrap();
                let inst = add_instr_with_tags(
                    ctx,
                    Instruction::Operand(Operand::Variable(fv.clone())),
                    t::Type::None,
                    vec![Tag::LoopPhiFunctionSite(LoopPhiFunctionSite {
                        label: label.clone(),
                        index: LoopPhiFunctionSiteIndex::FreeVar(Variable {
                            name: fv_id.clone(),
                        }),
                        header_label: header_label.clone(),
                    })],
                );
                ctx.env.insert_var(fv_id.clone(), inst.result);
            }

            ctx.loop_label_map.insert(label, (loop_label, loop_bb));

            for inst in body {
                compile_and_add(inst, ctx)?;
            }

            ctx.add_bb(end_bb);
        }
        Ast::Continue(Continue { label, updates }) => {
            let (loop_label, loop_bb) = ctx.loop_label_map.get(&label).unwrap().clone();

            let updated_vars = updates
                .into_iter()
                .map(|update| Ok((compile_and_add(update, ctx)?, ctx.current_bb_id())))
                .collect::<Result<Vec<_>>>()?;
            ctx.loop_updates_map.insert(label, updated_vars);

            add_instr(ctx, I::Jump(loop_label, loop_bb), t::Type::None);

            let label = ctx.gen_label();
            let bb = ctx.new_bb(label.name);
            ctx.add_bb(bb);
        }

        Ast::Lambda(Lambda {
            args,
            arg_types: _,
            body,
        }) => {
            let name = format!("fun{}", ctx.var_gen.gen_string());
            compile_lambda(name.clone(), args, body, ast_ty.clone(), ctx)?;

            add_instr(
                ctx,
                I::Operand(Operand::Immediate(Immediate::Label(Label { name }))),
                ast_ty,
            );
        }
    }

    Ok(())
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

fn compile_asts(asts: Vec<AnnotatedAst>, ctx: &mut Context) -> Result<()> {
    for ast in asts {
        compile_ast(ast, ctx)?;
    }
    Ok(())
}

fn compile_main_function(
    asts: Program,
    result: &mut Vec<Function>,
    main_bb: Id<BasicBlock>,
    ctx: &mut Context,
) -> Result<()> {
    ctx.basic_blocks.clear();
    ctx.add_bb(main_bb);

    for ast in asts {
        compile_ast(ast, ctx)?;
    }

    let res = ctx.last_inst()?;
    add_instr(
        ctx,
        Instruction::Ret(Operand::Variable(res.result)),
        t::Type::None,
    );

    result.push(Function::new(
        "main".to_string(),
        Vec::new(),
        Vec::new(),
        t::Type::None,
        ctx.basic_blocks.drain(0..).collect(),
    ));

    Ok(())
}

/// Insert phi nodes beginning of the loops
fn insert_phi_nodes_for_loops(funcs: Functions, ctx: &mut Context) -> Functions {
    // Moving is necessary because ctx is used in the following closure.
    let loop_updates_map: FxHashMap<_, _> = ctx.loop_updates_map.drain().collect();
    let assigned_map: FxHashMap<_, _> = ctx.assigned_map.drain().collect();

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
                for bb_id in &basic_blocks {
                    let bb = ctx.arena.get(*bb_id).unwrap();

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

                                    let (update, loop_bb_id) = match &tag.index {
                                        LoopPhiFunctionSiteIndex::Loop(index) => {
                                            loop_updates_map[&tag.label][*index].clone()
                                        }
                                        LoopPhiFunctionSiteIndex::FreeVar(var) => {
                                            assigned_map[&var.name].clone()
                                        }
                                    };

                                    let loop_bb = ctx.arena.get(loop_bb_id).unwrap();

                                    let cur_label = bb.label.clone();
                                    let mut last_updated_label = &"".to_string();
                                    if cur_label == loop_bb.label {
                                        for dest_bb in &loop_bb.destination_bbs {
                                            let found = dest_bb.find_forward(ctx.arena, |bb| {
                                                if bb.label != cur_label {
                                                    last_updated_label = &bb.label;
                                                    false
                                                } else {
                                                    true
                                                }
                                            });
                                            if found.is_some() {
                                                break;
                                            }
                                        }
                                    } else {
                                        loop_bb_id.find_forward(ctx.arena, |bb| {
                                            if bb.label != cur_label {
                                                last_updated_label = &bb.label;
                                                false
                                            } else {
                                                true
                                            }
                                        });
                                    }
                                    assert_ne!(last_updated_label, "");

                                    Instruction::Phi(vec![
                                        (Operand::Variable(init), tag.header_label.to_owned()),
                                        // TODO: Add ALL incoming basic blocks
                                        (
                                            Operand::Variable(update.result.clone()),
                                            Label {
                                                name: last_updated_label.clone(),
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

                    let bb = ctx.arena.get_mut(*bb_id).unwrap();
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

pub fn compile(asts: Program, ir_ctx: &mut IrContext, _opt: &CliOption) -> Result<Functions> {
    let mut result = Vec::new();

    let main_bb = ir_ctx
        .bb_arena
        .alloc(BasicBlock::new("main".to_string(), None));

    let mut ctx = Context::new(&mut ir_ctx.bb_arena);

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
                t::Type::None,
            );
            ctx.arena
                .get_mut(*fun.basic_blocks.last().unwrap())
                .unwrap()
                .push_inst(inst);
            result.push(fun);
        }
    }

    bb::build_connections_between_bbs(ctx.arena, &result);

    let result = insert_phi_nodes_for_loops(result, &mut ctx);

    Ok(result)
}
