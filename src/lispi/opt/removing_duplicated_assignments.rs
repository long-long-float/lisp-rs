use anyhow::Result;
use rustc_hash::FxHashMap;

use crate::lispi::ir::IrContext;

use super::super::ir::instruction::*;

use Instruction as I;

struct Context {
    assign_var_map: FxHashMap<Variable, Variable>,
    assign_imm_map: FxHashMap<Immediate, Variable>,

    replace_var_map: FxHashMap<Variable, Variable>,
}

fn remove_duplicated_assignments(fun: &Function, ir_ctx: &mut IrContext) -> Result<()> {
    fn replace_var(ctx: &Context, op: Operand) -> Operand {
        match op {
            Operand::Variable(ref var) => {
                if let Some(replaced_op) = ctx.replace_var_map.get(var) {
                    Operand::Variable(replaced_op.clone())
                } else {
                    op
                }
            }
            _ => op,
        }
    }

    let mut ctx = Context {
        assign_imm_map: FxHashMap::default(),
        assign_var_map: FxHashMap::default(),

        replace_var_map: FxHashMap::default(),
    };

    // Create var/imm and var mapping

    for bb in &fun.basic_blocks {
        let bb = ir_ctx.bb_arena.get_mut(*bb).unwrap();

        for AnnotatedInstr {
            result: result_var,
            inst,
            ty: _,
        } in &bb.insts
        {
            match inst {
                I::Operand(Operand::Variable(var)) => {
                    if let Some(rvar) = ctx.assign_var_map.get(var) {
                        ctx.replace_var_map.insert(result_var.clone(), rvar.clone());
                    } else {
                        ctx.assign_var_map.insert(var.clone(), result_var.clone());
                    }
                }
                I::Operand(Operand::Immediate(imm)) => {
                    if let Some(rvar) = ctx.assign_imm_map.get(imm) {
                        ctx.replace_var_map.insert(result_var.clone(), rvar.clone());
                    } else {
                        ctx.assign_imm_map.insert(imm.clone(), result_var.clone());
                    }
                }

                _ => {}
            };
        }
    }

    // Replace variables

    for bb in &fun.basic_blocks {
        let bb = ir_ctx.bb_arena.get_mut(*bb).unwrap();

        let mut result = Vec::new();

        for AnnotatedInstr {
            result: result_var,
            inst,
            ty,
        } in bb.insts.clone()
        {
            if ctx.replace_var_map.contains_key(&result_var) {
                continue;
            }

            let inst = match inst {
                I::Operand(op) => I::Operand(replace_var(&ctx, op)),

                I::Branch {
                    cond,
                    then_label,
                    else_label,
                    then_bb,
                    else_bb,
                } => {
                    let cond = replace_var(&ctx, cond);
                    I::Branch {
                        cond,
                        then_label,
                        else_label,
                        then_bb,
                        else_bb,
                    }
                }

                I::Add(left, right) => I::Add(replace_var(&ctx, left), replace_var(&ctx, right)),
                I::Sub(left, right) => I::Sub(replace_var(&ctx, left), replace_var(&ctx, right)),
                I::Mul(left, right) => I::Mul(replace_var(&ctx, left), replace_var(&ctx, right)),
                I::Or(left, right) => I::Or(replace_var(&ctx, left), replace_var(&ctx, right)),
                I::Shift(op, left, right) => {
                    I::Shift(op, replace_var(&ctx, left), replace_var(&ctx, right))
                }
                I::Store(addr, value) => {
                    I::Store(replace_var(&ctx, addr), replace_var(&ctx, value))
                }

                I::Cmp(op, left, right) => {
                    I::Cmp(op, replace_var(&ctx, left), replace_var(&ctx, right))
                }
                I::Call { fun, args } => {
                    let fun = replace_var(&ctx, fun);
                    let args = args.into_iter().map(|arg| replace_var(&ctx, arg)).collect();

                    I::Call { fun, args }
                }

                I::Ret(op) => I::Ret(replace_var(&ctx, op)),

                I::Jump(_, _) | I::Phi(_) | I::Label(_) => inst,
            };

            result.push(AnnotatedInstr {
                result: result_var,
                inst,
                ty,
            });
        }

        bb.insts = result;
    }

    Ok(())
}

pub fn optimize(funcs: &Functions, ir_ctx: &mut IrContext) -> Result<()> {
    for fun in funcs {
        remove_duplicated_assignments(fun, ir_ctx)?;
    }

    Ok(())
}
