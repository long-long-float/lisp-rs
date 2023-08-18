use anyhow::Result;
use rustc_hash::FxHashMap;

use crate::lispi::ir::IrContext;

use super::super::ir::basic_block::*;
use super::super::ir::instruction::*;

use Instruction as I;

struct Context {
    assign_var_map: FxHashMap<Variable, Variable>,
    assign_imm_map: FxHashMap<Immediate, Variable>,

    replace_var_map: FxHashMap<Variable, Variable>,
}

fn remove_duplicated_assignments(fun: &Function, ir_ctx: &mut IrContext) -> Result<()> {
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
            tags: _,
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
            tags: _,
        } in bb.insts.clone()
        {
            if ctx.replace_var_map.contains_key(&result_var) {
                continue;
            }

            let inst = inst.replace_var(&ctx.replace_var_map);
            result.push(AnnotatedInstr::new(result_var, inst, ty));
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
