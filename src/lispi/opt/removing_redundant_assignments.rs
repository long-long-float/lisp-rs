//!
//! This step removes redundant assignments such as `%var1 = %var2`.
//! It propagates assigned variables to the following instructions.
//!

use anyhow::Result;
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::lispi::ir::IrContext;

use super::super::ir::instruction::*;

use Instruction as I;

struct Context {
    replace_var_map: FxHashMap<Variable, Variable>,
}

fn remove_redundant_assignments(fun: &Function, ir_ctx: &mut IrContext) -> Result<()> {
    let mut ctx = Context {
        replace_var_map: FxHashMap::default(),
    };

    // Map two variables

    for bb in &fun.basic_blocks {
        let bb = ir_ctx.bb_arena.get_mut(*bb).unwrap();

        bb.insts = bb
            .insts
            .drain(..)
            .filter_map(
                |AnnotatedInstr {
                     result: result_var,
                     inst,
                     ty,
                     tags,
                 }| {
                    if let I::Operand(Operand::Variable(var)) = &inst {
                        // Don't remove loading arguments.
                        let in_args = fun.args.iter().any(|(name, _)| name == &var.name);
                        if !in_args {
                            ctx.replace_var_map.insert(result_var, var.clone());
                            return None;
                        }
                    }
                    Some(AnnotatedInstr {
                        result: result_var,
                        inst: inst.replace_var(&ctx.replace_var_map),
                        ty,
                        tags,
                    })
                },
            )
            .collect_vec();
    }

    Ok(())
}

pub fn optimize(funcs: &Functions, ir_ctx: &mut IrContext) -> Result<()> {
    for fun in funcs {
        remove_redundant_assignments(fun, ir_ctx)?;
    }

    Ok(())
}