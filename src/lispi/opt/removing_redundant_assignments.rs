//!
//! This step removes redundant assignments such as `%var1 = %var2`.
//! It propagates assigned variables to the following instructions.
//!

use anyhow::Result;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;

use crate::lispi::ir::IrContext;

use super::super::ir::basic_block::*;
use super::super::ir::instruction::*;

use Instruction as I;

struct Context {
    replace_var_map: FxHashMap<Variable, Variable>,
}

fn remove_redundant_assignments(fun: &Function, ir_ctx: &mut IrContext) -> Result<()> {
    let mut ctx = Context {
        replace_var_map: FxHashMap::default(),
    };

    let mut excluded_vars = FxHashSet::default();

    // Don't remove variables in phi instructions.
    for inst in fun.walk_instructions(&ir_ctx.bb_arena) {
        if let I::Phi(nodes) = &inst.inst {
            for (op, _) in nodes {
                if let Operand::Variable(var) = op {
                    excluded_vars.insert(var.clone());
                }
            }
        }
    }

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
                        let var = ctx.replace_var_map.get(var).unwrap_or(var);

                        // Don't remove loading arguments.
                        let in_args = fun.args.iter().any(|(name, _)| name == &var.name);
                        if !in_args && !excluded_vars.contains(&result_var) {
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
