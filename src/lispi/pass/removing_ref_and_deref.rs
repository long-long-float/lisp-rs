//!
//! Removing reference and dereference instructions for the same variable.
//!
//! For example, following instructions:
//! ```
//! %var1 = ref %var0
//! ; some instructions...
//! %var2 = deref %var1
//! ````
//!
//! Are converted to:
//!
//! ```
//! ; some instructions...
//! %var2 = %var0
//! ```
//!

use anyhow::Result;
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::lispi::ir::{
    basic_block::{Function, IrProgram},
    instruction::{AnnotatedInstr, Instruction, Operand},
    IrContext,
};

pub fn remove_ref_and_deref(fun: &Function, ir_ctx: &mut IrContext) -> Result<()> {
    let mut ref_mapping_candidates = FxHashMap::default();

    for inst in fun.walk_instructions(&ir_ctx.bb_arena) {
        if let Instruction::Reference(Operand::Variable(op)) = &inst.inst {
            ref_mapping_candidates.insert(inst.result.clone(), op.clone());
        }
    }

    let mut ref_mapping = FxHashMap::default();
    for inst in fun.walk_instructions(&ir_ctx.bb_arena) {
        if let Instruction::Dereference(Operand::Variable(op)) = &inst.inst {
            if let Some(referenced_var) = ref_mapping_candidates.get(&op) {
                ref_mapping.insert(op.clone(), referenced_var.clone());
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
                    match inst {
                        Instruction::Dereference(Operand::Variable(var)) => {
                            if let Some(referenced_var) = ref_mapping.get(&var) {
                                Some(AnnotatedInstr {
                                    result: result_var,
                                    inst: Instruction::Operand(Operand::Variable(
                                        referenced_var.clone(),
                                    )),
                                    ty,
                                    tags,
                                })
                            } else {
                                Some(AnnotatedInstr {
                                    result: result_var,
                                    inst: Instruction::Dereference(Operand::Variable(var)),
                                    ty,
                                    tags,
                                })
                            }
                        }
                        Instruction::Reference(Operand::Variable(var)) => {
                            if ref_mapping.contains_key(&result_var) {
                                None
                            } else {
                                Some(AnnotatedInstr {
                                    result: result_var,
                                    inst: Instruction::Reference(Operand::Variable(var)),
                                    ty,
                                    tags,
                                })
                            }
                        }
                        _ => Some(AnnotatedInstr {
                            result: result_var,
                            inst,
                            ty,
                            tags,
                        }),
                    }
                },
            )
            .collect_vec();
    }

    Ok(())
}

pub fn optimize(program: &IrProgram, ir_ctx: &mut IrContext) -> Result<()> {
    for fun in &program.funcs {
        remove_ref_and_deref(fun, ir_ctx)?;
    }

    Ok(())
}
