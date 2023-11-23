//!
//! Removes reference and dereference instructions for the same variable.
//! This also removes loadelement and reference for the same variable.
//!
//! For example, following instructions:
//! ```
//! %var1 = ref %var0
//! ; some instructions...
//! %var2 = deref %var1
//! ````
//!
//! Are converted to:
//! ```
//! ; some instructions...
//! %var2 = %var0
//! ```
//!
//! Following instructions:
//! ```
//! %var1 = loadelement %var0, int, 4
//! ; some instructions...
//! %var2 = deref %var1
//! ````
//!
//! Are converted to:
//! ```
//! ; some instructions...
//! %var2 = addi %var0, 4
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
    let mut le_mapping_candidates = FxHashMap::default();

    for inst in fun.walk_instructions(&ir_ctx.bb_arena) {
        if let Instruction::Reference(Operand::Variable(op)) = &inst.inst {
            ref_mapping_candidates.insert(inst.result.clone(), op.clone());
        } else if let Instruction::LoadElement {
            addr: Operand::Variable(addr),
            ty: _,
            index,
        } = &inst.inst
        {
            le_mapping_candidates.insert(inst.result.clone(), (addr.clone(), index.clone()));
        }
    }

    let mut ref_mapping = FxHashMap::default();
    let mut le_mapping = FxHashMap::default();

    for inst in fun.walk_instructions(&ir_ctx.bb_arena) {
        if let Instruction::Dereference(Operand::Variable(op)) = &inst.inst {
            if let Some(referenced_var) = ref_mapping_candidates.get(&op) {
                ref_mapping.insert(op.clone(), referenced_var.clone());
            }
        } else if let Instruction::Reference(Operand::Variable(op)) = &inst.inst {
            if let Some(referenced_var) = le_mapping_candidates.get(&op) {
                le_mapping.insert(op.clone(), referenced_var.clone());
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
                    // Remove ref and deref

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
            .filter_map(
                |AnnotatedInstr {
                     result: result_var,
                     inst,
                     ty,
                     tags,
                 }| {
                    // Remove loadelement and ref

                    match inst {
                        Instruction::Reference(Operand::Variable(var)) => {
                            if let Some((referenced_var, offset)) = le_mapping.get(&var) {
                                Some(AnnotatedInstr {
                                    result: result_var,
                                    inst: Instruction::Add(
                                        Operand::Variable(referenced_var.clone()),
                                        offset.clone(),
                                    ),
                                    ty,
                                    tags,
                                })
                            } else {
                                Some(AnnotatedInstr {
                                    result: result_var,
                                    inst: Instruction::Reference(Operand::Variable(var)),
                                    ty,
                                    tags,
                                })
                            }
                        }
                        Instruction::LoadElement {
                            addr,
                            ty: ety,
                            index,
                        } => {
                            if le_mapping.contains_key(&result_var) {
                                None
                            } else {
                                Some(AnnotatedInstr {
                                    result: result_var,
                                    inst: Instruction::LoadElement {
                                        addr,
                                        ty: ety,
                                        index,
                                    },
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
