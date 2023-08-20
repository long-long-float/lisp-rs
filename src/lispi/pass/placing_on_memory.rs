//! Place `ref`erenced variables on the stack memory.
//!
//! ## Example
//!
//! Translate:
//! ```txt
//!   ; A: Initialize
//!   %var1 = inst
//!   ; B: Reference the variable
//!   %var2 = add %var1, %var1
//!   ; C: Get address of the variable
//!   %var3 = ref %var1
//! ```
//! to:
//! ```txt
//!   %var1-pom0 = inst
//!   %var1 = alloca Int, 1
//!   store %var1, %var1-pom
//!
//!   %var1-pom1 = load %var1
//!   %var2 = add %var1-pom1, %var1-pom1
//!
//!   %var3 = %var1
//! ```

use anyhow::Result;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::lispi::{
    ir,
    ir::{
        basic_block::Functions,
        instruction::{AnnotatedInstr, Instruction, Operand, Variable},
        IrContext,
    },
    ty::Type,
    unique_generator::UniqueGenerator,
};

pub fn optimize(funcs: &Functions, ctx: &mut IrContext) -> Result<()> {
    for fun in funcs {
        let mut vars_on_memory = FxHashSet::default();
        for inst in fun.walk_instructions(&ctx.bb_arena) {
            if let Instruction::Reference(op) = &inst.inst {
                if let Operand::Variable(var) = op {
                    vars_on_memory.insert(var.clone());
                } else {
                    panic!("Cannot get address of immediate now.")
                }
            }
        }

        let mut gen = UniqueGenerator::new("pom".to_string());

        for bb in &fun.basic_blocks {
            let bb = ctx.bb_arena.get_mut(*bb).unwrap();

            let mut result = Vec::new();

            for AnnotatedInstr {
                result: result_var,
                inst,
                ty,
                tags: _,
            } in bb.insts.clone()
            {
                if vars_on_memory.contains(&result_var) {
                    //
                    // A: Initialize
                    //
                    let tmp_var = result_var.clone().with_suffix(&gen.gen_string());
                    result.push(AnnotatedInstr::new(tmp_var.clone(), inst, ty));

                    result.push(AnnotatedInstr::new(
                        result_var.clone(),
                        Instruction::Alloca {
                            // TODO: Set type
                            ty: ir::instruction::Type::I32,
                            count: 1.into(),
                        },
                        Type::None,
                    ));

                    result.push(AnnotatedInstr::new(
                        Variable::empty(),
                        Instruction::Store(result_var.into(), tmp_var.into()),
                        Type::None,
                    ));
                } else {
                    let referenced_var =
                        if let Instruction::Reference(Operand::Variable(var)) = &inst {
                            if vars_on_memory.contains(var) {
                                Some(var)
                            } else {
                                None
                            }
                        } else {
                            None
                        };

                    if let Some(ref_var) = referenced_var {
                        //
                        // C: Get address of the variable
                        //
                        result.push(AnnotatedInstr::new(
                            result_var,
                            Instruction::Operand(ref_var.clone().into()),
                            ty,
                        ));
                    } else {
                        //
                        // B: Reference the variable
                        //

                        let mut vmap = FxHashMap::default();

                        for var in inst.collect_vars() {
                            if !vars_on_memory.contains(var) {
                                continue;
                            }

                            let tmp_var = result_var.clone().with_suffix(&gen.gen_string());

                            result.push(AnnotatedInstr::new(
                                tmp_var.clone(),
                                Instruction::LoadElement {
                                    addr: var.clone().into(),
                                    ty: ir::instruction::Type::I32,
                                    index: 0.into(),
                                },
                                Type::None,
                            ));

                            vmap.insert(var.clone(), tmp_var);
                        }

                        result.push(AnnotatedInstr::new(result_var, inst.replace_var(&vmap), ty));
                    }
                }
            }

            bb.insts = result;
        }
    }

    Ok(())
}
