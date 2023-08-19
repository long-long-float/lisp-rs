//! Place `ref`erenced variables on the stack memory.
//!
//! ## Example
//!
//! Translate:
//! ```txt
//!   %var1 = inst
//!   %var2 = add %var1, %var1
//!   %var3 = ref %var1
//! ```
//! to:
//! ```txt
//!   %var1-pom0 = inst
//!   %var1 = alloca Int, 1
//!   store %var1, %var1-pom
//!
//!   %var1-pom1 = load %var1
//!   %var1-pom2 = load %var1
//!   %var2 = add %var1-pom1, %var1-pom2
//!
//!   %var3 = %var1
//! ```

use anyhow::Result;
use object::pe::COR_VTABLE_FROM_UNMANAGED_RETAIN_APPDOMAIN;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::lispi::{
    ir,
    ir::{
        basic_block::Functions,
        instruction::{AnnotatedInstr, Immediate, Instruction, Operand, Variable},
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
                result: var,
                inst,
                ty,
                tags: _,
            } in bb.insts.clone()
            {
                if vars_on_memory.contains(&var) {
                    let tmp_var = var.clone().with_suffix(&gen.gen_string());
                    result.push(AnnotatedInstr::new(
                        tmp_var.clone(),
                        Instruction::Operand(tmp_var.clone().into()),
                        Type::None,
                    ));

                    result.push(AnnotatedInstr::new(
                        var.clone(),
                        Instruction::Alloca {
                            ty: ir::instruction::Type::I32,
                            count: 1.into(),
                        },
                        Type::None,
                    ));

                    result.push(AnnotatedInstr::new(
                        Variable::empty(),
                        Instruction::Store(var.into(), tmp_var.into()),
                        Type::None,
                    ));
                }

                // TODO: write
            }
        }
    }

    Ok(())
}
