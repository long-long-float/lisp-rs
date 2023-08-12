use rustc_hash::FxHashSet;

use crate::lispi::ir::{
    basic_block::Functions,
    instruction::{Immediate, Instruction, Operand},
    IrContext,
};

pub fn optimize(funcs: Functions, ctx: &mut IrContext) -> Functions {
    let mut called_funcs = FxHashSet::default();
    called_funcs.insert("main".to_string());

    for func in &funcs {
        for inst in func.walk_instructions(&ctx.bb_arena) {
            if let Instruction::Call {
                fun: Operand::Immediate(Immediate::Label(name)),
                ..
            } = &inst.inst
            {
                called_funcs.insert(name.name.clone());
            }
        }
    }

    funcs
        .into_iter()
        .filter(|func| called_funcs.contains(&func.name))
        .collect()
}
