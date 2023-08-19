use rustc_hash::FxHashMap;

use crate::lispi::ir::{
    basic_block::Functions,
    instruction::{Immediate, Instruction, Operand},
    IrContext,
};

fn is_called_from_main(
    calling_relations: &FxHashMap<String, Vec<String>>,
    func_name: &String,
) -> bool {
    fn is_called_internal(
        calling_relations: &FxHashMap<String, Vec<String>>,
        func_name: &String,
        current: &String,
    ) -> bool {
        if current == func_name {
            true
        } else if let Some(funcs) = calling_relations.get(current) {
            funcs
                .iter()
                .any(|f| is_called_internal(calling_relations, func_name, f))
        } else {
            false
        }
    }

    is_called_internal(calling_relations, func_name, &"main".to_string())
}

pub fn optimize(funcs: Functions, ctx: &mut IrContext) -> Functions {
    // Map caller function to called functions
    let mut calling_relations: FxHashMap<String, Vec<String>> = FxHashMap::default();

    for func in &funcs {
        for inst in func.walk_instructions(&ctx.bb_arena) {
            if let Instruction::Call {
                fun: Operand::Immediate(Immediate::Label(name)),
                ..
            } = &inst.inst
            {
                let name = name.name.clone();
                if let Some(called_funcs) = calling_relations.get_mut(&func.name) {
                    called_funcs.push(name);
                } else {
                    calling_relations.insert(func.name.clone(), vec![name]);
                }
            }
        }
    }

    funcs
        .into_iter()
        .filter(|func| 
            // Don't remove lambdas conservatively
            func.is_lambda || is_called_from_main(&calling_relations, &func.name))
        .collect()
}
