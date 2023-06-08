use rustc_hash::FxHashMap;

use super::super::ir::{basic_block as bb, instruction as i, IrContext};

pub fn remove_phi_instructions(funcs: &bb::Functions, ir_ctx: &mut IrContext) {
    for fun in funcs {
        let bb::Function {
            name: _,
            args: _,
            free_vars: _,
            ty: _,
            basic_blocks,
        } = fun;

        let mut assign_map = FxHashMap::default();

        for bb in basic_blocks {
            let bb = ir_ctx.bb_arena.get_mut(*bb).unwrap();

            for i::AnnotatedInstr {
                result,
                inst,
                ty,
                tags: _,
            } in &bb.insts
            {
                if let i::Instruction::Phi(nodes) = &inst {
                    for (node, label) in nodes {
                        if !assign_map.contains_key(&label.name) {
                            assign_map.insert(label.name.clone(), Vec::new());
                        }

                        if let Some(entries) = assign_map.get_mut(&label.name) {
                            entries.push((result.clone(), ty.clone(), node.clone()));
                        }
                    }
                }
            }
        }

        for bb in basic_blocks {
            let bb = ir_ctx.bb_arena.get_mut(*bb).unwrap();

            let mut insts = Vec::new();
            insts.append(&mut bb.insts);

            let mut new_insts = Vec::new();

            for i::AnnotatedInstr {
                result,
                inst,
                ty,
                tags: _,
            } in insts.into_iter().rev()
            {
                match &inst {
                    i::Instruction::Phi(_) => { /* Remove phi instruction */ }
                    _ => {
                        if !inst.is_terminal() {
                            if let Some(entries) = assign_map.remove(&bb.label) {
                                for (result, ty, operand) in entries {
                                    new_insts.push(i::AnnotatedInstr::new(
                                        result,
                                        i::Instruction::Operand(operand),
                                        ty,
                                    ));
                                }
                            }
                        }

                        new_insts.push(i::AnnotatedInstr::new(result, inst, ty));
                    }
                }
            }

            new_insts.reverse();
            bb.insts = new_insts;
        }
    }
}
