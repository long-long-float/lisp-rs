use std::collections::HashSet;

use id_arena::{Arena, Id};

use super::instruction as i;

#[derive(Clone, PartialEq, Debug)]
pub struct BasicBlock {
    pub label: String,
    pub insts: Vec<i::AnnotatedInstr>,
}

impl BasicBlock {
    pub fn dump_by_id(
        bb: Id<BasicBlock>,
        arena: &Arena<BasicBlock>,
        dumped_bb: &mut HashSet<Id<BasicBlock>>,
    ) {
        if dumped_bb.contains(&bb) {
            return;
        }
        dumped_bb.insert(bb);

        let bb = arena.get(bb).unwrap();

        println!("  {}:", bb.label);
        for inst in &bb.insts {
            println!("  {}", inst);
        }

        for inst in &bb.insts {
            match inst.inst {
                i::Instruction::Branch {
                    then_bb, else_bb, ..
                } => {
                    Self::dump_by_id(then_bb, arena, dumped_bb);
                    Self::dump_by_id(else_bb, arena, dumped_bb);
                }
                i::Instruction::Jump(_, bb) => {
                    Self::dump_by_id(bb, arena, dumped_bb);
                }
                _ => {}
            }
        }
    }

    pub fn new(label: String) -> Self {
        Self {
            label,
            insts: Vec::new(),
        }
    }

    pub fn push_inst(&mut self, inst: i::AnnotatedInstr) {
        self.insts.push(inst);
    }
}
