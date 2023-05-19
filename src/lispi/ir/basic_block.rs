use id_arena::Id;

use super::instruction as i;

#[derive(Clone, PartialEq, Debug)]
pub struct BasicBlock {
    pub label: String,
    pub insts: Vec<i::AnnotatedInstr>,

    /// Basic blocks where the control flow goes to
    pub destination_bbs: Vec<Id<BasicBlock>>,

    /// Basic blocks where the control flow comes from
    pub source_bbs: Vec<Id<BasicBlock>>,
}

impl BasicBlock {
    pub fn new(label: String) -> Self {
        Self {
            label,
            insts: Vec::new(),
            destination_bbs: Vec::new(),
            source_bbs: Vec::new(),
        }
    }

    pub fn push_inst(&mut self, inst: i::AnnotatedInstr) {
        self.insts.push(inst);
    }
}
