use id_arena::Id;
use rustc_hash::FxHashSet;

use super::instruction as i;

#[derive(Clone, PartialEq, Debug)]
pub struct BasicBlock {
    pub label: String,
    pub insts: Vec<i::AnnotatedInstr>,

    /// Basic blocks where the control flow goes to
    pub destination_bbs: FxHashSet<Id<BasicBlock>>,

    /// Basic blocks where the control flow comes from
    pub source_bbs: FxHashSet<Id<BasicBlock>>,

    pub preceding_bb: Option<Id<BasicBlock>>,
}

impl BasicBlock {
    pub fn new(label: String, preceding_bb: Option<Id<BasicBlock>>) -> Self {
        Self {
            label,
            insts: Vec::new(),
            destination_bbs: FxHashSet::default(),
            source_bbs: FxHashSet::default(),
            preceding_bb,
        }
    }

    pub fn push_inst(&mut self, inst: i::AnnotatedInstr) {
        self.insts.push(inst);
    }
}
