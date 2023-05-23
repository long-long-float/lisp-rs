use std::collections::VecDeque;

use id_arena::{Arena, Id};
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

pub trait BasicBlockIdExtension {
    /// Find BasicBlock by BFS
    fn find_forward<'a, F>(&self, arena: &'a Arena<BasicBlock>, pred: F) -> Option<&'a BasicBlock>
    where
        F: FnMut(&'a BasicBlock) -> bool;
}

impl BasicBlockIdExtension for Id<BasicBlock> {
    fn find_forward<'a, F>(
        &self,
        arena: &'a Arena<BasicBlock>,
        mut pred: F,
    ) -> Option<&'a BasicBlock>
    where
        F: FnMut(&'a BasicBlock) -> bool,
    {
        let mut que = VecDeque::new();

        que.push_back(self);

        let mut visited_bbs = FxHashSet::default();

        while let Some(bb) = que.pop_back() {
            if visited_bbs.contains(bb) {
                continue;
            }
            visited_bbs.insert(bb);

            let bb = arena.get(*bb).unwrap();

            if pred(bb) {
                return Some(bb);
            }

            for dbb in &bb.destination_bbs {
                que.push_back(dbb);
            }
        }

        None
    }
}
