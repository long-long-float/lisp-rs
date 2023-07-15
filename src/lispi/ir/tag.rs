use super::instruction::{Label, Variable};

#[derive(Clone, PartialEq, Debug)]
pub enum Tag {
    /// Indicates the head of the loop
    LoopHeader { label: String },
    /// Indicates that it will be replaced by phi function
    LoopPhiFunctionSite(LoopPhiFunctionSite),
    /// Indicates that the result variable don't need to be allocated a register.
    DontAllocateRegister,
}

impl Tag {
    pub fn is_match_with(&self, tag: &Tag) -> bool {
        use Tag::*;
        matches!(
            (self, tag),
            (LoopHeader { .. }, LoopHeader { .. })
                | (LoopPhiFunctionSite(_), LoopPhiFunctionSite(_))
                | (DontAllocateRegister, DontAllocateRegister)
        )
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct LoopPhiFunctionSite {
    pub label: String,
    pub index: LoopPhiFunctionSiteIndex,
    pub header_label: Label,
}

#[derive(Clone, PartialEq, Debug)]
pub enum LoopPhiFunctionSiteIndex {
    Loop(usize),
    FreeVar(Variable),
}
