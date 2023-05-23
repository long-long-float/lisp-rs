use super::instruction::{Label, Variable};

#[derive(Clone, PartialEq, Debug)]
pub enum Tag {
    /// Indicates the head of the loop
    LoopHeader {
        label: String,
    },
    // Indicates that it will be replaced by phi function
    LoopPhiFunctionSite(LoopPhiFunctionSite),
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
