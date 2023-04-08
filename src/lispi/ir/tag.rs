use super::instruction::Label;

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
    pub index: usize,
    pub header_label: Label,
    pub loop_label: Label,
}
