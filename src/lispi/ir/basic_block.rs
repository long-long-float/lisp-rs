use super::instruction as i;

#[derive(Clone, PartialEq, Debug)]
pub struct BasicBlock {
    pub label: String,
    pub insts: Vec<i::Instruction>,
}

impl BasicBlock {
    pub fn new(label: String) -> Self {
        Self {
            label,
            insts: Vec::new(),
        }
    }
}
