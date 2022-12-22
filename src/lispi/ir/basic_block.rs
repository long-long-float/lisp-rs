use super::instruction as i;

#[derive(Clone, PartialEq, Debug)]
struct BasicBlock {
    label: String,
    insts: Vec<i::Instruction>,
}
