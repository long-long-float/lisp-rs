use std::fmt::Display;

use super::instruction as i;

#[derive(Clone, PartialEq, Debug)]
pub struct BasicBlock {
    pub label: String,
    pub insts: Vec<i::AnnotatedInstr>,
}

impl BasicBlock {
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

impl Display for BasicBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "  {}:", self.label)?;
        for inst in &self.insts {
            writeln!(f, "  {}", inst)?;
        }
        Ok(())
    }
}
