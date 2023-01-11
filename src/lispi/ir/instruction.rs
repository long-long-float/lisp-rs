use anyhow::Result;
use id_arena::{Arena, Id};
use std::{cell::RefCell, collections::HashSet, default, fmt::Display, marker::PhantomData};

use crate::lispi::{
    console::{println, printlnuw, printuw},
    ty::Type,
};

use super::basic_block::BasicBlock;

#[derive(Clone, PartialEq, Debug)]
pub enum Instruction {
    Branch {
        cond: Operand,
        then_label: Label,
        else_label: Label,

        then_bb: Id<BasicBlock>,
        else_bb: Id<BasicBlock>,
    },
    Jump(Label, Id<BasicBlock>),
    Ret(Operand),

    Add(Operand, Operand),
    Sub(Operand, Operand),
    Mul(Operand, Operand),
    Or(Operand, Operand),
    Store(Operand, Operand),
    Cmp(CmpOperator, Operand, Operand),
    Call {
        fun: Operand,
        args: Vec<Operand>,
    },
    Phi(Vec<(Operand, Label)>),

    Operand(Operand),
    Label(Label),
}

impl Instruction {
    pub fn is_terminal(&self) -> bool {
        use Instruction::*;

        match self {
            Branch { .. } | Jump(_, _) | Ret(_) => true,
            _ => false,
        }
    }

    pub fn has_result(&self) -> bool {
        use Instruction::*;

        match self {
            Add(_, _)
            | Sub(_, _)
            | Mul(_, _)
            | Cmp(_, _, _)
            | Call { .. }
            | Operand(_)
            | Phi(_) => true,
            _ => false,
        }
    }

    pub fn is_operand(&self) -> bool {
        if let Instruction::Operand(_) = self {
            true
        } else {
            false
        }
    }

    pub fn is_label(&self) -> bool {
        if let Instruction::Label(_) = self {
            true
        } else {
            false
        }
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Instruction::*;

        match self {
            Branch {
                cond,
                then_label,
                else_label,
                ..
            } => {
                write!(f, "branch {}, {}, {}", cond, then_label, else_label)
            }
            Jump(label, _) => {
                write!(f, "jump {}", label)
            }
            Ret(val) => {
                write!(f, "ret {}", val)
            }
            Add(left, right) => {
                write!(f, "add {}, {}", left, right)
            }
            Sub(left, right) => {
                write!(f, "sub {}, {}", left, right)
            }
            Mul(left, right) => {
                write!(f, "mul {}, {}", left, right)
            }
            Or(left, right) => {
                write!(f, "or {}, {}", left, right)
            }
            Store(addr, value) => {
                write!(f, "store {}, {}", addr, value)
            }
            Cmp(op, left, right) => {
                write!(f, "cmp {}, {}, {}", op, left, right)
            }
            Call { fun, args } => {
                write!(f, "call {}", fun)?;
                for arg in args {
                    write!(f, ", {}", arg)?;
                }
                Ok(())
            }
            Phi(nodes) => {
                write!(f, "phi ")?;
                for (val, label) in nodes {
                    write!(f, "[{}, {}], ", val, label)?;
                }
                Ok(())
            }
            Operand(op) => {
                write!(f, "{}", op)
            }
            Label(label) => {
                write!(f, "{}", label)
            }
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct AnnotatedInstr {
    pub result: Variable,
    pub inst: Instruction,
    pub ty: Type,
}

impl Display for AnnotatedInstr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Instruction::*;
        match &self.inst {
            Branch { .. } | Jump(_, _) | Ret(_) => {
                write!(f, "  {}", self.inst)
            }

            Add(_, _)
            | Sub(_, _)
            | Mul(_, _)
            | Or(_, _)
            | Store(_, _)
            | Cmp(_, _, _)
            | Call { .. }
            | Operand(_)
            | Phi(_) => {
                write!(f, "  {}:{} = {}", self.result, self.ty, self.inst)
            }

            Label(_) => {
                write!(f, "{}:", self.inst)
            }
        }
    }
}

#[derive(Clone)]
pub struct Function {
    pub name: String,
    pub args: Vec<(String, Type)>,
    pub body: Instructions,
    pub ty: Type,

    pub head_bb: Id<BasicBlock>,
}

impl Function {
    pub fn new(
        name: String,
        args: Vec<(String, Type)>,
        body: Instructions,
        ty: Type,
        head_bb: Id<BasicBlock>,
    ) -> Self {
        Self {
            name,
            args,
            body,
            ty,
            head_bb,
        }
    }

    pub fn replace_body_with<F>(self, replacer: F) -> Result<Self>
    where
        F: Fn(Instructions) -> Result<Instructions>,
    {
        let Function {
            name,
            args,
            body,
            ty,
            head_bb,
        } = self;
        let body = replacer(body)?;
        Ok(Function {
            name,
            args,
            body,
            ty,
            head_bb,
        })
    }

    pub fn dump(&self, arena: &Arena<BasicBlock>) {
        print!("function {} (", self.name);
        for (id, ty) in &self.args {
            print!("%{}: {}, ", id, ty);
        }
        println!("): {} {{", self.ty);

        BasicBlock::dump_by_id(self.head_bb, arena, &mut HashSet::new());

        println!("}}");
    }
}

pub type Instructions = Vec<AnnotatedInstr>;
pub type Functions = Vec<Function>;

#[derive(Clone, PartialEq, Debug)]
pub enum Operand {
    Variable(Variable),
    Immediate(Immediate),
    // Label(Label),
}

impl Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Operand::*;

        match self {
            Variable(v) => write!(f, "{}", v),
            Immediate(v) => write!(f, "{:?}", v),
            // Label(v) => write!(f, "{}", v),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum CmpOperator {
    /// <=
    SGE,
}

impl Display for CmpOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use CmpOperator::*;

        match self {
            SGE => write!(f, "<="),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Label {
    pub name: String,
}

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Variable {
    pub name: String,
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%{}", self.name)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Immediate {
    Integer(i32),
    Boolean(bool),
    Label(Label),
}
