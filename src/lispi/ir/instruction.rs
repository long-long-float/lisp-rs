use colored::Colorize;
use id_arena::{Arena, Id};
use rustc_hash::FxHashMap;
use std::fmt::Display;

use crate::lispi::{ty::Type, SymbolValue};

use super::{basic_block::BasicBlock, tag::Tag};

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
    Not(Operand),
    Shift(ShiftOperator, Operand, Operand),
    /// addr, value
    Store(Operand, Operand),
    Cmp(CmpOperator, Operand, Operand),
    Call {
        fun: Operand,
        args: Vec<Operand>,
    },
    Phi(Vec<(Operand, Label)>),

    Operand(Operand),
    /// TODO: Remove this
    Label(Label),

    Nop,
}

impl Instruction {
    pub fn is_terminal(&self) -> bool {
        use Instruction::*;

        matches!(self, Branch { .. } | Jump(_, _) | Ret(_))
    }

    pub fn is_removable(&self) -> bool {
        use Instruction::*;

        match self {
            Store(_, _) | Call { .. } => false,
            _ => !self.is_terminal(),
        }
    }

    pub fn has_result(&self) -> bool {
        use Instruction::*;

        matches!(
            self,
            Add(_, _) | Sub(_, _) | Mul(_, _) | Cmp(_, _, _) | Call { .. } | Operand(_) | Phi(_)
        )
    }

    pub fn is_operand(&self) -> bool {
        matches!(self, Instruction::Operand(_))
    }

    pub fn is_label(&self) -> bool {
        matches!(self, Instruction::Label(_))
    }

    pub fn replace_var(self, replace_var_map: &FxHashMap<Variable, Variable>) -> Self {
        fn replace_var(replace_var_map: &FxHashMap<Variable, Variable>, op: Operand) -> Operand {
            match op {
                Operand::Variable(ref var) => {
                    if let Some(replaced_op) = replace_var_map.get(var) {
                        Operand::Variable(replaced_op.clone())
                    } else {
                        op
                    }
                }
                _ => op,
            }
        }

        use Instruction as I;

        match self {
            I::Operand(op) => I::Operand(replace_var(replace_var_map, op)),

            I::Branch {
                cond,
                then_label,
                else_label,
                then_bb,
                else_bb,
            } => {
                let cond = replace_var(replace_var_map, cond);
                I::Branch {
                    cond,
                    then_label,
                    else_label,
                    then_bb,
                    else_bb,
                }
            }

            I::Add(left, right) => I::Add(
                replace_var(replace_var_map, left),
                replace_var(replace_var_map, right),
            ),
            I::Sub(left, right) => I::Sub(
                replace_var(replace_var_map, left),
                replace_var(replace_var_map, right),
            ),
            I::Mul(left, right) => I::Mul(
                replace_var(replace_var_map, left),
                replace_var(replace_var_map, right),
            ),
            I::Or(left, right) => I::Or(
                replace_var(replace_var_map, left),
                replace_var(replace_var_map, right),
            ),
            I::Not(op) => I::Not(replace_var(replace_var_map, op)),
            I::Shift(op, left, right) => I::Shift(
                op,
                replace_var(replace_var_map, left),
                replace_var(replace_var_map, right),
            ),
            I::Store(addr, value) => I::Store(
                replace_var(replace_var_map, addr),
                replace_var(replace_var_map, value),
            ),

            I::Cmp(op, left, right) => I::Cmp(
                op,
                replace_var(replace_var_map, left),
                replace_var(replace_var_map, right),
            ),
            I::Call { fun, args } => {
                let fun = replace_var(replace_var_map, fun);
                let args = args
                    .into_iter()
                    .map(|arg| replace_var(replace_var_map, arg))
                    .collect();

                I::Call { fun, args }
            }

            I::Ret(op) => I::Ret(replace_var(replace_var_map, op)),

            I::Jump(_, _) | I::Phi(_) | I::Label(_) | I::Nop => self,
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
            Not(val) => {
                write!(f, "not {}", val)
            }
            Shift(ShiftOperator::LogicalRight, left, right) => {
                write!(f, "lrshift {}, {}", left, right)
            }
            Shift(ShiftOperator::LogicalLeft, left, right) => {
                write!(f, "llshift {}, {}", left, right)
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
            Nop => {
                write!(f, "nop")
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum ShiftOperator {
    LogicalLeft,
    LogicalRight,
}

#[derive(Clone, PartialEq, Debug)]
pub struct AnnotatedInstr {
    pub result: Variable,
    pub inst: Instruction,
    pub ty: Type,
    pub tags: Vec<Tag>,
}

impl AnnotatedInstr {
    pub fn new(result: Variable, inst: Instruction, ty: Type) -> Self {
        Self {
            result,
            inst,
            ty,
            tags: Vec::new(),
        }
    }

    pub fn display<'a>(&'a self, colored: bool) -> AnnotatedInstrDisplay {
        AnnotatedInstrDisplay {
            instr: self,
            colored,
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct AnnotatedInstrDisplay<'a> {
    instr: &'a AnnotatedInstr,
    colored: bool,
}

impl Display for AnnotatedInstrDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Instruction::*;

        let AnnotatedInstr {
            result,
            inst,
            ty,
            tags,
        } = &self.instr;

        match inst {
            Branch { .. } | Jump(_, _) | Ret(_) | Nop => {
                write!(f, "  {}", inst)?;
            }

            Add(_, _)
            | Sub(_, _)
            | Mul(_, _)
            | Or(_, _)
            | Not(_)
            | Shift(_, _, _)
            | Store(_, _)
            | Cmp(_, _, _)
            | Call { .. }
            | Operand(_)
            | Phi(_) => {
                write!(f, "  {}:{} = {}", result, ty, inst)?;
            }

            Label(_) => {
                write!(f, "{}:", inst)?;
            }
        }

        if !tags.is_empty() && self.colored {
            write!(f, "  {}", ";".dimmed())?;
            for tag in tags {
                let str = format!("{:?}, ", tag).dimmed();
                write!(f, "  {}", str)?;
            }
        }

        Ok(())
    }
}

pub type BasicBlocks = Vec<Id<BasicBlock>>;

#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub args: Vec<(String, Type)>,
    pub free_vars: Vec<SymbolValue>,
    pub ty: Type,

    pub basic_blocks: BasicBlocks,
}

impl Function {
    pub fn new(
        name: String,
        args: Vec<(String, Type)>,
        free_vars: Vec<SymbolValue>,
        ty: Type,
        basic_blocks: BasicBlocks,
    ) -> Self {
        Self {
            name,
            args,
            free_vars,
            ty,
            basic_blocks,
        }
    }

    pub fn dump(&self, arena: &Arena<BasicBlock>) {
        print!("function {} (", self.name);
        for (id, ty) in &self.args {
            print!("%{}: {}, ", id, ty);
        }
        print!(") (");
        for id in &self.free_vars {
            print!("%{}, ", id);
        }
        println!("): {} {{", self.ty);

        for bb in &self.basic_blocks {
            let bb = arena.get(*bb).unwrap();
            println!("  {}:", bb.label);
            for inst in &bb.insts {
                println!("  {}", inst.display(true));
            }
        }

        println!("}}");
    }
}

pub type Instructions = Vec<AnnotatedInstr>;
pub type Functions = Vec<Function>;

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
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
            Immediate(v) => write!(f, "{}", v),
            // Label(v) => write!(f, "{}", v),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum CmpOperator {
    /// '<='
    SGE,
    /// '>'
    SGT,
    /// '<'
    SLT,
}

impl Display for CmpOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use CmpOperator::*;

        let str = match self {
            SGE => "<=",
            SGT => ">",
            SLT => "<",
        };
        write!(f, "{}", str)
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
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

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum Immediate {
    Integer(i32),
    Boolean(bool),
    Label(Label),
}

impl Display for Immediate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Immediate::Integer(v) => write!(f, "{}", v),
            Immediate::Boolean(v) => write!(f, "{}", v),
            Immediate::Label(v) => write!(f, "{}", v),
        }
    }
}
