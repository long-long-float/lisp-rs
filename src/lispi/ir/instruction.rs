use colored::Colorize;
use id_arena::Id;
use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt::Display;

use crate::lispi::ty::Type;

use super::{basic_block::BasicBlock, tag::Tag};

impl Type {
    /// Return data size in bytes
    pub fn size(&self) -> usize {
        use Type::*;
        match self {
            Int => 4,
            Char => 1,
            Struct { .. } => {
                panic!("Cannot get struct size from its type.")
            }
            _ => 4,
        }
    }
}

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

    /// It allocates count (in bytes) on the stack frame.
    /// Allocated memory is released when the function returns.
    Alloca {
        /// TODO: Remove this
        ty: Type,
        count: Operand,
    },

    Add(Operand, Operand),
    Sub(Operand, Operand),
    Mul(Operand, Operand),
    Div(Operand, Operand),
    Mod(Operand, Operand),
    And(Operand, Operand),
    Or(Operand, Operand),
    Not(Operand),
    Shift(ShiftOperator, Operand, Operand),
    /// addr, value
    Store(Operand, Operand),
    /// Load the data whose size is ty from addr + index (in bytes).
    LoadElement {
        addr: Operand,
        ty: Type,
        index: Operand,
    },
    /// Store value whose size is ty to addr + index (in bytes).
    StoreElement {
        addr: Operand,
        ty: Type,
        index: Operand,
        value: Operand,
    },
    Cmp(CmpOperator, Operand, Operand),
    Call {
        fun: Operand,
        args: Vec<Operand>,
    },
    /// Calls a system function. Note that args depend on the target environment strongly.
    SysCall {
        number: Operand,
        args: Vec<Operand>,
    },
    Phi(Vec<(Operand, Label)>),

    Reference(Operand),

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
            Store(_, _) | StoreElement { .. } | Call { .. } | SysCall { .. } => false,
            _ => !self.is_terminal(),
        }
    }

    pub fn has_result(&self) -> bool {
        use Instruction::*;

        matches!(
            self,
            Add(_, _)
                | Sub(..)
                | Mul(..)
                | Cmp(..)
                | Or(..)
                | And(..)
                | Call { .. }
                | Operand(_)
                | Reference(_)
                | Phi(_)
        )
    }

    pub fn is_operand(&self) -> bool {
        matches!(self, Instruction::Operand(_))
    }

    pub fn is_label(&self) -> bool {
        matches!(self, Instruction::Label(_))
    }

    pub fn collect_vars(&self) -> FxHashSet<&Variable> {
        fn add_only_var<'a>(op: &'a Operand, vars: &mut FxHashSet<&'a Variable>) {
            if let Operand::Variable(var) = op {
                vars.insert(var);
            }
        }

        let mut vars = FxHashSet::default();

        match self {
            Instruction::Branch { cond, .. } => {
                add_only_var(cond, &mut vars);
            }
            Instruction::Jump(_, _) => {}
            Instruction::Ret(op) => add_only_var(op, &mut vars),
            Instruction::Alloca { ty: _, count } => add_only_var(count, &mut vars),
            Instruction::Add(left, right)
            | Instruction::Sub(left, right)
            | Instruction::Mul(left, right)
            | Instruction::Div(left, right)
            | Instruction::Mod(left, right)
            | Instruction::And(left, right)
            | Instruction::Or(left, right) => {
                add_only_var(left, &mut vars);
                add_only_var(right, &mut vars);
            }

            Instruction::Not(op) => {
                add_only_var(op, &mut vars);
            }
            Instruction::Shift(_, left, right) => {
                add_only_var(left, &mut vars);
                add_only_var(right, &mut vars);
            }
            Instruction::Store(addr, value) => {
                add_only_var(addr, &mut vars);
                add_only_var(value, &mut vars);
            }
            Instruction::LoadElement { addr, ty: _, index } => {
                add_only_var(addr, &mut vars);
                add_only_var(index, &mut vars);
            }
            Instruction::StoreElement {
                addr,
                ty: _,
                index,
                value,
            } => {
                add_only_var(addr, &mut vars);
                add_only_var(index, &mut vars);
                add_only_var(value, &mut vars);
            }
            Instruction::Cmp(_, left, right) => {
                add_only_var(left, &mut vars);
                add_only_var(right, &mut vars);
            }
            Instruction::Call { fun, args } => {
                add_only_var(fun, &mut vars);
                for arg in args {
                    add_only_var(arg, &mut vars);
                }
            }
            Instruction::SysCall { number, args } => {
                add_only_var(number, &mut vars);
                for arg in args {
                    add_only_var(arg, &mut vars);
                }
            }
            Instruction::Phi(nodes) => {
                for (op, _) in nodes {
                    add_only_var(op, &mut vars);
                }
            }
            Instruction::Operand(op) => add_only_var(op, &mut vars),
            Instruction::Reference(op) => add_only_var(op, &mut vars),
            Instruction::Label(_) => {}
            Instruction::Nop => {}
        }

        vars
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

            I::Alloca { ty, count } => I::Alloca {
                ty,
                count: replace_var(replace_var_map, count),
            },

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
            I::Div(left, right) => I::Div(
                replace_var(replace_var_map, left),
                replace_var(replace_var_map, right),
            ),
            I::Mod(left, right) => I::Mod(
                replace_var(replace_var_map, left),
                replace_var(replace_var_map, right),
            ),
            I::Or(left, right) => I::Or(
                replace_var(replace_var_map, left),
                replace_var(replace_var_map, right),
            ),
            I::And(left, right) => I::And(
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
            I::LoadElement { addr, ty, index } => I::LoadElement {
                addr: replace_var(replace_var_map, addr),
                ty,
                index: replace_var(replace_var_map, index),
            },
            I::StoreElement {
                addr,
                ty,
                index,
                value,
            } => I::StoreElement {
                addr: replace_var(replace_var_map, addr),
                ty,
                index: replace_var(replace_var_map, index),
                value: replace_var(replace_var_map, value),
            },

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
            I::SysCall { number, args } => {
                let number = replace_var(replace_var_map, number);
                let args = args
                    .into_iter()
                    .map(|arg| replace_var(replace_var_map, arg))
                    .collect();

                I::SysCall { number, args }
            }

            I::Reference(op) => I::Reference(replace_var(replace_var_map, op)),

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
            Alloca { ty, count } => {
                write!(f, "alloca {:?}, {}", ty, count)
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
            Div(left, right) => {
                write!(f, "div {}, {}", left, right)
            }
            Mod(left, right) => {
                write!(f, "mod {}, {}", left, right)
            }
            And(left, right) => {
                write!(f, "and {}, {}", left, right)
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
            LoadElement { addr, ty, index } => {
                write!(f, "loadelement {}, {:?}, {}", addr, ty, index)
            }
            StoreElement {
                addr,
                ty,
                index,
                value,
            } => {
                write!(f, "storeelement {}, {:?}, {}, {}", addr, ty, index, value)
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
            SysCall { number, args } => {
                write!(f, "syscall {}", number)?;
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
            Reference(op) => {
                write!(f, "ref {}", op)
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

    pub fn with_tags(self, tags: Vec<Tag>) -> Self {
        Self { tags, ..self }
    }

    pub fn has_tag(&self, tag: Tag) -> bool {
        self.tags.iter().any(|t| t.is_match_with(&tag))
    }

    pub fn has_result(&self) -> bool {
        use Instruction::*;
        !matches!(
            &self.inst,
            Branch { .. } | Jump(_, _) | Ret(_) | Nop | Store(_, _) | StoreElement { .. }
        ) && (self.ty != Type::Void)
    }

    pub fn display(&self, colored: bool) -> AnnotatedInstrDisplay {
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

        if let Label(_) = inst {
            write!(f, "{}:", inst)?;
        } else if !self.instr.has_result() {
            // write!(f, "  {}", inst)?;
            write!(f, "  {}:{} = {}", result, ty, inst)?;
        } else {
            write!(f, "  {}:{} = {}", result, ty, inst)?;
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

pub type Instructions = Vec<AnnotatedInstr>;

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

impl From<Variable> for Operand {
    fn from(var: Variable) -> Self {
        Operand::Variable(var)
    }
}

impl From<i32> for Operand {
    fn from(value: i32) -> Self {
        Operand::Immediate(Immediate::Integer(value))
    }
}

impl From<usize> for Operand {
    fn from(value: usize) -> Self {
        Self::from(value as i32)
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum CmpOperator {
    Eq,
    /// '>='
    SGE,
    /// '<='
    SLE,
    /// '>'
    SGT,
    /// '<'
    SLT,
}

impl Display for CmpOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use CmpOperator::*;

        let str = match self {
            Eq => "=",
            SGE => ">=",
            SLE => "<=",
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

impl Variable {
    pub fn new(name: String) -> Self {
        Self { name }
    }

    pub fn empty() -> Variable {
        Variable {
            name: "".to_string(),
        }
    }

    pub fn with_suffix(self, suff: &String) -> Self {
        Self::new(format!("{}-{}", self.name, suff))
    }
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
        use Immediate::*;
        match self {
            Integer(v) => write!(f, "{}", v),
            Boolean(v) => write!(f, "{}", v),
            Label(v) => write!(f, "{}", v),
            // Array(elems) => {
            //     write!(
            //         f,
            //         "[{}]",
            //         elems.iter().map(|elem| elem.to_string()).join(", ")
            //     )
            // }
        }
    }
}
