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
            FixedArray(..) => {
                panic!("Cannot get fixed array size from its type.")
            }
            Void => 4,
            _ => todo!(),
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

    pub fn display(&self, colored: bool) -> InstructionDisplay {
        InstructionDisplay {
            instr: self,
            colored,
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct InstructionDisplay<'a> {
    instr: &'a Instruction,
    colored: bool,
}

impl<'a> Display for InstructionDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Instruction::*;

        let mut operands: Vec<Box<&dyn ColoredDisplay>> = Vec::new();

        let name = match &self.instr {
            Branch {
                cond,
                then_label,
                else_label,
                ..
            } => {
                operands.push(Box::new(cond));
                operands.push(Box::new(then_label));
                operands.push(Box::new(else_label));
                "branch"
            }
            Jump(label, _) => {
                operands.push(Box::new(label));
                "jump"
            }
            Ret(val) => {
                operands.push(Box::new(val));
                "ret"
            }
            Alloca { ty, count } => {
                operands.push(Box::new(ty));
                operands.push(Box::new(count));
                "alloca"
            }
            Add(left, right) => {
                operands.push(Box::new(left));
                operands.push(Box::new(right));
                "add"
            }
            Sub(left, right) => {
                operands.push(Box::new(left));
                operands.push(Box::new(right));
                "sub"
            }
            Mul(left, right) => {
                operands.push(Box::new(left));
                operands.push(Box::new(right));
                "mul"
            }
            Div(left, right) => {
                operands.push(Box::new(left));
                operands.push(Box::new(right));
                "div"
            }
            Mod(left, right) => {
                operands.push(Box::new(left));
                operands.push(Box::new(right));
                "mod"
            }
            And(left, right) => {
                operands.push(Box::new(left));
                operands.push(Box::new(right));
                "and"
            }
            Or(left, right) => {
                operands.push(Box::new(left));
                operands.push(Box::new(right));
                "or"
            }
            Not(val) => {
                operands.push(Box::new(val));
                "not"
            }
            Shift(ShiftOperator::LogicalRight, left, right) => {
                operands.push(Box::new(left));
                operands.push(Box::new(right));
                "lrshift"
            }
            Shift(ShiftOperator::LogicalLeft, left, right) => {
                operands.push(Box::new(left));
                operands.push(Box::new(right));
                "llshift"
            }
            Store(addr, value) => {
                operands.push(Box::new(addr));
                operands.push(Box::new(value));
                "store"
            }
            LoadElement { addr, ty, index } => {
                operands.push(Box::new(addr));
                operands.push(Box::new(ty));
                operands.push(Box::new(index));
                "loadelement"
            }
            StoreElement {
                addr,
                ty,
                index,
                value,
            } => {
                operands.push(Box::new(addr));
                operands.push(Box::new(ty));
                operands.push(Box::new(index));
                operands.push(Box::new(value));
                "storeelement"
            }
            Cmp(op, left, right) => {
                operands.push(Box::new(op));
                operands.push(Box::new(left));
                operands.push(Box::new(right));
                "cmp"
            }
            Call { fun, args } => {
                operands.push(Box::new(fun));
                for arg in args {
                    operands.push(Box::new(arg));
                }
                "call"
            }
            SysCall { number, args } => {
                operands.push(Box::new(number));
                for arg in args {
                    operands.push(Box::new(arg));
                }
                "syscall"
            }
            Phi(nodes) => {
                for node in nodes {
                    operands.push(Box::new(node));
                }
                "phi"
            }
            Reference(op) => {
                operands.push(Box::new(op));
                "ref"
            }
            Operand(op) => {
                operands.push(Box::new(op));
                ""
            }
            Label(label) => {
                operands.push(Box::new(label));
                ""
            }
            Nop => "nop",
        };

        if self.colored {
            write!(f, "{}", name.yellow())?;
        } else {
            write!(f, "{}", name)?;
        }

        if let Some((fst, rest)) = operands.split_first() {
            write!(f, " {}", fst.display(self.colored))?;
            for op in rest {
                write!(f, ", {}", op.display(self.colored))?;
            }
        }

        Ok(())
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
            write!(f, "{}:", inst.display(self.colored))?;
        } else if !self.instr.has_result() {
            write!(f, "  {}", inst.display(self.colored))?;
        } else {
            let result = if self.colored {
                result.to_string().blue().to_string()
            } else {
                result.to_string()
            };
            write!(
                f,
                "  {}:{} = {}",
                result,
                ty.display(self.colored),
                inst.display(self.colored)
            )?;
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

trait ColoredDisplay {
    fn display<'a>(&'a self, colored: bool) -> Box<dyn Display + 'a>;
}

impl ColoredDisplay for Type {
    fn display<'a>(&'a self, colored: bool) -> Box<dyn Display + 'a> {
        Box::new(TypeDisplay { ty: self, colored })
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct TypeDisplay<'a> {
    ty: &'a Type,
    colored: bool,
}

impl Display for TypeDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.colored {
            write!(f, "{}", self.ty.to_string().green())
        } else {
            write!(f, "{}", self.ty)
        }
    }
}

// Implementation for phi
impl ColoredDisplay for (Operand, Label) {
    fn display<'a>(&'a self, colored: bool) -> Box<dyn Display + 'a> {
        Box::new(PhiNodeDisplay {
            node: self,
            colored,
        })
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct PhiNodeDisplay<'a> {
    node: &'a (Operand, Label),
    colored: bool,
}

impl Display for PhiNodeDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}, {}]",
            self.node.0.display(self.colored),
            self.node.1.display(self.colored)
        )
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum Operand {
    Variable(Variable),
    Immediate(Immediate),
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

impl ColoredDisplay for Operand {
    fn display<'a>(&'a self, colored: bool) -> Box<dyn Display + 'a> {
        Box::new(OperandDisplay { op: self, colored })
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct OperandDisplay<'a> {
    op: &'a Operand,
    colored: bool,
}

impl Display for OperandDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Operand::*;

        if self.colored {
            match &self.op {
                Variable(v) => write!(f, "{}", format!("%{}", v.name).blue()),
                Immediate(v) => write!(f, "{}", v.to_string().bright_red()),
            }
        } else {
            match &self.op {
                Variable(v) => write!(f, "{}", v),
                Immediate(v) => write!(f, "{}", v),
            }
        }
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

impl ColoredDisplay for CmpOperator {
    fn display<'a>(&'a self, colored: bool) -> Box<dyn Display + 'a> {
        Box::new(CmpOperatorDisplay { op: self, colored })
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct CmpOperatorDisplay<'a> {
    op: &'a CmpOperator,
    colored: bool,
}

impl<'a> Display for CmpOperatorDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use CmpOperator::*;

        let str = match self.op {
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

impl ColoredDisplay for Label {
    fn display<'a>(&'a self, colored: bool) -> Box<dyn Display + 'a> {
        Box::new(LabelDisplay {
            label: self,
            colored,
        })
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct LabelDisplay<'a> {
    label: &'a Label,
    colored: bool,
}

impl<'a> Display for LabelDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.colored {
            write!(f, "{}", self.label.name.cyan())
        } else {
            write!(f, "{}", self.label.name)
        }
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
            Label(v) => write!(f, "{}", v.name),
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
