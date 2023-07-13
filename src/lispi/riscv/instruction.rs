use std::fmt::Display;
use std::ops;

use crate::lispi::ir::instruction::{self as i, Label};

type RegisterType = u32;
pub const XLEN: u8 = 32;

#[derive(Clone, PartialEq, Debug)]
pub enum Instruction {
    R(RInstruction),
    I(IInstruction),
    S(SInstruction),
    J(JInstruction),
    U(UInstruction),
    SB(SBInstruction),
}

impl Instruction {
    // Pseudo instructions

    pub fn mv(rd: Register, rs1: Register) -> Instruction {
        Instruction::R(RInstruction {
            op: RInstructionOp::Add,
            rs1,
            rs2: Register::zero(),
            rd,
        })
    }

    pub fn li(rd: Register, imm: Immediate) -> Instruction {
        Instruction::I(IInstruction {
            op: IInstructionOp::Addi,
            imm,
            rs1: Register::zero(),
            rd,
        })
    }

    pub fn ret() -> Instruction {
        Instruction::I(IInstruction {
            op: IInstructionOp::Jalr,
            imm: Immediate::new(0),
            rs1: Register::ra(),
            rd: Register::zero(),
        })
    }

    #[allow(dead_code)]
    pub fn nop() -> Instruction {
        Instruction::I(IInstruction {
            op: IInstructionOp::Addi,
            imm: Immediate::new(0),
            rs1: Register::zero(),
            rd: Register::zero(),
        })
    }

    // Frequently used instructions

    /// Store `rs2` to `mem[rs1 + imm]`
    pub fn sw(rs2: Register, rs1: Register, imm: Immediate) -> Instruction {
        Instruction::S(SInstruction {
            op: SInstructionOp::Sw,
            rs1,
            rs2,
            imm,
        })
    }

    /// Load `mem[rs1 + imm]` to `rd`
    pub fn lw(rd: Register, rs1: Register, imm: Immediate) -> Instruction {
        Instruction::I(IInstruction {
            op: IInstructionOp::Lw,
            rs1,
            rd,
            imm,
        })
    }

    pub fn addi(rd: Register, rs1: Register, imm: i32) -> Instruction {
        Instruction::I(IInstruction {
            op: IInstructionOp::Addi,
            rs1,
            rd,
            imm: Immediate::for_i(imm),
        })
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Instruction::*;
        match self {
            R(ri) => write!(f, "{}", ri.generate_asm()),
            I(ii) => write!(f, "{}", ii.generate_asm()),
            S(si) => write!(f, "{}", si.generate_asm()),
            J(ji) => write!(f, "{}", ji.generate_asm()),
            U(ui) => write!(f, "{}", ui.generate_asm()),
            SB(sbi) => write!(f, "{}", sbi.generate_asm()),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct RInstruction {
    pub op: RInstructionOp,
    pub rs1: Register,
    pub rs2: Register,
    pub rd: Register,
}

#[derive(Clone, PartialEq, Debug)]
pub enum RInstructionOp {
    Add,
    Sub,
    Or,
    ShiftLeft,
    ShiftRight,
    /// Set Less Than
    Slt,

    Mul,
    Div,
}

#[derive(Clone, PartialEq, Debug)]
pub struct IInstruction {
    pub op: IInstructionOp,
    pub imm: Immediate,
    pub rs1: Register,
    pub rd: Register,
}

impl IInstruction {
    pub fn is_nop(&self) -> bool {
        self.op == IInstructionOp::Addi
            && self.imm.value() == 0
            && self.rs1.is_zero()
            && self.rd.is_zero()
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum IInstructionOp {
    Ori,
    Addi,
    Jalr,
    Ecall,
    /// Load Word
    Lw,
    /// Load Byte
    Lb,
    Xori,
    /// Set Less Than Immediate
    Slti,
}

#[derive(Clone, PartialEq, Debug)]
pub struct SInstruction {
    pub op: SInstructionOp,
    pub imm: Immediate,
    pub rs1: Register,
    pub rs2: Register,
}

#[derive(Clone, PartialEq, Debug)]
pub enum SInstructionOp {
    /// Store Word
    Sw,
    /// Store Byte
    Sb,
}

#[derive(Clone, PartialEq, Debug)]
pub struct JInstruction {
    pub op: JInstructionOp,
    pub imm: RelAddress,
    pub rd: Register,
}

#[derive(Clone, PartialEq, Debug)]
pub enum JInstructionOp {
    Jal,
}

#[derive(Clone, PartialEq, Debug)]
pub struct UInstruction {
    pub op: UInstructionOp,
    pub imm: Immediate,
    pub rd: Register,
}

#[derive(Clone, PartialEq, Debug)]
pub enum UInstructionOp {
    Lui,
}

#[derive(Clone, PartialEq, Debug)]
pub struct SBInstruction {
    pub op: SBInstructionOp,
    pub imm: RelAddress,
    pub rs1: Register,
    pub rs2: Register,
}

#[derive(Clone, PartialEq, Debug)]
pub enum SBInstructionOp {
    /// Branch EQual
    #[allow(dead_code)]
    Beq,
    /// Branch Not Equal
    Bne,
}

pub trait GenerateCode {
    fn generate_code(&self) -> RegisterType;
    fn generate_asm(&self) -> String;
}

impl GenerateCode for RInstruction {
    fn generate_code(&self) -> RegisterType {
        use RInstructionOp::*;

        let rs2 = self.rs2.as_int();
        let rs1 = self.rs1.as_int();
        let rd = self.rd.as_int();

        let (funct7, funct3, opcode) = match self.op {
            Add => (0b0000000, 0b000, 0b0110011),
            Sub => (0b0100000, 0b000, 0b0110011),
            Or => (0b0000000, 0b110, 0b0110011),
            ShiftLeft => (0b0000000, 0b001, 0b0110011),
            ShiftRight => (0b0000000, 0b101, 0b0110011),
            Slt => (0b0000000, 0b010, 0b0110011),
            Mul => (0b0000001, 0b000, 0b0110011),
            Div => (0b0000001, 0b100, 0b0110011),
        };

        (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode
    }

    fn generate_asm(&self) -> String {
        use RInstructionOp::*;

        let name = match self.op {
            Add => "add",
            Sub => "sub",
            Or => "or",
            ShiftLeft => "sll",
            ShiftRight => "srl",
            Slt => "slt",
            Mul => "mul",
            Div => "div",
        };

        format!("{} {}, {}, {}", name, self.rd, self.rs1, self.rs2)
    }
}

impl GenerateCode for IInstruction {
    fn generate_code(&self) -> RegisterType {
        use IInstructionOp::*;

        assert!(
            (self.imm.value() & !0xfff) == 0,
            "Immediate of IInstruction must be under 0x1000. But the value is 0x{:x}.",
            self.imm.value()
        );

        let imm = (self.imm.value() as u32) & 0xfff;
        let rs1 = self.rs1.as_int();

        let (funct3, opcode) = match self.op {
            Ori => (0b110, 0b0010011),
            Addi => (0b000, 0b0010011),
            Jalr => (0b000, 0b1100111),
            Ecall => (0b000, 0b1110011),
            Lw => (0b010, 0b0000011),
            Lb => (0b000, 0b0000011),
            Xori => (0b100, 0b0010011),
            Slti => (0b010, 0b0010011),
        };

        let rd = self.rd.as_int();

        (imm << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode
    }

    fn generate_asm(&self) -> String {
        use IInstructionOp::*;

        if self.is_nop() {
            return "nop".to_string();
        }

        match self.op {
            Ori | Addi | Jalr | Xori | Slti => {
                let mut imm = self.imm.value();
                if imm >> 11 & 1 == 1 {
                    // sign extension
                    imm |= 0xffff_f000u32 as i32;
                }
                let name = match self.op {
                    Ori => "ori",
                    Addi => "addi",
                    Jalr => "jalr",
                    Xori => "xori",
                    Slti => "slti",
                    _ => "BUG",
                };
                format!("{} {}, {}, {}", name, self.rd, self.rs1, imm)
            }
            Ecall => "ecall".to_string(),
            Lw => {
                format!("lw {}, {}({})", self.rd, self.imm, self.rs1)
            }
            Lb => {
                format!("lb {}, {}({})", self.rd, self.imm, self.rs1)
            }
        }
    }
}

impl GenerateCode for SInstruction {
    fn generate_code(&self) -> RegisterType {
        use SInstructionOp::*;

        let rs1 = self.rs1.as_int();
        let rs2 = self.rs2.as_int();

        let imm = self.imm.uvalue();
        let imm1 = (imm >> 5) & 0b111_1111;
        let imm2 = imm & 0b1_1111;

        let (funct3, opcode) = match self.op {
            Sw => (0b010, 0b0100011),
            Sb => (0b000, 0b0100011),
        };

        (imm1 << 24) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (imm2 << 7) | opcode
    }

    fn generate_asm(&self) -> String {
        use SInstructionOp::*;

        let name = match self.op {
            Sw => "sw",
            Sb => "sb",
        };

        format!("{} {}, {}({})", name, self.rs2, self.imm, self.rs1)
    }
}

impl GenerateCode for JInstruction {
    fn generate_code(&self) -> RegisterType {
        use JInstructionOp::*;

        let imm = self.imm.value();

        assert!(imm & 1 == 0);
        let imm = imm >> 1;

        let imm = (imm & (0b1 << 19))
            | ((imm & 0b1111_1111_11) << 9)
            | (imm & (0b1 << 10) >> 2)
            | ((imm & (0b1111_1111 << 11)) >> 11);

        let rd = self.rd.as_int();

        let opcode = match self.op {
            Jal => 0b1101111,
        };

        (imm << 12) | (rd << 7) | opcode
    }

    fn generate_asm(&self) -> String {
        use JInstructionOp::*;

        match self.op {
            Jal => {
                format!("jal {}, {}", self.rd, self.imm)
            }
        }
    }
}

impl GenerateCode for UInstruction {
    fn generate_code(&self) -> RegisterType {
        use UInstructionOp::*;

        let imm = self.imm.uvalue() & 0xfffff000;
        let rd = self.rd.as_int();

        let opcode = match self.op {
            Lui => 0b0110111,
        };

        imm | (rd << 7) | opcode
    }

    fn generate_asm(&self) -> String {
        use UInstructionOp::*;

        match self.op {
            Lui => {
                let imm = self.imm.uvalue() & 0xfffff000;
                format!("lui {}, {}", self.rd, imm >> 12)
            }
        }
    }
}

impl GenerateCode for SBInstruction {
    fn generate_code(&self) -> RegisterType {
        use SBInstructionOp::*;

        let imm = self.imm.value();
        assert!(imm & 1 == 0);
        // 7 bits
        let imm_upper = ((imm & (1 << 12)) >> 5) | ((imm >> 5) & 0b11111);
        // 5 bits
        let imm_lower = (imm & 0b11110) | ((imm >> 11) & 1);

        let rs1 = self.rs1.as_int();
        let rs2 = self.rs2.as_int();

        let (opcode, funct3) = match self.op {
            Beq => (0b1100011, 0b000),
            Bne => (0b1100011, 0b001),
        };

        (imm_upper << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (imm_lower << 7) | opcode
    }

    fn generate_asm(&self) -> String {
        use SBInstructionOp::*;

        let name = match self.op {
            Beq => "beq",
            Bne => "bne",
        };
        format!("{} {}, {}, {}", name, self.rs1, self.rs2, self.imm)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum RelAddress {
    Label(i::Label),
    Immediate(Immediate),
}

impl RelAddress {
    fn value(&self) -> RegisterType {
        match self {
            RelAddress::Label(_) => unimplemented!(),
            RelAddress::Immediate(imm) => imm.uvalue(),
        }
    }
}

impl Display for RelAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RelAddress::Label(label) => write!(f, "{}", label),
            RelAddress::Immediate(imm) => write!(f, "{}", imm.value()),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Register {
    Integer(u32),
    #[allow(dead_code)]
    Float(u32),
}

impl Register {
    pub fn zero() -> Register {
        Register::Integer(0)
    }

    pub fn is_zero(&self) -> bool {
        self.as_int() == 0
    }

    pub fn ra() -> Register {
        Register::Integer(1)
    }

    pub fn sp() -> Register {
        Register::Integer(2)
    }

    #[allow(dead_code)]
    pub fn gp() -> Register {
        Register::Integer(3)
    }

    #[allow(dead_code)]
    pub fn tp() -> Register {
        Register::Integer(4)
    }

    pub fn t(i: u32) -> Register {
        match i {
            0..=2 => Register::Integer(5 + i),
            3.. => Register::Integer(28 - 3 + i),
        }
    }

    #[allow(dead_code)]
    pub fn fp() -> Register {
        Self::s(0)
    }

    pub fn s(i: u32) -> Register {
        match i {
            0 | 1 => Register::Integer(8 + i),
            2.. => Register::Integer(18 - 2 + i),
        }
    }

    pub fn a(i: u32) -> Register {
        Register::Integer(10 + i)
    }

    pub fn as_int(&self) -> u32 {
        if let Register::Integer(i) = self {
            if i >= &32u32 {
                panic!("Register #{} is invalid!", *i)
            } else {
                *i
            }
        } else {
            panic!("Register {} is invalid!", self)
        }
    }
}

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Register::Integer(i) => match i {
                0 => write!(f, "zero"),
                1 => write!(f, "ra"),
                2 => write!(f, "sp"),
                3 => write!(f, "gp"),
                4 => write!(f, "tp"),
                5..=7 => write!(f, "t{}", i - 5),
                8 => write!(f, "s0"),
                9 => write!(f, "s1"),
                10..=17 => write!(f, "a{}", i - 10),
                18..=27 => write!(f, "s{}", i - 16),
                28..=31 => write!(f, "t{}", i - 25),
                _ => write!(f, "(invalid register {})", i),
            },
            Register::Float(i) => {
                write!(f, "f{}", i)
            }
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Immediate {
    Value(i32),
    Label(Label),
}

impl Immediate {
    pub fn new(value: i32) -> Immediate {
        Immediate::Value(value)
    }

    pub fn value(&self) -> i32 {
        match self {
            Immediate::Value(value) => *value,
            Immediate::Label(_) => todo!(),
        }
    }

    pub fn uvalue(&self) -> u32 {
        self.value() as u32
    }

    /// Create an immediate for I-instruction.
    pub fn for_i(value: i32) -> Self {
        Self::new(value & 0xfff)
    }
}

impl ops::MulAssign<i32> for Immediate {
    fn mul_assign(&mut self, rhs: i32) {
        match self {
            Immediate::Value(value) => {
                *value *= rhs;
            }
            Immediate::Label(_) => todo!(),
        }
    }
}

impl Display for Immediate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value())
    }
}

impl From<i::Immediate> for Immediate {
    fn from(imm: i::Immediate) -> Self {
        use i::Immediate::*;
        match imm {
            Integer(v) => Immediate::new(v),
            Boolean(v) => Immediate::new(v as i32),
            Label(label) => Immediate::Label(label),
        }
    }
}
