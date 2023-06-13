#[derive(Clone, PartialEq, Debug)]
enum Instruction {
    R(RInstruction),
    I(IInstruction),
    S(SInstruction),
    J(JInstruction),
    U(UInstruction),
    SB(SBInstruction),
}

impl Instruction {
    // Pseudo instructions

    fn mv(rd: Register, rs1: Register) -> Instruction {
        Instruction::R(RInstruction {
            op: RInstructionOp::Add,
            rs1,
            rs2: Register::zero(),
            rd,
        })
    }

    fn li(rd: Register, imm: Immediate) -> Instruction {
        Instruction::I(IInstruction {
            op: IInstructionOp::Addi,
            imm,
            rs1: Register::zero(),
            rd,
        })
    }

    fn ret() -> Instruction {
        Instruction::I(IInstruction {
            op: IInstructionOp::Jalr,
            imm: Immediate::new(0, XLEN),
            rs1: Register::ra(),
            rd: Register::zero(),
        })
    }

    #[allow(dead_code)]
    fn nop() -> Instruction {
        Instruction::I(IInstruction {
            op: IInstructionOp::Addi,
            imm: Immediate::new(0, XLEN),
            rs1: Register::zero(),
            rd: Register::zero(),
        })
    }

    // Frequently used instructions

    /// Store `rs2` to `mem[rs1 + imm]`
    fn sw(rs2: Register, rs1: Register, imm: Immediate) -> Instruction {
        Instruction::S(SInstruction {
            op: SInstructionOp::Sw,
            rs1,
            rs2,
            imm,
        })
    }

    /// Load `mem[rs1 + imm]` to `rd`
    fn lw(rd: Register, rs1: Register, imm: Immediate) -> Instruction {
        Instruction::I(IInstruction {
            op: IInstructionOp::Lw,
            rs1,
            rd,
            imm,
        })
    }

    fn addi(rd: Register, rs1: Register, imm: Immediate) -> Instruction {
        Instruction::I(IInstruction {
            op: IInstructionOp::Addi,
            rs1,
            rd,
            imm,
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
struct RInstruction {
    op: RInstructionOp,
    rs1: Register,
    rs2: Register,
    rd: Register,
}

#[derive(Clone, PartialEq, Debug)]
enum RInstructionOp {
    Add,
    Sub,
    Or,
    ShiftLeft,
    ShiftRight,
    /// Set Less Than
    Slt,
}

#[derive(Clone, PartialEq, Debug)]
struct IInstruction {
    op: IInstructionOp,
    imm: Immediate,
    rs1: Register,
    rd: Register,
}

impl IInstruction {
    fn is_nop(&self) -> bool {
        self.op == IInstructionOp::Addi
            && self.imm.value == 0
            && self.rs1.is_zero()
            && self.rd.is_zero()
    }
}

#[derive(Clone, PartialEq, Debug)]
enum IInstructionOp {
    Ori,
    Addi,
    Jalr,
    Ecall,
    Lw,
    Xori,
    /// Set Less Than Immediate
    Slti,
}

#[derive(Clone, PartialEq, Debug)]
struct SInstruction {
    op: SInstructionOp,
    imm: Immediate,
    rs1: Register,
    rs2: Register,
}

#[derive(Clone, PartialEq, Debug)]
enum SInstructionOp {
    /// Store Word
    Sw,
}

#[derive(Clone, PartialEq, Debug)]
struct JInstruction {
    op: JInstructionOp,
    imm: RelAddress,
    rd: Register,
}

#[derive(Clone, PartialEq, Debug)]
enum JInstructionOp {
    Jal,
}

#[derive(Clone, PartialEq, Debug)]
struct UInstruction {
    op: UInstructionOp,
    imm: Immediate,
    rd: Register,
}

#[derive(Clone, PartialEq, Debug)]
enum UInstructionOp {
    Lui,
}

#[derive(Clone, PartialEq, Debug)]
struct SBInstruction {
    op: SBInstructionOp,
    imm: RelAddress,
    rs1: Register,
    rs2: Register,
}

#[derive(Clone, PartialEq, Debug)]
enum SBInstructionOp {
    /// Branch EQual
    #[allow(dead_code)]
    Beq,
    /// Branch Not Equal
    Bne,
}

trait GenerateCode {
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
        };

        format!("{} {}, {}, {}", name, self.rd, self.rs1, self.rs2)
    }
}

impl GenerateCode for IInstruction {
    fn generate_code(&self) -> RegisterType {
        use IInstructionOp::*;

        assert!(
            (self.imm.value & !0xfff) == 0,
            "Immediate of IInstruction must be under 0x1000. But the value is 0x{:x}.",
            self.imm.value
        );

        let imm = (self.imm.value as u32) & 0xfff;
        let rs1 = self.rs1.as_int();

        let (funct3, opcode) = match self.op {
            Ori => (0b110, 0b0010011),
            Addi => (0b000, 0b0010011),
            Jalr => (0b000, 0b1100111),
            Ecall => (0b000, 0b1110011),
            Lw => (0b010, 0b0000011),
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
                let mut imm = self.imm.value;
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
        }
    }
}

impl GenerateCode for SInstruction {
    fn generate_code(&self) -> RegisterType {
        use SInstructionOp::*;

        let rs1 = self.rs1.as_int();
        let rs2 = self.rs2.as_int();

        let imm = self.imm.value as u32;
        let imm1 = (imm >> 5) & 0b111_1111;
        let imm2 = imm & 0b1_1111;

        let (funct3, opcode) = match self.op {
            Sw => (0b010, 0b0100011),
        };

        (imm1 << 24) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (imm2 << 7) | opcode
    }

    fn generate_asm(&self) -> String {
        use SInstructionOp::*;

        match self.op {
            Sw => {
                format!("sw {}, {}({})", self.rs2, self.imm, self.rs1)
            }
        }
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

        let imm = self.imm.value as u32 & 0xfffff000;
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
                let imm = self.imm.value as u32 & 0xfffff000;
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
