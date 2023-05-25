use std::fmt::Display;

use anyhow::Result;
use colored::*;
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{bug, lispi::ir::register_allocation::RegisterMap};

use super::{
    cli_option::CliOption,
    error::*,
    ir::{instruction as i, register_allocation as ra, IrContext},
};

type RegisterType = u32;
const XLEN: u8 = 32;

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

#[derive(Clone, PartialEq, Debug)]
enum RelAddress {
    Label(i::Label),
    Immediate(Immediate),
}

impl RelAddress {
    fn value(&self) -> RegisterType {
        match self {
            RelAddress::Label(_) => unimplemented!(),
            RelAddress::Immediate(imm) => imm.value as RegisterType,
        }
    }
}

impl Display for RelAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RelAddress::Label(label) => write!(f, "{}", label),
            RelAddress::Immediate(imm) => write!(f, "{}", imm.value),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
enum Register {
    Integer(u32),
    #[allow(dead_code)]
    Float(u32),
}

impl Register {
    fn zero() -> Register {
        Register::Integer(0)
    }

    fn is_zero(&self) -> bool {
        self.as_int() == 0
    }

    fn ra() -> Register {
        Register::Integer(1)
    }

    fn sp() -> Register {
        Register::Integer(2)
    }

    #[allow(dead_code)]
    fn gp() -> Register {
        Register::Integer(3)
    }

    #[allow(dead_code)]
    fn tp() -> Register {
        Register::Integer(4)
    }

    fn t(i: u32) -> Register {
        match i {
            0..=2 => Register::Integer(5 + i),
            3.. => Register::Integer(28 - 3 + i),
        }
    }

    #[allow(dead_code)]
    fn fp() -> Register {
        Self::s(0)
    }

    fn s(i: u32) -> Register {
        match i {
            0 | 1 => Register::Integer(8 + i),
            2.. => Register::Integer(18 - 2 + i),
        }
    }

    fn a(i: u32) -> Register {
        Register::Integer(10 + i)
    }

    fn as_int(&self) -> u32 {
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
struct Immediate {
    value: i32,
    /// Length in bits
    len: u8,
}

impl Immediate {
    fn new(value: i32, len: u8) -> Immediate {
        Immediate { value, len }
    }
}

impl Display for Immediate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl From<i::Immediate> for Immediate {
    fn from(imm: i::Immediate) -> Self {
        use i::Immediate::*;
        match imm {
            Integer(v) => Immediate::new(v, XLEN),
            Boolean(v) => Immediate::new(v as i32, 1),
            Label(_) => todo!(),
        }
    }
}

struct Context {
    arg_reg_map: FxHashMap<String, Register>,
    arg_count: u32,

    label_addrs: FxHashMap<String, i32>,
}

impl Context {
    fn new() -> Context {
        Context {
            arg_reg_map: FxHashMap::default(),
            arg_count: 0,
            label_addrs: FxHashMap::default(),
        }
    }

    fn reset_on_fun(&mut self) {
        self.arg_reg_map.clear();
        self.arg_count = 0;
    }

    fn allocate_arg_reg(&mut self) -> Register {
        let reg = Register::a(self.arg_count);
        self.arg_count += 1;
        reg
    }
}

type Code = u32;
type Codes = Vec<Code>;

fn dump_instructions(ctx: &mut Context, insts: &[Instruction]) {
    println!("{}", "RISC-V Instructions:".red());
    for (addr, inst) in insts.iter().enumerate() {
        let label = ctx.label_addrs.iter().find_map(|(label, laddr)| {
            if *laddr == addr as i32 {
                Some(label)
            } else {
                None
            }
        });
        if let Some(label) = label {
            let addr = format!("; 0x{:x}", addr * 4);
            println!("{}: {}", label, addr.dimmed());
        }
        println!("  {}", inst);
    }
    println!();
}

fn load_operand(
    ctx: &mut Context,
    _insts: &mut [Instruction],
    register_map: &RegisterMap,
    op: i::Operand,
) -> Result<Register> {
    match op {
        i::Operand::Variable(var) => {
            if let Some(reg) = register_map.get(&var) {
                Ok(Register::t(*reg as u32))
            } else if let Some(reg) = ctx.arg_reg_map.get(&var.name) {
                Ok(reg.clone())
            } else {
                Err(bug!(format!(
                    "A register corresponded to a variable {} is not defined.",
                    var.name
                )))
            }
        }
        i::Operand::Immediate(imm) => Err(bug!(format!(
            "Cannot load immediate operand. This should be formed as `%var = {}.`",
            imm
        ))),
    }
}

fn load_operand_to(
    ctx: &mut Context,
    insts: &mut Vec<Instruction>,
    register_map: &RegisterMap,
    op: i::Operand,
    rd: Register,
) {
    match op {
        i::Operand::Variable(var) => {
            let reg = register_map
                .get(&var)
                .map(|&reg| Register::t(reg as u32))
                .or_else(|| ctx.arg_reg_map.get(&var.name).cloned())
                .unwrap();
            insts.push(Instruction::mv(rd, reg));
        }
        i::Operand::Immediate(imm) => {
            let imm: Immediate = imm.into();
            load_immediate(insts, imm, rd);
        }
    }
}

fn load_immediate(insts: &mut Vec<Instruction>, imm: Immediate, rd: Register) {
    let mut last_set_bit = -1;
    for i in (0..=31).rev() {
        if imm.value & (1 << i) != 0 {
            last_set_bit = i;
            break;
        }
    }
    if last_set_bit >= 12 {
        // Large integer
        let bot = Immediate::new(imm.value & 0xfff, 12);
        let top = if (bot.value >> 11 & 1) == 1 {
            Immediate::new(imm.value + 0x1000, imm.len)
        } else {
            imm
        };
        insts.push(Instruction::U(UInstruction {
            op: UInstructionOp::Lui,
            imm: top,
            rd: rd.clone(),
        }));
        if bot.value > 0 {
            insts.push(Instruction::addi(rd.clone(), rd, bot));
        }
    } else {
        insts.push(Instruction::li(rd, imm));
    }
}

fn generate_code_bin_op(
    ctx: &mut Context,
    insts: &mut Vec<Instruction>,
    register_map: &RegisterMap,
    left: i::Operand,
    right: i::Operand,
    op: RInstructionOp,
    opi: IInstructionOp,
    result_reg: Register,
) -> Result<()> {
    use i::Operand::*;
    use Instruction::*;

    let inst = match (left, right) {
        (Immediate(imm), var) | (var, Immediate(imm)) => {
            let rs1 = load_operand(ctx, insts, register_map, var)?;
            I(IInstruction {
                op: opi,
                imm: imm.into(),
                rs1,
                rd: result_reg,
            })
        }
        (left, right) => {
            let rs1 = load_operand(ctx, insts, register_map, left)?;
            let rs2 = load_operand(ctx, insts, register_map, right)?;

            R(RInstruction {
                op,
                rs1,
                rs2,
                rd: result_reg,
            })
        }
    };

    insts.push(inst);

    Ok(())
}

pub fn generate_code(
    funcs: Vec<(i::Function, ra::RegisterMap)>,
    ir_ctx: &mut IrContext,
    opt: &CliOption,
) -> Result<Codes> {
    fn load_argument(
        ctx: &mut Context,
        insts: &mut Vec<Instruction>,
        register_map: &RegisterMap,
        op: i::Operand,
    ) {
        let rd = ctx.allocate_arg_reg();
        load_operand_to(ctx, insts, register_map, op, rd);
    }

    fn add_label(ctx: &mut Context, insts: &mut Vec<Instruction>, label: String) {
        ctx.label_addrs.insert(label, insts.len() as i32);
    }

    fn add_fun_header(insts: &mut Vec<Instruction>, register_map: &RegisterMap) {
        let frame_size = 4 * (2 + register_map.values().unique().count() as i32);

        insts.push(Instruction::addi(
            Register::sp(),
            Register::sp(),
            Immediate::new(-frame_size & 0xfff, XLEN),
        ));
        insts.push(Instruction::sw(
            Register::ra(),
            Register::sp(),
            Immediate::new(0, XLEN),
        ));
        insts.push(Instruction::sw(
            Register::s(0),
            Register::sp(),
            Immediate::new(4, XLEN),
        ));

        insts.push(Instruction::addi(
            Register::s(0),
            Register::sp(),
            Immediate::new(8, XLEN),
        ));
    }

    fn add_fun_footer(insts: &mut Vec<Instruction>, register_map: &RegisterMap) {
        let frame_size = 4 * (2 + register_map.values().unique().count() as i32);

        insts.push(Instruction::lw(
            Register::ra(),
            Register::sp(),
            Immediate::new(0, XLEN),
        ));
        insts.push(Instruction::lw(
            Register::s(0),
            Register::sp(),
            Immediate::new(4, XLEN),
        ));
        insts.push(Instruction::addi(
            Register::sp(),
            Register::sp(),
            Immediate::new(frame_size, XLEN),
        ));
    }

    use Instruction::*;

    let mut ctx = Context::new();
    let mut insts = Vec::new();

    // Initialize specific registers
    load_immediate(
        &mut insts,
        Immediate::new(0x80000000u32 as i32, XLEN),
        Register::sp(),
    );

    for (fun, register_map) in funcs {
        ctx.reset_on_fun();

        for (i, (arg, _)) in fun.args.iter().enumerate() {
            ctx.arg_reg_map.insert(arg.clone(), Register::a(i as u32));
        }

        for (bbi, bb) in fun.basic_blocks.into_iter().enumerate() {
            let bb = ir_ctx.bb_arena.get(bb).unwrap();

            add_label(&mut ctx, &mut insts, bb.label.clone());

            if bbi == 0 {
                add_fun_header(&mut insts, &register_map);
            }

            for i::AnnotatedInstr {
                result,
                inst,
                ty: _,
                tags: _,
            } in bb.insts.clone()
            {
                use i::Instruction::*;

                let result_reg = if !inst.is_terminal() {
                    if let Some(&reg) = register_map.get(&result) {
                        Register::t(reg as u32)
                    } else {
                        Register::zero()
                    }
                } else {
                    Register::zero()
                };

                match inst {
                    Branch {
                        cond,
                        then_label,
                        else_label,
                        then_bb: _,
                        else_bb: _,
                    } => {
                        let cond = load_operand(&mut ctx, &mut insts, &register_map, cond)?;
                        insts.push(SB(SBInstruction {
                            op: SBInstructionOp::Bne,
                            imm: RelAddress::Label(then_label),
                            rs1: cond,
                            rs2: Register::zero(),
                        }));
                        insts.push(J(JInstruction {
                            op: JInstructionOp::Jal,
                            imm: RelAddress::Label(else_label),
                            rd: Register::zero(),
                        }));
                    }
                    Jump(label, _) => {
                        insts.push(J(JInstruction {
                            op: JInstructionOp::Jal,
                            imm: RelAddress::Label(label),
                            rd: Register::zero(),
                        }));
                    }
                    Ret(op) => {
                        load_operand_to(&mut ctx, &mut insts, &register_map, op, Register::a(0));

                        if fun.name == "main" {
                            // syscall EXIT on rv32emu
                            // insts.push(Instruction::li(Register::a(0), Immediate::new(0, XLEN)));
                            insts.push(Instruction::li(Register::a(7), Immediate::new(93, XLEN)));
                            insts.push(I(IInstruction {
                                op: IInstructionOp::Ecall,
                                imm: Immediate::new(0, XLEN),
                                rs1: Register::zero(),
                                rd: Register::zero(),
                            }));
                        } else {
                            add_fun_footer(&mut insts, &register_map);

                            insts.push(Instruction::ret());
                        }
                    }
                    Add(left, right) => {
                        generate_code_bin_op(
                            &mut ctx,
                            &mut insts,
                            &register_map,
                            left,
                            right,
                            RInstructionOp::Add,
                            IInstructionOp::Addi,
                            result_reg,
                        )?;
                    }
                    Sub(_, _) => todo!(),
                    Mul(_, _) => todo!(),
                    Or(left, right) => {
                        generate_code_bin_op(
                            &mut ctx,
                            &mut insts,
                            &register_map,
                            left,
                            right,
                            RInstructionOp::Or,
                            IInstructionOp::Ori,
                            result_reg,
                        )?;
                    }
                    Not(op) => {
                        let op = load_operand(&mut ctx, &mut insts, &register_map, op)?;
                        insts.push(I(IInstruction {
                            op: IInstructionOp::Xori,
                            // imm: Immediate::new(0xfffu32 as i32, XLEN),
                            imm: Immediate::new(0x1u32 as i32, XLEN),
                            rs1: op,
                            rd: result_reg,
                        }))
                    }
                    Shift(op, left, right) => {
                        let rs1 = load_operand(&mut ctx, &mut insts, &register_map, left)?;
                        let rs2 = load_operand(&mut ctx, &mut insts, &register_map, right)?;

                        let op = match op {
                            i::ShiftOperator::LogicalLeft => RInstructionOp::ShiftLeft,
                            i::ShiftOperator::LogicalRight => RInstructionOp::ShiftRight,
                        };

                        insts.push(R(RInstruction {
                            op,
                            rs1,
                            rs2,
                            rd: result_reg,
                        }))
                    }
                    Store(addr, value) => {
                        let rs1 = load_operand(&mut ctx, &mut insts, &register_map, addr)?;
                        let rs2 = load_operand(&mut ctx, &mut insts, &register_map, value)?;

                        insts.push(S(SInstruction {
                            op: SInstructionOp::Sw,
                            imm: Immediate::new(0, XLEN),
                            rs1,
                            rs2,
                        }))
                    }
                    Cmp(op, left, right) => {
                        let (inst_op, inst_opi) = match op {
                            i::CmpOperator::SGE => todo!(),
                            i::CmpOperator::SGT => todo!(),
                            i::CmpOperator::SLT => (RInstructionOp::Slt, IInstructionOp::Slti),
                        };

                        generate_code_bin_op(
                            &mut ctx,
                            &mut insts,
                            &register_map,
                            left,
                            right,
                            inst_op,
                            inst_opi,
                            result_reg,
                        )?;
                    }
                    Call { fun, args } => {
                        ctx.arg_count = 0;
                        for arg in args {
                            load_argument(&mut ctx, &mut insts, &register_map, arg);
                        }

                        // Save caller-saved registers
                        // Now only for temporary registers
                        let used_regs = register_map
                            .values()
                            .unique()
                            .map(|id| Register::t(*id as u32))
                            .collect_vec();

                        for (i, reg) in used_regs.iter().enumerate() {
                            insts.push(Instruction::sw(
                                reg.clone(),
                                Register::sp(),
                                Immediate::new((i as i32 + 2) * 4, XLEN),
                            ));
                        }

                        if let i::Operand::Immediate(i::Immediate::Label(label)) = fun {
                            insts.push(J(JInstruction {
                                op: JInstructionOp::Jal,
                                imm: RelAddress::Label(label),
                                rd: Register::ra(),
                            }));
                        } else {
                            todo!()
                        }

                        // Load caller-saved registers
                        for (i, reg) in used_regs.iter().enumerate() {
                            insts.push(Instruction::lw(
                                reg.clone(),
                                Register::sp(),
                                Immediate::new((i as i32 + 2) * 4, XLEN),
                            ));
                        }

                        insts.push(Instruction::mv(result_reg, Register::a(0)));
                    }
                    Phi(_nodes) => {}
                    Operand(op) => {
                        load_operand_to(&mut ctx, &mut insts, &register_map, op, result_reg);
                    }
                    Label(label) => {
                        add_label(&mut ctx, &mut insts, label.name);
                    }
                    Nop => {}
                }
            }
        }
    }

    // Resolving label addresses

    let insts = insts
        .into_iter()
        .enumerate()
        .map(|(addr, inst)| {
            let addr = addr as i32;
            match inst {
                J(JInstruction {
                    op: op @ JInstructionOp::Jal,
                    imm: RelAddress::Label(label),
                    rd,
                }) => {
                    let laddr = *ctx.label_addrs.get(&label.name).unwrap();

                    J(JInstruction {
                        op,
                        imm: RelAddress::Immediate(Immediate::new((laddr - addr) * 4, 20)),
                        rd,
                    })
                }
                SB(SBInstruction {
                    op,
                    imm: RelAddress::Label(label),
                    rs1,
                    rs2,
                }) => {
                    let laddr = *ctx.label_addrs.get(&label.name).unwrap();

                    SB(SBInstruction {
                        op,
                        imm: RelAddress::Immediate(Immediate::new((laddr - addr) * 4, 12)),
                        rs1,
                        rs2,
                    })
                }
                _ => inst,
            }
        })
        .collect::<Vec<Instruction>>();

    if opt.dump {
        dump_instructions(&mut ctx, &insts);
    }

    let asm = insts
        .iter()
        .map(|inst| match inst {
            R(ri) => ri.generate_asm(),
            I(ii) => ii.generate_asm(),
            S(si) => si.generate_asm(),
            J(ji) => ji.generate_asm(),
            U(ui) => ui.generate_asm(),
            SB(sbi) => sbi.generate_asm(),
        })
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write("out.s", asm)?;

    let result = insts
        .into_iter()
        .map(|inst| match inst {
            R(ri) => ri.generate_code(),
            I(ii) => ii.generate_code(),
            S(si) => si.generate_code(),
            J(ji) => ji.generate_code(),
            U(ui) => ui.generate_code(),
            SB(sbi) => sbi.generate_code(),
        })
        .collect();

    Ok(result)
}
