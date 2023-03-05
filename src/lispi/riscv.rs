use std::{fmt::Display, fs::File, io::Write};

use anyhow::Result;
use rustc_hash::FxHashMap;

use crate::lispi::{console::printlnuw, ir::register_allocation::RegisterMap};

use super::{
    cli_option::CliOption,
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

    fn nop() -> Instruction {
        Instruction::I(IInstruction {
            op: IInstructionOp::Addi,
            imm: Immediate::new(0, XLEN),
            rs1: Register::zero(),
            rd: Register::zero(),
        })
    }

    // Frequently used instructions

    fn sw(rs2: Register, rs1: Register, imm: Immediate) -> Instruction {
        Instruction::S(SInstruction {
            op: SInstructionOp::Sw,
            rs1,
            rs2,
            imm,
        })
    }

    fn lw(rs1: Register, rd: Register, imm: Immediate) -> Instruction {
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
            R(ri) => write!(f, "{:?} {} {} {}", ri.op, ri.rd, ri.rs1, ri.rs2),
            I(ii) => {
                if ii.is_nop() {
                    write!(f, "Nop")
                } else {
                    write!(f, "{:?} {} {} {}", ii.op, ii.rd, ii.rs1, ii.imm)
                }
            }
            S(si) => write!(f, "{:?} {} {} {}", si.op, si.rs1, si.imm, si.rs2),
            J(ji) => write!(f, "{:?} {} {}", ji.op, ji.rd, ji.imm),
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
        };

        format!("{} {}, {}, {}", name, self.rd, self.rs1, self.rs2)
    }
}

impl GenerateCode for IInstruction {
    fn generate_code(&self) -> RegisterType {
        use IInstructionOp::*;

        let imm = (self.imm.value as u32) & 0xfff;
        let rs1 = self.rs1.as_int();

        let (funct3, opcode) = match self.op {
            Ori => (0b110, 0b0010011),
            Addi => (0b000, 0b0010011),
            Jalr => (0b000, 0b1100111),
            Ecall => (0b000, 0b1110011),
            Lw => (0b010, 0b0000011),
        };

        let rd = self.rd.as_int();

        (imm << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode
    }

    fn generate_asm(&self) -> String {
        use IInstructionOp::*;

        match self.op {
            Ori | Addi => {
                let name = if self.op == Ori { "ori" } else { "addi" };
                format!("{} {}, {}, {}", name, self.rd, self.rs1, self.imm)
            }
            Jalr => "jalr".to_string(),
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
            | (imm & 0b1111_1111_11) << 9
            | (imm & (0b1 << 8))
            | (imm & 0b1111_1111) >> 9;

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
enum JInstructionOp {
    Jal,
}

#[derive(Clone, PartialEq, Debug)]
enum Register {
    Integer(u32),
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

    fn gp() -> Register {
        Register::Integer(3)
    }

    fn tp() -> Register {
        Register::Integer(4)
    }

    fn t(i: u32) -> Register {
        match i {
            0..=2 => Register::Integer(5 + i),
            3.. => Register::Integer(28 - 3 + i),
        }
    }

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
    reg_map: FxHashMap<String, Register>,
    reg_count: u32,
    arg_count: u32,

    label_addrs: FxHashMap<String, i32>,
}

/// t3
const TEMP_REG_BASE: u32 = 28;

impl Context {
    fn new() -> Context {
        Context {
            reg_map: FxHashMap::default(),
            reg_count: TEMP_REG_BASE,
            arg_count: 0,
            label_addrs: FxHashMap::default(),
        }
    }

    fn reset_on_fun(&mut self) {
        self.reg_map.clear();
        self.reg_count = TEMP_REG_BASE;
        self.arg_count = 0;
    }

    fn allocate_reg(&mut self) -> Register {
        let reg = Register::Integer(self.reg_count);
        self.reg_count += 1;
        reg
    }

    fn allocate_arg_reg(&mut self) -> Register {
        let reg = Register::Integer(10 + self.arg_count);
        self.arg_count += 1;
        reg
    }
}

type Code = u32;
type Codes = Vec<Code>;

fn dump_instructions(ctx: &mut Context, insts: &[Instruction]) {
    println!("RISC-V Instructions:");
    for (addr, inst) in insts.iter().enumerate() {
        let label = ctx.label_addrs.iter().find_map(|(label, laddr)| {
            if *laddr == addr as i32 {
                Some(label)
            } else {
                None
            }
        });
        if let Some(label) = label {
            println!("{}:", label);
        }
        println!("  {}", inst);
    }
    println!();
}

fn load_operand(ctx: &mut Context, insts: &mut Vec<Instruction>, op: i::Operand) -> Register {
    match op {
        i::Operand::Variable(var) => ctx.reg_map.get(&var.name).unwrap().clone(),
        i::Operand::Immediate(imm) => {
            let rd = ctx.allocate_reg();
            insts.push(Instruction::li(rd.clone(), imm.into()));
            rd
        }
    }
}

fn generate_code_bin_op(
    ctx: &mut Context,
    insts: &mut Vec<Instruction>,
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
            let rs1 = load_operand(ctx, insts, var);
            I(IInstruction {
                op: opi,
                imm: imm.into(),
                rs1,
                rd: result_reg,
            })
        }
        (left, right) => {
            let rs1 = load_operand(ctx, insts, left);
            let rs2 = load_operand(ctx, insts, right);

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
                    .or_else(|| ctx.reg_map.get(&var.name).cloned())
                    .unwrap();
                insts.push(Instruction::mv(rd, reg));
            }
            i::Operand::Immediate(imm) => {
                insts.push(Instruction::li(rd, imm.into()));
            }
        }
    }

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

    fn add_fun_header(insts: &mut Vec<Instruction>) {
        insts.push(Instruction::addi(
            Register::sp(),
            Register::sp(),
            Immediate::new(-8, XLEN),
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

    fn add_fun_footer(insts: &mut Vec<Instruction>) {
        insts.push(Instruction::lw(
            Register::s(0),
            Register::sp(),
            Immediate::new(4, XLEN),
        ));
        insts.push(Instruction::lw(
            Register::s(0),
            Register::sp(),
            Immediate::new(4, XLEN),
        ));
        insts.push(Instruction::addi(
            Register::sp(),
            Register::sp(),
            Immediate::new(8, XLEN),
        ));
    }

    use Instruction::*;

    // Remove phi nodes
    for (fun, register_map) in &funcs {
        let i::Function {
            name: _,
            args: _,
            ty: _,
            basic_blocks,
        } = fun;

        let mut assign_map = FxHashMap::default();

        for bb in basic_blocks.iter().rev() {
            let bb = ir_ctx.bb_arena.get_mut(*bb).unwrap();

            let mut insts = Vec::new();
            insts.append(&mut bb.insts);

            let mut new_insts = Vec::new();

            for i::AnnotatedInstr { result, inst, ty } in insts {
                match &inst {
                    i::Instruction::Phi(nodes) => {
                        for (node, label) in nodes {
                            assign_map.insert(
                                label.name.clone(),
                                (result.clone(), ty.clone(), node.clone()),
                            );
                        }
                    }
                    _ => {
                        if inst.is_terminal() {
                            if let Some((result, ty, operand)) = assign_map.get(&bb.label) {
                                new_insts.push(i::AnnotatedInstr {
                                    result: result.clone(),
                                    inst: i::Instruction::Operand(operand.clone()),
                                    ty: ty.clone(),
                                });
                            }
                        }

                        new_insts.push(i::AnnotatedInstr { result, inst, ty });
                    }
                }
            }

            bb.insts = new_insts;
        }
    }

    if opt.dump {
        printlnuw("Remove phi nodes:");
        for (fun, _) in &funcs {
            fun.dump(&ir_ctx.bb_arena);
        }
    }

    let mut ctx = Context::new();
    let mut insts = Vec::new();

    for (fun, register_map) in funcs {
        ctx.reset_on_fun();

        for (i, (arg, _)) in fun.args.iter().enumerate() {
            ctx.reg_map.insert(arg.clone(), Register::a(i as u32));
        }

        for (bbi, bb) in fun.basic_blocks.into_iter().enumerate() {
            let bb = ir_ctx.bb_arena.get(bb).unwrap();

            add_label(&mut ctx, &mut insts, bb.label.clone());

            if bbi == 0 {
                add_fun_header(&mut insts);
            }

            for i::AnnotatedInstr {
                result,
                inst,
                ty: _,
            } in bb.insts.clone()
            {
                use i::Instruction::*;

                let result_reg = if !inst.is_terminal() {
                    if let Some(&reg) = register_map.get(&result) {
                        let reg = Register::t(reg as u32);
                        ctx.reg_map.insert(result.name, reg.clone());
                        reg
                    } else {
                        Register::zero()
                    }
                } else {
                    Register::zero()
                };

                match inst {
                    Branch {
                        cond: _,
                        then_label: _,
                        else_label: _,
                        ..
                    } => {}
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
                            add_fun_footer(&mut insts);

                            insts.push(Instruction::ret());
                        }
                    }
                    Add(left, right) => {
                        generate_code_bin_op(
                            &mut ctx,
                            &mut insts,
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
                            left,
                            right,
                            RInstructionOp::Or,
                            IInstructionOp::Ori,
                            result_reg,
                        )?;
                    }
                    Shift(op, left, right) => {
                        let rs1 = load_operand(&mut ctx, &mut insts, left);
                        let rs2 = load_operand(&mut ctx, &mut insts, right);

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
                        let rs1 = load_operand(&mut ctx, &mut insts, addr);
                        let rs2 = load_operand(&mut ctx, &mut insts, value);

                        insts.push(S(SInstruction {
                            op: SInstructionOp::Sw,
                            imm: Immediate::new(0, XLEN),
                            rs1,
                            rs2,
                        }))
                    }
                    Cmp(_, _, _) => todo!(),
                    Call { fun, args } => {
                        for arg in args {
                            load_argument(&mut ctx, &mut insts, &register_map, arg);
                        }
                        if let i::Operand::Immediate(i::Immediate::Label(label)) = fun {
                            insts.push(J(JInstruction {
                                op: JInstructionOp::Jal,
                                imm: RelAddress::Label(label),
                                rd: Register::ra(),
                            }));
                            insts.push(Instruction::mv(result_reg, Register::a(0)));
                        } else {
                            todo!()
                        }
                    }
                    Phi(_nodes) => {}
                    Operand(op) => {
                        load_operand_to(&mut ctx, &mut insts, &register_map, op, result_reg);
                    }
                    Label(label) => {
                        add_label(&mut ctx, &mut insts, label.name);
                    }
                }
            }
        }
    }

    // Resolving label addresses

    let insts = insts
        .into_iter()
        .enumerate()
        .map(|(addr, inst)| match inst {
            J(JInstruction {
                op: JInstructionOp::Jal,
                imm: RelAddress::Label(label),
                rd,
            }) => {
                let laddr = ctx.label_addrs.get(&label.name).unwrap();

                let addr = addr as i32;
                let laddr = *laddr;

                J(JInstruction {
                    op: JInstructionOp::Jal,
                    imm: RelAddress::Immediate(Immediate::new((laddr - addr) * 4, 20)),
                    rd,
                })
            }
            _ => inst,
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
        })
        .collect();

    Ok(result)
}
