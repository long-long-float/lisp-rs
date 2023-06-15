use anyhow::Result;
use colored::*;
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{bug, lispi::ir::register_allocation::RegisterMap};

use super::super::{
    cli_option::CliOption,
    error::*,
    ir::{basic_block as bb, instruction as i, register_allocation as ra, IrContext},
};
use super::instruction::*;

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

fn get_register_from_operand(
    ctx: &mut Context,
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
        i::Operand::Immediate(imm) => panic!(
            "Cannot load immediate operand. This should be formed as `%var = {}`.",
            imm,
        ),
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
        i::Operand::Variable(_) => {
            let reg = get_register_from_operand(ctx, register_map, op).unwrap();
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

#[allow(clippy::too_many_arguments)]
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
            let rs1 = get_register_from_operand(ctx, register_map, var)?;
            I(IInstruction {
                op: opi,
                imm: imm.into(),
                rs1,
                rd: result_reg,
            })
        }
        (left, right) => {
            let rs1 = get_register_from_operand(ctx, register_map, left)?;
            let rs2 = get_register_from_operand(ctx, register_map, right)?;

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
    funcs: Vec<(bb::Function, ra::RegisterMap)>,
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
                        let cond = get_register_from_operand(&mut ctx, &register_map, cond)?;
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
                    Alloca { ty, count } => todo!(),
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
                    Sub(left, right) => {
                        let rs1 = get_register_from_operand(&mut ctx, &register_map, left)?;
                        let rs2 = get_register_from_operand(&mut ctx, &register_map, right)?;

                        insts.push(R(RInstruction {
                            op: RInstructionOp::Sub,
                            rs1,
                            rs2,
                            rd: result_reg,
                        }));
                    }
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
                        let op = get_register_from_operand(&mut ctx, &register_map, op)?;
                        insts.push(I(IInstruction {
                            op: IInstructionOp::Xori,
                            // imm: Immediate::new(0xfffu32 as i32, XLEN),
                            imm: Immediate::new(0x1u32 as i32, XLEN),
                            rs1: op,
                            rd: result_reg,
                        }))
                    }
                    Shift(op, left, right) => {
                        let rs1 = get_register_from_operand(&mut ctx, &register_map, left)?;
                        let rs2 = get_register_from_operand(&mut ctx, &register_map, right)?;

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
                        let rs1 = get_register_from_operand(&mut ctx, &register_map, addr)?;
                        let rs2 = get_register_from_operand(&mut ctx, &register_map, value)?;

                        insts.push(S(SInstruction {
                            op: SInstructionOp::Sw,
                            imm: Immediate::new(0, XLEN),
                            rs1,
                            rs2,
                        }))
                    }
                    LoadElement { addr, ty, index } => todo!(),
                    StoreElement {
                        addr,
                        ty,
                        index,
                        value,
                    } => todo!(),
                    Cmp(op, left, right) => {
                        use i::CmpOperator::*;

                        let (inst_op, inst_opi) = match op {
                            Eq => todo!(),
                            SGE => todo!(),
                            SGT => todo!(),
                            SLT => (RInstructionOp::Slt, IInstructionOp::Slti),
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
                        let used_regs = register_map
                            .values()
                            .unique()
                            .map(|id| Register::t(*id as u32))
                            .chain(args.iter().enumerate().map(|(i, _)| Register::a(i as u32)))
                            .filter(|reg| reg != &result_reg)
                            .collect_vec();

                        // Save caller-saved registers for temporary and function arguments registers now
                        for (i, reg) in used_regs.iter().enumerate() {
                            insts.push(Instruction::sw(
                                reg.clone(),
                                Register::sp(),
                                Immediate::new((i as i32 + 2) * 4, XLEN),
                            ));
                        }

                        ctx.arg_count = 0;
                        for arg in args {
                            load_argument(&mut ctx, &mut insts, &register_map, arg);
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

                        insts.push(Instruction::mv(result_reg, Register::a(0)));

                        // Load caller-saved registers
                        for (i, reg) in used_regs.iter().enumerate() {
                            insts.push(Instruction::lw(
                                reg.clone(),
                                Register::sp(),
                                Immediate::new((i as i32 + 2) * 4, XLEN),
                            ));
                        }
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