use core::panic;
use std::collections::HashSet;

use anyhow::Result;
use colored::*;
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
    bug,
    lispi::{
        ir::{basic_block::IrProgram, register_allocation::RegisterMap, tag::Tag},
        ty::{StructDefinition, StructDefinitions, Type},
    },
};

use super::{
    super::{
        cli_option::CliOption,
        error::*,
        ir::{instruction as i, register_allocation as ra, IrContext},
    },
    Spec,
};
use super::{instruction::*, stack_frame::*};

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

fn dump_instructions(ctx: &mut Context, insts: &[InstrWithIr]) {
    println!("{}", "RISC-V Instructions:".red());
    for (addr, InstrWithIr(inst, ir)) in insts.iter().enumerate() {
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
        if let Some(ir) = ir {
            let ir = format!(";{}", ir);
            println!("  {}", ir.dimmed());
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
                Ok(*reg)
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
    insts: &mut Vec<InstrWithIr>,
    register_map: &RegisterMap,
    op: i::Operand,
    rd: Register,
) {
    match op {
        i::Operand::Variable(_) => {
            let reg = get_register_from_operand(ctx, register_map, op).unwrap();
            insts.push(InstrWithIr::from(Instruction::mv(rd, reg)));
        }
        i::Operand::Immediate(imm) => {
            use i::Immediate::*;
            match imm {
                Integer(_) | Boolean(_) => {
                    let imm: Immediate = imm.into();
                    load_immediate(insts, imm, rd);
                }
                Label(_) => {
                    // Replace this label to the real address.
                    // To load large addresses (larger than 12bits), we reserve for two instructions, lui and addi.
                    insts.push(InstrWithIr::from(Instruction::nop()));
                    insts.push(Instruction::li(rd, imm.into()).into());
                }
            }
        }
    }
}

fn load_immediate(insts: &mut Vec<InstrWithIr>, imm: Immediate, rd: Register) {
    let mut last_set_bit = -1;
    for i in (0..=31).rev() {
        if imm.value() & (1 << i) != 0 {
            last_set_bit = i;
            break;
        }
    }
    if last_set_bit >= 12 {
        // Large integer
        let bot = imm.value() & 0xfff;
        let top = if (bot >> 11 & 1) == 1 {
            println!("{:x}", imm.value());
            Immediate::new(imm.value().wrapping_add(0x1000))
        } else {
            imm
        };
        insts.push(InstrWithIr::from(Instruction::U(UInstruction {
            op: UInstructionOp::Lui,
            imm: top,
            rd,
        })));
        if bot > 0 {
            insts.push(Instruction::addi(rd, rd, bot).into());
        }
    } else {
        insts.push(InstrWithIr::from(Instruction::li(rd, imm)));
    }
}

#[allow(clippy::too_many_arguments)]
fn generate_code_bin_op(
    ctx: &mut Context,
    insts: &mut Vec<InstrWithIr>,
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
        (var, Immediate(imm)) => {
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

    insts.push(inst.into());

    Ok(())
}

fn replace_label(imm: Immediate, ctx: &Context) -> Immediate {
    match imm {
        Immediate::Value(_) => imm,
        Immediate::Label(label) => {
            let addr = ctx.label_addrs.get(&label.name).unwrap();
            Immediate::new(*addr * 4)
        }
    }
}

fn replace_labels(inst: InstrWithIr, ctx: &Context) -> InstrWithIr {
    use Instruction::*;

    let InstrWithIr(inst, ir) = inst;
    let replaced = match inst {
        R(_) => inst,
        I(IInstruction { op, imm, rs1, rd }) => I(IInstruction {
            op,
            imm: replace_label(imm, ctx),
            rs1,
            rd,
        }),
        S(SInstruction { op, imm, rs1, rs2 }) => S(SInstruction {
            op,
            imm: replace_label(imm, ctx),
            rs1,
            rs2,
        }),
        J(_) => inst,
        U(UInstruction { op, imm, rd }) => U(UInstruction {
            op,
            imm: replace_label(imm, ctx),
            rd,
        }),
        SB(_) => inst,
    };
    InstrWithIr(replaced, ir)
}

fn get_type_size(ty: &Type, structs: &StructDefinitions, align: usize) -> Result<usize> {
    match ty {
        Type::Struct { name } => {
            let Some(struct_def) = structs.get(name) else {
                return Err(Error::CompileError(format!("Struct {} is not defined", name)).into());
            };
            Ok(struct_def.size(align))
        }
        Type::FixedArray(et, len) => {
            Ok(Type::Int.size() + get_type_size(et, structs, align)? * len)
        }
        _ => Ok(ty.size()),
    }
}

fn get_struct_def<'a>(ty: &Type, structs: &'a StructDefinitions) -> Option<&'a StructDefinition> {
    if let Type::Struct { name } = ty {
        structs.get(name)
    } else {
        None
    }
}

pub fn generate_code(
    program: IrProgram,
    register_maps: Vec<ra::RegisterMap>,
    ir_ctx: &mut IrContext,
    opt: &CliOption,
    specs: HashSet<Spec>,
) -> Result<Codes> {
    if !specs.contains(&Spec::Integer32) {
        return Err(Error::CompileError("RV32I must be needed.".to_string()).into());
    }

    fn load_argument(
        ctx: &mut Context,
        insts: &mut Vec<InstrWithIr>,
        register_map: &RegisterMap,
        op: i::Operand,
    ) {
        let rd = ctx.allocate_arg_reg();
        load_operand_to(ctx, insts, register_map, op, rd);
    }

    fn add_label(ctx: &mut Context, insts: &mut Vec<InstrWithIr>, label: String) {
        ctx.label_addrs.insert(label, insts.len() as i32);
    }

    use Instruction::*;

    let mut ctx = Context::new();
    let mut insts: Vec<InstrWithIr> = Vec::new();

    // Initialize specific registers
    load_immediate(
        &mut insts,
        Immediate::new(0x80000000u32 as i32),
        Register::sp(),
    );

    let IrProgram { funcs, structs } = program;

    let reg_size = (XLEN / 8) as usize;

    for (fun, register_map) in funcs.into_iter().zip(register_maps) {
        let mut frame = StackFrame::new(&register_map);

        ctx.reset_on_fun();

        let result_size = fun
            .ty
            .fun_result_type()
            .ok_or(
                Error::CompileError("The type of function must be function type.".to_string())
                    .into(),
            )
            .and_then(|ty| get_type_size(ty, &structs, reg_size))
            .unwrap_or(0);

        let args_offset = if result_size > reg_size * 2 { 1 } else { 0 };
        for (i, (arg, _)) in fun.args.iter().enumerate() {
            ctx.arg_reg_map
                .insert(arg.clone(), Register::a((i + args_offset) as u32));
        }

        // Scan alloca with DontAllocateRegister
        for bb in &fun.basic_blocks {
            let bb = ir_ctx.bb_arena.get(*bb).unwrap();

            for i::AnnotatedInstr {
                result,
                inst,
                ty,
                tags,
            } in bb.insts.clone()
            {
                if let i::Instruction::Alloca {
                    ty: _,
                    count: i::Operand::Immediate(_),
                } = inst
                {
                    // TODO: Support count other than 4.
                    let has_dont_alloc_tag = tags
                        .iter()
                        .any(|t| t.is_match_with(&Tag::DontAllocateRegister));

                    if has_dont_alloc_tag {
                        frame.allocate_local_var(&result, get_type_size(&ty, &structs, reg_size)?);
                    }
                }
            }
        }

        for (bbi, bb) in fun.basic_blocks.into_iter().enumerate() {
            let bb = ir_ctx.bb_arena.get(bb).unwrap();

            add_label(&mut ctx, &mut insts, bb.label.clone());

            if bbi == 0 {
                insts.append(&mut frame.generate_fun_header());
            }

            for ainst in bb.insts.clone() {
                let ir = Some(ainst.display(false).to_string());

                let i::AnnotatedInstr {
                    result,
                    inst,
                    ty,
                    tags,
                } = ainst;

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

                let ir_insertion_idx = insts.len();

                match inst {
                    Branch {
                        cond,
                        then_label,
                        else_label,
                        then_bb: _,
                        else_bb: _,
                    } => {
                        let cond = get_register_from_operand(&mut ctx, &register_map, cond)?;
                        insts.push(InstrWithIr::from(SB(SBInstruction {
                            op: SBInstructionOp::Bne,
                            imm: RelAddress::Label(then_label),
                            rs1: cond,
                            rs2: Register::zero(),
                        })));
                        insts.push(
                            J(JInstruction {
                                op: JInstructionOp::Jal,
                                imm: RelAddress::Label(else_label),
                                rd: Register::zero(),
                            })
                            .into(),
                        );
                    }
                    Jump(label, _) => {
                        insts.push(InstrWithIr::from(J(JInstruction {
                            op: JInstructionOp::Jal,
                            imm: RelAddress::Label(label),
                            rd: Register::zero(),
                        })));
                    }
                    Ret(op) => {
                        if result_size > reg_size {
                            let reg =
                                get_register_from_operand(&mut ctx, &register_map, op).unwrap();

                            if result_size <= reg_size * 2 {
                                insts.push(
                                    Instruction::lw(Register::a(0), reg, Immediate::new(0)).into(),
                                );
                                insts.push(
                                    Instruction::lw(Register::a(1), reg, Immediate::new(4)).into(),
                                );
                            } else {
                                // result_size > reg_size * 2
                                let offsets = if let Some(struct_def @ StructDefinition { .. }) =
                                    get_struct_def(fun.ty.fun_result_type().unwrap(), &structs)
                                {
                                    struct_def.offsets(reg_size)
                                } else {
                                    (0..(result_size / reg_size)).map(|i| i * 4).collect_vec()
                                };

                                for offset in offsets {
                                    let offset = offset as i32;
                                    // We should be able to use register s2 at Ret instruction.
                                    let tmp_reg = Register::s(2);
                                    insts.push(
                                        Instruction::lw(tmp_reg, reg, Immediate::new(offset))
                                            .into(),
                                    );
                                    insts.push(
                                        Instruction::sw(
                                            tmp_reg,
                                            Register::a(0),
                                            Immediate::new(offset),
                                        )
                                        .into(),
                                    );
                                }
                            }
                        } else {
                            load_operand_to(
                                &mut ctx,
                                &mut insts,
                                &register_map,
                                op,
                                Register::a(0),
                            );
                        }

                        if fun.name == "main" {
                            // syscall EXIT on rv32emu
                            // insts.push(Instruction::li(Register::a(0), Immediate::new(0, XLEN)));
                            insts.push(Instruction::li(Register::a(7), Immediate::new(93)).into());
                            insts.push(
                                I(IInstruction {
                                    op: IInstructionOp::Ecall,
                                    imm: Immediate::new(0),
                                    rs1: Register::zero(),
                                    rd: Register::zero(),
                                })
                                .into(),
                            );
                        } else {
                            insts.append(&mut frame.generate_fun_footer());
                            insts.push(Instruction::ret().into());
                        }
                    }
                    Alloca { ty: _, count } => {
                        match count {
                            count @ i::Operand::Variable(_) => {
                                let count =
                                    get_register_from_operand(&mut ctx, &register_map, count)?;

                                insts.push(
                                    Instruction::R(RInstruction {
                                        op: RInstructionOp::Sub,
                                        rs1: Register::sp(),
                                        rs2: count,
                                        rd: Register::sp(),
                                    })
                                    .into(),
                                );
                            }
                            i::Operand::Immediate(count) => {
                                let has_dont_alloc_tag = tags
                                    .iter()
                                    .any(|t| t.is_match_with(&Tag::DontAllocateRegister));

                                if has_dont_alloc_tag {
                                    // It has been already allocated.
                                } else {
                                    let count = (Immediate::from(count).value() as f32 / 4.0).ceil()
                                        as i32
                                        * 4;
                                    insts.push(
                                        Instruction::addi(Register::sp(), Register::sp(), -count)
                                            .into(),
                                    );
                                }
                            }
                        }

                        insts.push(Instruction::mv(result_reg, Register::sp()).into());
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
                    Sub(left, right) => {
                        let rs1 = get_register_from_operand(&mut ctx, &register_map, left)?;
                        let rs2 = get_register_from_operand(&mut ctx, &register_map, right)?;

                        insts.push(
                            R(RInstruction {
                                op: RInstructionOp::Sub,
                                rs1,
                                rs2,
                                rd: result_reg,
                            })
                            .into(),
                        );
                    }
                    Mul(left, right) => {
                        if specs.contains(&Spec::Multiplication) {
                            let rs1 = get_register_from_operand(&mut ctx, &register_map, left)?;
                            let rs2 = get_register_from_operand(&mut ctx, &register_map, right)?;

                            insts.push(
                                R(RInstruction {
                                    op: RInstructionOp::Mul,
                                    rs1,
                                    rs2,
                                    rd: result_reg,
                                })
                                .into(),
                            );
                        } else {
                            todo!()
                        }
                    }
                    Div(left, right) => {
                        if specs.contains(&Spec::Multiplication) {
                            let rs1 = get_register_from_operand(&mut ctx, &register_map, left)?;
                            let rs2 = get_register_from_operand(&mut ctx, &register_map, right)?;

                            insts.push(
                                R(RInstruction {
                                    op: RInstructionOp::Div,
                                    rs1,
                                    rs2,
                                    rd: result_reg,
                                })
                                .into(),
                            );
                        } else {
                            todo!()
                        }
                    }
                    Mod(left, right) => {
                        if specs.contains(&Spec::Multiplication) {
                            let rs1 = get_register_from_operand(&mut ctx, &register_map, left)?;
                            let rs2 = get_register_from_operand(&mut ctx, &register_map, right)?;

                            insts.push(
                                R(RInstruction {
                                    op: RInstructionOp::Rem,
                                    rs1,
                                    rs2,
                                    rd: result_reg,
                                })
                                .into(),
                            );
                        } else {
                            todo!()
                        }
                    }
                    And(left, right) => {
                        generate_code_bin_op(
                            &mut ctx,
                            &mut insts,
                            &register_map,
                            left,
                            right,
                            RInstructionOp::And,
                            IInstructionOp::Andi,
                            result_reg,
                        )?;
                    }
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
                        insts.push(
                            I(IInstruction {
                                op: IInstructionOp::Xori,
                                imm: Immediate::new(0x1),
                                rs1: op,
                                rd: result_reg,
                            })
                            .into(),
                        )
                    }
                    Shift(op, left, right) => {
                        let rs1 = get_register_from_operand(&mut ctx, &register_map, left)?;
                        let rs2 = get_register_from_operand(&mut ctx, &register_map, right)?;

                        let op = match op {
                            i::ShiftOperator::LogicalLeft => RInstructionOp::ShiftLeft,
                            i::ShiftOperator::LogicalRight => RInstructionOp::ShiftRight,
                        };

                        insts.push(
                            R(RInstruction {
                                op,
                                rs1,
                                rs2,
                                rd: result_reg,
                            })
                            .into(),
                        )
                    }
                    Store(addr, value) => {
                        let rs1 = get_register_from_operand(&mut ctx, &register_map, addr)?;
                        let rs2 = get_register_from_operand(&mut ctx, &register_map, value)?;

                        insts.push(
                            S(SInstruction {
                                op: SInstructionOp::Sw,
                                imm: Immediate::new(0),
                                rs1,
                                rs2,
                            })
                            .into(),
                        )
                    }
                    LoadElement { addr, ty, index } => {
                        let local_idx = if let i::Operand::Variable(addr) = &addr {
                            frame
                                .get_local_var(addr)
                                .map(|(idx, _)| Immediate::new(idx as i32))
                        } else {
                            None
                        };

                        let op = match ty {
                            Type::Int => IInstructionOp::Lw,
                            Type::Char => IInstructionOp::Lb,
                            _ => todo!(),
                        };

                        let (addr, index) = if let Some(local_idx) = local_idx {
                            let addr = Register::fp();
                            match index {
                                i::Operand::Immediate(index) => (addr, local_idx + index.into()),
                                _ => {
                                    let index =
                                        get_register_from_operand(&mut ctx, &register_map, index)?;
                                    let new_addr = Register::s(2);
                                    insts.push(Instruction::add(new_addr, addr, index).into());

                                    (new_addr, local_idx)
                                }
                            }
                        } else {
                            let addr = get_register_from_operand(&mut ctx, &register_map, addr)?;
                            match index {
                                i::Operand::Immediate(index) => (addr, index.into()),
                                _ => {
                                    let index =
                                        get_register_from_operand(&mut ctx, &register_map, index)?;
                                    let new_addr = Register::s(2);
                                    insts.push(Instruction::add(new_addr, addr, index).into());

                                    (new_addr, Immediate::Value(0))
                                }
                            }
                        };

                        insts.push(
                            I(IInstruction {
                                op,
                                imm: index,
                                rs1: addr,
                                rd: result_reg,
                            })
                            .into(),
                        )
                    }
                    StoreElement {
                        addr,
                        ty,
                        index,
                        value,
                    } => {
                        let local_idx = if let i::Operand::Variable(addr) = &addr {
                            frame
                                .get_local_var(addr)
                                .map(|(idx, _)| Immediate::new(idx as i32))
                        } else {
                            None
                        };

                        let value = get_register_from_operand(&mut ctx, &register_map, value)?;

                        let op = match ty {
                            Type::Int => SInstructionOp::Sw,
                            Type::Char => SInstructionOp::Sb,
                            _ => todo!(),
                        };

                        let (addr, index) = if let Some(local_idx) = local_idx {
                            let addr = Register::fp();
                            match index {
                                i::Operand::Immediate(index) => (addr, local_idx + index.into()),
                                _ => {
                                    let index =
                                        get_register_from_operand(&mut ctx, &register_map, index)?;
                                    let new_addr = Register::s(2);
                                    insts.push(Instruction::add(new_addr, addr, index).into());

                                    (new_addr, local_idx)
                                }
                            }
                        } else {
                            let addr = get_register_from_operand(&mut ctx, &register_map, addr)?;
                            match index {
                                i::Operand::Immediate(index) => (addr, index.into()),
                                _ => {
                                    let index =
                                        get_register_from_operand(&mut ctx, &register_map, index)?;
                                    let new_addr = Register::s(2);
                                    insts.push(Instruction::add(new_addr, addr, index).into());

                                    (new_addr, Immediate::Value(0))
                                }
                            }
                        };

                        insts.push(
                            S(SInstruction {
                                op,
                                imm: index,
                                rs1: addr,
                                rs2: value,
                            })
                            .into(),
                        )
                    }
                    Cmp(op, left, right) => {
                        use i::CmpOperator::*;

                        match op {
                            Eq => todo!(),
                            SGE => todo!(),
                            SLE => todo!(),
                            SGT => todo!(),
                            SLT => {
                                generate_code_bin_op(
                                    &mut ctx,
                                    &mut insts,
                                    &register_map,
                                    left,
                                    right,
                                    RInstructionOp::Slt,
                                    IInstructionOp::Slti,
                                    result_reg,
                                )?;
                            }
                        };
                    }
                    Call { fun, args } => {
                        if !matches!(
                            ty,
                            Type::Int
                                | Type::Char
                                | Type::Boolean
                                | Type::Void
                                | Type::FixedArray(_, _)
                                | Type::Struct { .. }
                        ) {
                            return Err(Error::CompileError(format!(
                                "Functions can't return {} now.",
                                ty
                            ))
                            .into());
                        }

                        let type_size = get_type_size(&ty, &structs, reg_size)?;

                        if type_size > reg_size {
                            let local_idx = frame.allocate_local_var(&result, type_size);
                            insts.push(
                                Instruction::addi(result_reg, Register::fp(), local_idx as i32)
                                    .into(),
                            );
                        }

                        let preserve_result_reg = reg_size < type_size && type_size <= reg_size * 2;

                        // If the size of result value is greater than reg_size,
                        // the result value is stored at the reference passed at the 1st argument.
                        let pass_ref_as_returned_value = type_size > reg_size * 2;

                        let (mut save, mut restore_preserved_result_reg, mut restore) = {
                            let (args_len, result_reg) = if pass_ref_as_returned_value {
                                (args.len() + 1, None)
                            } else {
                                (args.len(), Some(&result_reg))
                            };
                            frame.generate_insts_for_call(args_len, result_reg, preserve_result_reg)
                        };

                        insts.append(&mut save);

                        if pass_ref_as_returned_value {
                            insts.push(Instruction::mv(Register::a(0), result_reg).into());
                        }

                        ctx.arg_count = if pass_ref_as_returned_value { 1 } else { 0 };
                        for arg in args {
                            load_argument(&mut ctx, &mut insts, &register_map, arg);
                        }

                        match fun {
                            i::Operand::Variable(_) => {
                                let fun = get_register_from_operand(&mut ctx, &register_map, fun)?;
                                insts.push(
                                    I(IInstruction {
                                        op: IInstructionOp::Jalr,
                                        imm: Immediate::new(0),
                                        rs1: fun,
                                        rd: Register::ra(),
                                    })
                                    .into(),
                                );
                            }
                            i::Operand::Immediate(i::Immediate::Label(label)) => {
                                insts.push(
                                    J(JInstruction {
                                        op: JInstructionOp::Jal,
                                        imm: RelAddress::Label(label),
                                        rd: Register::ra(),
                                    })
                                    .into(),
                                );
                            }
                            _ => todo!(),
                        }

                        insts.append(&mut restore_preserved_result_reg);

                        if ty == Type::Void {
                            // Drop the void result
                        } else if type_size <= reg_size {
                            insts.push(Instruction::mv(result_reg, Register::a(0)).into());
                        } else if type_size <= reg_size * 2 {
                            insts.push(
                                Instruction::sw(Register::a(0), result_reg, Immediate::new(0))
                                    .into(),
                            );
                            insts.push(
                                Instruction::sw(Register::a(1), result_reg, Immediate::new(4))
                                    .into(),
                            );
                        } else {
                            // Received the result through result_reg
                        }

                        insts.append(&mut restore);
                    }
                    SysCall { number, args } => {
                        let (mut save, mut restore_preserved_result_reg, mut restore) =
                            frame.generate_insts_for_call(args.len(), Some(&result_reg), false);

                        insts.append(&mut save);

                        ctx.arg_count = 0;
                        for arg in args {
                            load_argument(&mut ctx, &mut insts, &register_map, arg);
                        }

                        load_operand_to(
                            &mut ctx,
                            &mut insts,
                            &register_map,
                            number,
                            Register::a(7),
                        );

                        insts.push(
                            Instruction::I(IInstruction {
                                op: IInstructionOp::Ecall,
                                imm: Immediate::new(0),
                                rs1: Register::zero(),
                                rd: Register::zero(),
                            })
                            .into(),
                        );

                        insts.append(&mut restore_preserved_result_reg);
                        insts.append(&mut restore);
                    }
                    Phi(_nodes) => {}
                    Reference(_) => {
                        panic!("ref must be removed before code generating.")
                    }
                    Operand(op) => {
                        load_operand_to(&mut ctx, &mut insts, &register_map, op, result_reg);
                    }
                    Label(label) => {
                        add_label(&mut ctx, &mut insts, label.name);
                    }
                    Nop => {}
                }

                if let Some(head) = insts.get_mut(ir_insertion_idx) {
                    head.set_ir(ir);
                }
            }
        }
    }

    // Resolving label addresses

    let insts = insts
        .into_iter()
        .map(|inst| replace_labels(inst, &ctx))
        .collect_vec();

    let insts = insts
        .into_iter()
        .enumerate()
        .map(|(addr, InstrWithIr(inst, ir))| {
            let addr = addr as i32;
            let inst = match inst {
                J(JInstruction {
                    op: op @ JInstructionOp::Jal,
                    imm: RelAddress::Label(label),
                    rd,
                }) => {
                    let laddr = *ctx.label_addrs.get(&label.name).unwrap();

                    J(JInstruction {
                        op,
                        imm: RelAddress::Immediate(Immediate::new((laddr - addr) * 4)),
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
                        imm: RelAddress::Immediate(Immediate::new((laddr - addr) * 4)),
                        rs1,
                        rs2,
                    })
                }
                _ => inst,
            };
            InstrWithIr(inst, ir)
        })
        .collect_vec();

    if opt.dump {
        dump_instructions(&mut ctx, &insts);
    }

    let asm = insts
        .iter()
        .map(|InstrWithIr(inst, _)| match inst {
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
        .map(|InstrWithIr(inst, _)| match inst {
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
