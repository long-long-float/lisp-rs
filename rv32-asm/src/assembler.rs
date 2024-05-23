use std::io::Write;
use std::{collections::HashSet, fs::File};

use anyhow::Result;
use colored::*;
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::instruction::*;

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

#[allow(dead_code)]
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

pub fn assemble(instructions: &[Instruction]) -> Result<Codes> {
    use Instruction::*;

    let mut ctx = Context::new();
    // TODO: Add label to instruction and remove ctx.

    let insts = instructions
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

    let mut asm = File::create("out.s")?;
    for (addr, InstrWithIr(inst, ir)) in insts.iter().enumerate() {
        let label = ctx.label_addrs.iter().find_map(|(label, laddr)| {
            if *laddr == addr as i32 {
                Some(label)
            } else {
                None
            }
        });
        if let Some(label) = label {
            writeln!(asm, "{}: # 0x{:x}", label, addr * 4)?;
        }
        if let Some(ir) = ir {
            writeln!(asm, "  #{}", ir)?;
        }
        let a = match inst {
            R(ri) => ri.generate_asm(),
            I(ii) => ii.generate_asm(),
            S(si) => si.generate_asm(),
            J(ji) => ji.generate_asm(),
            U(ui) => ui.generate_asm(),
            SB(sbi) => sbi.generate_asm(),
        };
        writeln!(asm, "  {}", a)?;
    }

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
