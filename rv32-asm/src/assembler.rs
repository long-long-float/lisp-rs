use std::fs::File;
use std::io::Write;
use std::path::Path;

use anyhow::Result;
use colored::*;
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::error::*;
use crate::instruction::*;

struct Context {
    label_addrs: FxHashMap<String, usize>,
}

impl Context {
    fn new() -> Context {
        Context {
            label_addrs: FxHashMap::default(),
        }
    }

    fn get_addr_by_label(&self, name: &str) -> Result<usize> {
        Ok(self
            .label_addrs
            .get(name)
            .cloned()
            .ok_or_else(|| Error::LabelNotDefined(name.to_string()))?)
    }
}

type Code = u32;
type Codes = Vec<Code>;

#[allow(dead_code)]
fn dump_instructions(insts: &[InstructionWithLabel]) {
    println!("{}", "RISC-V Instructions:".red());
    for (addr, InstructionWithLabel { inst, labels, ir }) in insts.iter().enumerate() {
        for label in labels {
            let addr = format!("; 0x{:x}", addr * 4);
            println!("{}: {}", &label.name, addr.dimmed());
        }

        if let Some(ir) = ir {
            let ir = format!(";{}", ir);
            println!("  {}", ir.dimmed());
        }
        println!("  {}", inst);
    }
    println!();
}

fn replace_label(imm: Immediate, ctx: &Context) -> Result<Immediate> {
    match imm {
        Immediate::Value(_) => Ok(imm),
        Immediate::Label(label) => Ok(Immediate::new(ctx.get_addr_by_label(&label.name)? as i32)),
    }
}

fn replace_redaddr_label(rel_addr: RelAddress, addr: usize, ctx: &Context) -> Result<RelAddress> {
    match rel_addr {
        RelAddress::Immediate(_) => Ok(rel_addr),
        RelAddress::Label(label) => Ok(RelAddress::Immediate(Immediate::Value(
            (ctx.get_addr_by_label(&label.name)? - addr) as i32,
        ))),
    }
}

fn replace_labels(inst: InstructionWithLabel, ctx: &Context) -> Result<InstructionWithLabel> {
    use Instruction::*;

    let InstructionWithLabel { inst, labels, ir } = inst;
    let replaced = match inst {
        R(_) => inst,
        I(IInstruction { op, imm, rs1, rd }) => I(IInstruction {
            op,
            imm: replace_label(imm, ctx)?,
            rs1,
            rd,
        }),
        S(SInstruction { op, imm, rs1, rs2 }) => S(SInstruction {
            op,
            imm: replace_label(imm, ctx)?,
            rs1,
            rs2,
        }),
        J(_) => inst,
        U(UInstruction { op, imm, rd }) => U(UInstruction {
            op,
            imm: replace_label(imm, ctx)?,
            rd,
        }),
        SB(_) => inst,
    };
    Ok(InstructionWithLabel::new(replaced, labels, ir))
}

fn replace_reladdr_labels(
    inst: InstructionWithLabel,
    addr: usize,
    ctx: &Context,
) -> Result<InstructionWithLabel> {
    use Instruction::*;

    let InstructionWithLabel { inst, labels, ir } = inst;
    let replaced = match inst {
        J(JInstruction { op, imm, rd }) => J(JInstruction {
            op,
            imm: replace_redaddr_label(imm, addr, ctx)?,
            rd,
        }),
        SB(SBInstruction { op, imm, rs1, rs2 }) => SB(SBInstruction {
            op,
            imm: replace_redaddr_label(imm, addr, ctx)?,
            rs1,
            rs2,
        }),
        _ => inst,
    };
    Ok(InstructionWithLabel::new(replaced, labels, ir))
}

pub fn assemble<P>(instructions: Vec<InstructionWithLabel>, dump_to: Option<P>) -> Result<Codes>
where
    P: AsRef<Path>,
{
    use Instruction::*;

    let mut ctx = Context::new();

    for (idx, inst) in instructions.iter().enumerate() {
        for label in &inst.labels {
            ctx.label_addrs.insert(label.name.clone(), idx * 4);
        }
    }

    let insts: Vec<_> = instructions
        .into_iter()
        .enumerate()
        .map(|(addr, inst)| {
            let inst = replace_labels(inst, &ctx)?;
            replace_reladdr_labels(inst, addr * 4, &ctx)
        })
        .try_collect()?;

    if let Some(dump_to) = dump_to {
        let mut asm = File::create(dump_to)?;
        for (addr, InstructionWithLabel { inst, ir, labels }) in insts.iter().enumerate() {
            for label in labels {
                writeln!(asm, "{}: # 0x{:x}", &label.name, addr * 4)?;
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
    }

    let result = insts
        .into_iter()
        .map(|InstructionWithLabel { inst, .. }| match inst {
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
