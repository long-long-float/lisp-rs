use std::fs::File;
use std::io::Write;
use std::path::Path;

use anyhow::Result;
use colored::*;
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

    fn get_addr_by_label(
        &self,
        label: &Label,
        inst_addr: usize,
        label_addr: usize,
    ) -> Result<(i32, Option<RelocationEntry>)> {
        if label.relocated_later {
            Ok((
                0,
                Some(RelocationEntry {
                    addr: label_addr,
                    name: label.name.clone(),
                }),
            ))
        } else {
            let addr = self
                .label_addrs
                .get(&label.name)
                .cloned()
                .ok_or_else(|| Error::LabelNotDefined(label.name.to_string()))
                .map(|addr| addr as i32 - inst_addr as i32)?;
            Ok((addr, None))
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
struct RelocationEntry {
    addr: usize,
    name: String,
}

type Code = u32;
type Codes = Vec<Code>;

pub fn dump_instructions(insts: &[InstructionWithLabel]) {
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

fn replace_label(
    imm: Immediate,
    imm_addr: usize,
    ctx: &Context,
) -> Result<(Immediate, Option<RelocationEntry>)> {
    match imm {
        Immediate::Value(_) => Ok((imm, None)),
        Immediate::Label(label) => {
            let (addr, rel) = ctx.get_addr_by_label(
                &label,
                // This offset is not considered because the address as immediate is not relative.
                0, imm_addr,
            )?;
            Ok((Immediate::new(addr), rel))
        }
    }
}

fn replace_reladdr_label(
    rel_addr: RelAddress,
    rel_addr_addr: usize,
    inst_addr: usize,
    ctx: &Context,
) -> Result<(RelAddress, Option<RelocationEntry>)> {
    match rel_addr {
        RelAddress::Immediate(_) => Ok((rel_addr, None)),
        RelAddress::Label(label) => {
            let (addr, rel) = ctx.get_addr_by_label(&label, inst_addr, rel_addr_addr)?;
            Ok((RelAddress::Immediate(Immediate::Value(addr)), rel))
        }
    }
}

fn replace_labels(
    inst: InstructionWithLabel,
    inst_addr: usize,
    ctx: &Context,
) -> Result<(InstructionWithLabel, Option<RelocationEntry>)> {
    use Instruction::*;

    let InstructionWithLabel { inst, labels, ir } = inst;
    let (replaced, rel) = match inst {
        R(_) => (inst, None),
        I(IInstruction { op, imm, rs1, rd }) => {
            let (imm, rel) = replace_label(imm, todo!(), ctx)?;
            (I(IInstruction { op, imm, rs1, rd }), rel)
        }
        S(SInstruction { op, imm, rs1, rs2 }) => {
            let (imm, rel) = replace_label(imm, todo!(), ctx)?;
            (S(SInstruction { op, imm, rs1, rs2 }), rel)
        }
        J(_) => (inst, None),
        U(UInstruction { op, imm, rd }) => {
            let (imm, rel) = replace_label(imm, todo!(), ctx)?;
            (U(UInstruction { op, imm, rd }), rel)
        }
        SB(_) => (inst, None),
    };
    Ok((InstructionWithLabel::new(replaced, labels, ir), rel))
}

fn replace_reladdr_labels(
    inst: InstructionWithLabel,
    addr: usize,
    ctx: &Context,
) -> Result<(InstructionWithLabel, Option<RelocationEntry>)> {
    use Instruction::*;

    let InstructionWithLabel { inst, labels, ir } = inst;
    let (replaced, rel) = match inst {
        J(JInstruction { op, imm, rd }) => {
            let (imm, rel) = replace_reladdr_label(imm, addr, todo!(), ctx)?;
            (J(JInstruction { op, imm, rd }), rel)
        }
        SB(SBInstruction { op, imm, rs1, rs2 }) => {
            let (imm, rel) = replace_reladdr_label(imm, addr, todo!(), ctx)?;
            (SB(SBInstruction { op, imm, rs1, rs2 }), rel)
        }
        _ => (inst, None),
    };
    Ok((InstructionWithLabel::new(replaced, labels, ir), rel))
}

pub fn assemble<P>(instructions: Vec<InstructionWithLabel>, dump_to: Option<P>) -> Result<Codes>
where
    P: AsRef<Path>,
{
    use Instruction::*;

    let mut ctx = Context::new();

    let mut rel_entries = Vec::new();

    for (idx, inst) in instructions.iter().enumerate() {
        for label in &inst.labels {
            ctx.label_addrs.insert(label.name.clone(), idx * 4);
        }
    }

    let mut insts = Vec::with_capacity(instructions.len());
    for (addr, inst) in instructions.into_iter().enumerate() {
        let addr = addr * 4;

        let (inst, rel) = replace_labels(inst, addr, &ctx)?;
        if let Some(rel) = rel {
            rel_entries.push(rel);
        }

        let (inst, rel) = replace_reladdr_labels(inst, addr, &ctx)?;
        if let Some(rel) = rel {
            rel_entries.push(rel);
        }

        insts.push(inst);
    }

    dbg!(rel_entries);

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
