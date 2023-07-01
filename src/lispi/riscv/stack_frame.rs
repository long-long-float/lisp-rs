use itertools::Itertools;

use super::instruction::*;
use crate::lispi::ir::register_allocation::RegisterMap;

pub struct StackFrame<'a> {
    register_map: &'a RegisterMap,
    callee_saved_registers: Vec<Register>,
}

impl<'a> StackFrame<'a> {
    pub fn new(register_map: &'a RegisterMap) -> Self {
        Self {
            register_map,
            callee_saved_registers: vec![
                // Register 'ra' is caller-saved.
                // However it is treated as callee-saved because it is not used in function body.
                Register::ra(),
                Register::fp(),
                Register::s(1),
            ],
        }
    }

    pub fn generate_fun_header(&self) -> Vec<Instruction> {
        let frame_size = 4
            * (self.callee_saved_registers.len() + self.register_map.values().unique().count())
                as i32;

        let mut insts = Vec::new();

        insts.push(Instruction::addi(
            Register::sp(),
            Register::sp(),
            -frame_size,
        ));

        for (i, reg) in self.callee_saved_registers.iter().enumerate() {
            insts.push(Instruction::sw(
                reg.clone(),
                Register::sp(),
                Immediate::new(i as i32 * 4),
            ));
        }

        insts.push(Instruction::addi(
            Register::fp(),
            Register::sp(),
            frame_size,
        ));

        insts.push(Instruction::mv(Register::s(1), Register::sp()));

        insts
    }

    pub fn generate_fun_footer(&self) -> Vec<Instruction> {
        let mut insts = Vec::new();

        insts.push(Instruction::mv(Register::t(0), Register::fp()));

        for (i, reg) in self.callee_saved_registers.iter().enumerate() {
            insts.push(Instruction::lw(
                reg.clone(),
                Register::s(1),
                Immediate::new(i as i32 * 4),
            ));
        }

        insts.push(Instruction::mv(Register::sp(), Register::t(0)));

        insts
    }

    /// Generate insts to save and restore caller-saved registers.
    pub fn generate_insts_for_call(
        &self,
        args_count: usize,
        result_reg: &Register,
    ) -> (Vec<Instruction>, Vec<Instruction>) {
        let used_regs = self
            .register_map
            .values()
            .unique()
            .map(|id| Register::t(*id as u32))
            .chain((0..args_count).map(|i| Register::a(i as u32)))
            .filter(|reg| reg != result_reg)
            .collect_vec();

        let mut save = Vec::new();
        // Save caller-saved registers for temporary and function arguments registers now
        for (i, reg) in used_regs.iter().enumerate() {
            save.push(Instruction::sw(
                reg.clone(),
                Register::s(1),
                Immediate::new((i as i32 + 3) * 4),
            ));
        }

        let mut restore = Vec::new();
        for (i, reg) in used_regs.into_iter().enumerate() {
            restore.push(Instruction::lw(
                reg,
                Register::s(1),
                Immediate::new((i as i32 + 3) * 4),
            ));
        }

        (save, restore)
    }
}
