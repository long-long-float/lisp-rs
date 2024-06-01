//! Stack frame
//!
//! ```text
//!   Higher
//!
//!   Caller frame
//! ========================= FP
//!   Saved Registers
//! * Used registers
//!   * aX for arguments
//!   * tX
//! * fp(s0)
//! * ra
//! -------------------------
//!   Local Variables
//! ========================= SP
//!   Callee frame
//!
//!   Lower
//! ```
//!

use itertools::Itertools;
use rustc_hash::FxHashMap;
use rv32_asm::instruction::*;

use crate::lispi::ir::{instruction::Variable, register_allocation::RegisterMap};

pub struct StackFrame<'a> {
    register_map: &'a RegisterMap,
    callee_saved_registers: Vec<Register>,

    num_of_used_a_register: usize,

    /// Size of the region for local variable in bytes
    local_var_size: usize,
    local_var_map: FxHashMap<Variable, (usize, usize)>,
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
                // Used for temporary register
                Register::s(2),
            ],
            num_of_used_a_register: 10,
            local_var_size: 16 * 4,
            local_var_map: FxHashMap::default(),
        }
    }

    /// TODO: Manage local variable statically
    pub fn allocate_local_var(&mut self, var: &Variable, size: usize) -> usize {
        assert!(self.get_local_vars_size() < self.local_var_size);

        let idx = 4
            * (self.callee_saved_registers.len()
                + self.register_map.values().unique().count()
                + self.num_of_used_a_register)
            + self.get_local_vars_size();
        self.local_var_map.insert(var.clone(), (idx, size));
        idx
    }

    /// Returns the address and size of var.
    pub fn get_local_var(&self, var: &Variable) -> Option<(usize, usize)> {
        self.local_var_map.get(var).copied()
    }

    pub fn get_local_vars_size(&self) -> usize {
        self.local_var_map.values().map(|(_, size)| size).sum()
    }

    pub fn generate_fun_header(&self) -> Vec<InstructionWithLabel> {
        let frame_size = 4
            * (self.callee_saved_registers.len()
                + self.register_map.values().unique().count()
                + self.num_of_used_a_register
                + self.local_var_size) as i32;

        let mut insts = Vec::new();

        insts.push(Instruction::addi(Register::sp(), Register::sp(), -frame_size).into());

        for (i, reg) in self.callee_saved_registers.iter().enumerate() {
            insts.push(Instruction::sw(*reg, Register::sp(), Immediate::new(i as i32 * 4)).into());
        }

        insts.push(Instruction::addi(Register::fp(), Register::sp(), frame_size).into());

        insts.push(Instruction::mv(Register::s(1), Register::sp()).into());

        insts
    }

    pub fn generate_fun_footer(&self) -> Vec<InstructionWithLabel> {
        let mut insts = Vec::new();

        insts.push(Instruction::mv(Register::t(0), Register::fp()).into());

        for (i, reg) in self.callee_saved_registers.iter().enumerate() {
            insts.push(Instruction::lw(*reg, Register::s(1), Immediate::new(i as i32 * 4)).into());
        }

        insts.push(Instruction::mv(Register::sp(), Register::t(0)).into());

        insts
    }

    /// Generate insts to save and restore caller-saved registers.
    pub fn generate_insts_for_call(
        &self,
        args_count: usize,
        result_reg: Option<&Register>,
        preserve_result_reg: bool,
    ) -> (
        Vec<InstructionWithLabel>,
        Vec<InstructionWithLabel>,
        Vec<InstructionWithLabel>,
    ) {
        let used_regs = self
            .register_map
            .values()
            .unique()
            .map(|id| Register::t(*id as u32))
            .chain((0..args_count).map(|i| Register::a(i as u32)))
            .filter(|reg| {
                if preserve_result_reg {
                    true
                } else {
                    Some(reg) != result_reg
                }
            })
            .collect_vec();

        let mut save = Vec::new();
        // Save caller-saved registers for temporary and function arguments registers now
        for (i, reg) in used_regs.iter().enumerate() {
            save.push(
                Instruction::sw(*reg, Register::s(1), Immediate::new((i as i32 + 3) * 4)).into(),
            );
        }

        let mut restore_preserved_result_reg = Vec::new();

        let mut restore = Vec::new();
        for (i, reg) in used_regs.into_iter().enumerate() {
            if preserve_result_reg && Some(&reg) == result_reg {
                restore_preserved_result_reg.push(
                    Instruction::lw(reg, Register::s(1), Immediate::new((i as i32 + 3) * 4)).into(),
                );
            } else {
                restore.push(
                    Instruction::lw(reg, Register::s(1), Immediate::new((i as i32 + 3) * 4)).into(),
                );
            }
        }

        (save, restore_preserved_result_reg, restore)
    }
}
