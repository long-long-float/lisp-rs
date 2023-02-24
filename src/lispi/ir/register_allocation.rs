use std::default;

use rustc_hash::FxHashSet;

use crate::lispi::{console::println, ir::instruction::Operand};

use super::{
    instruction::{Functions, Instruction, Variable},
    IrContext,
};

fn get_vars<'a>(inst: &'a Instruction, vars: &mut Vec<&'a Variable>) {
    fn add_only_var<'a>(op: &'a Operand, vars: &mut Vec<&'a Variable>) {
        if let Operand::Variable(var) = op {
            vars.push(var);
        }
    }

    match inst {
        Instruction::Branch { cond, .. } => {
            add_only_var(cond, vars);
        }
        Instruction::Jump(_, _) => {}
        Instruction::Ret(op) => add_only_var(op, vars),
        Instruction::Add(left, right) => {
            add_only_var(left, vars);
            add_only_var(right, vars);
        }
        Instruction::Sub(left, right) => {
            add_only_var(left, vars);
            add_only_var(right, vars);
        }
        Instruction::Mul(left, right) => {
            add_only_var(left, vars);
            add_only_var(right, vars);
        }
        Instruction::Or(left, right) => {
            add_only_var(left, vars);
            add_only_var(right, vars);
        }
        Instruction::Shift(_, left, right) => {
            add_only_var(left, vars);
            add_only_var(right, vars);
        }
        Instruction::Store(addr, value) => {
            add_only_var(addr, vars);
            add_only_var(value, vars);
        }
        Instruction::Cmp(_, left, right) => {
            add_only_var(left, vars);
            add_only_var(right, vars);
        }
        Instruction::Call { fun, args } => {
            add_only_var(fun, vars);
            for arg in args {
                add_only_var(arg, vars);
            }
        }
        Instruction::Phi(nodes) => {
            for (op, _) in nodes {
                add_only_var(op, vars);
            }
        }
        Instruction::Operand(op) => add_only_var(op, vars),
        Instruction::Label(_) => {}
    }
}

pub fn create_interference_graph(funcs: &Functions, ir_ctx: &mut IrContext) {
    for func in funcs {
        let mut living_vars = FxHashSet::default();

        for bb in func.basic_blocks.iter().rev() {
            let bb = ir_ctx.bb_arena.get(*bb).unwrap();

            for annot_inst in &bb.insts {
                let mut used_vars = Vec::new();
                get_vars(&annot_inst.inst, &mut used_vars);

                for var in used_vars {
                    living_vars.insert(var);
                }

                for living_var in &living_vars {
                    print!("{} ", living_var.name);
                }
                println!();

                living_vars.remove(&annot_inst.result);
            }
        }
    }
}
