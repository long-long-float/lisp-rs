use std::collections::HashSet;

use anyhow::Result;
use rustc_hash::FxHashMap;

use crate::lispi::ir::IrContext;

use super::super::ir::basic_block::*;
use super::super::ir::instruction::*;

use Instruction as I;

struct Context {
    env: FxHashMap<String, Immediate>,
}

fn remove_deadcode(fun: &Function, ir_ctx: &mut IrContext) -> Result<()> {
    fn register_as_used(used_vars: &mut HashSet<Variable>, op: &Operand) {
        if let Operand::Variable(var) = op {
            used_vars.insert(var.clone());
        }
    }

    let mut used_vars = HashSet::new();

    // Look phi functions first because they reference back variables.
    for bb in fun.basic_blocks.iter().rev() {
        let bb = ir_ctx.bb_arena.get_mut(*bb).unwrap();
        for AnnotatedInstr { inst, .. } in &bb.insts {
            if let Instruction::Phi(nodes) = inst {
                for (op, _) in nodes {
                    register_as_used(&mut used_vars, op);
                }
            }
        }
    }

    for bb in fun.basic_blocks.iter().rev() {
        let mut result = Vec::new();

        let bb = ir_ctx.bb_arena.get_mut(*bb).unwrap();

        for AnnotatedInstr {
            result: var,
            inst,
            ty,
            tags: _,
        } in bb.insts.clone().into_iter().rev()
        {
            // TOOD: Use get_vars in register_allocation
            match &inst {
                Instruction::Branch {
                    cond,
                    then_label: _,
                    else_label: _,
                    ..
                } => {
                    register_as_used(&mut used_vars, cond);
                }
                Instruction::Ret(op) => register_as_used(&mut used_vars, op),

                Instruction::Alloca { ty: _, count } => register_as_used(&mut used_vars, count),

                Instruction::Add(l, r)
                | Instruction::Sub(l, r)
                | Instruction::Mul(l, r)
                | Instruction::Div(l, r)
                | Instruction::Or(l, r)
                | Instruction::Shift(_, l, r)
                | Instruction::Store(l, r)
                | Instruction::Cmp(_, l, r) => {
                    register_as_used(&mut used_vars, l);
                    register_as_used(&mut used_vars, r);
                }
                Instruction::Not(op) => register_as_used(&mut used_vars, op),

                Instruction::LoadElement { addr, ty: _, index } => {
                    register_as_used(&mut used_vars, addr);
                    register_as_used(&mut used_vars, index);
                }
                Instruction::StoreElement {
                    addr,
                    ty: _,
                    index,
                    value,
                } => {
                    register_as_used(&mut used_vars, addr);
                    register_as_used(&mut used_vars, index);
                    register_as_used(&mut used_vars, value);
                }

                Instruction::Call { fun, args } => {
                    register_as_used(&mut used_vars, fun);
                    args.iter()
                        .for_each(|arg| register_as_used(&mut used_vars, arg));
                }
                Instruction::SysCall { number, args } => {
                    register_as_used(&mut used_vars, number);
                    args.iter()
                        .for_each(|arg| register_as_used(&mut used_vars, arg));
                }

                Instruction::Phi(_) => { /* Variables added in front. */ }

                Instruction::Operand(op) => register_as_used(&mut used_vars, op),

                Instruction::Jump(_, _) | Instruction::Label(_) | Instruction::Nop => {}
            }

            let used = inst.is_label() || inst.is_terminal() || used_vars.contains(&var);

            if !inst.is_removable() || used {
                result.push(AnnotatedInstr::new(var, inst, ty));
            }
        }

        result.reverse();
        bb.insts = result;
    }

    Ok(())
}

fn fold_imm(ctx: &mut Context, op: Operand) -> Operand {
    match op {
        Operand::Variable(var) => {
            if let Some(imm) = ctx.env.get(&var.name) {
                Operand::Immediate(imm.clone())
            } else {
                Operand::Variable(var)
            }
        }
        Operand::Immediate(_) => op,
    }
}

fn insert_imm(ctx: &mut Context, op: &Operand, var: &Variable) {
    match op {
        Operand::Immediate(imm) => {
            ctx.env.insert(var.name.clone(), imm.clone());
        }
        Operand::Variable(_) => {}
    }
}

fn fold_constants_arith<F1, F2>(
    ctx: &mut Context,
    var: &Variable,
    left: Operand,
    right: Operand,
    if_int: F1,
    if_else: F2,
) -> Instruction
where
    F1: Fn(i32, i32) -> i32,
    F2: Fn(Operand, Operand) -> Instruction,
{
    let folded_left = fold_imm(ctx, left.clone());
    let folded_right = fold_imm(ctx, right.clone());

    if let (
        Operand::Immediate(Immediate::Integer(left)),
        Operand::Immediate(Immediate::Integer(right)),
    ) = (&folded_left, &folded_right)
    {
        let val = if_int(*left, *right);

        let op = Operand::Immediate(Immediate::Integer(val));
        insert_imm(ctx, &op, var);
        I::Operand(op)
    } else {
        if_else(folded_left, folded_right)
    }
}

/// TODO: Commonalize with fold_constants_arith
fn fold_constants_logical<F1, F2>(
    ctx: &mut Context,
    var: &Variable,
    left: Operand,
    right: Operand,
    if_int: F1,
    if_else: F2,
) -> Instruction
where
    F1: Fn(bool, bool) -> bool,
    F2: Fn(Operand, Operand) -> Instruction,
{
    let folded_left = fold_imm(ctx, left.clone());
    let folded_right = fold_imm(ctx, right.clone());

    if let (
        Operand::Immediate(Immediate::Boolean(left)),
        Operand::Immediate(Immediate::Boolean(right)),
    ) = (&folded_left, &folded_right)
    {
        let val = if_int(*left, *right);

        let op = Operand::Immediate(Immediate::Boolean(val));
        insert_imm(ctx, &op, var);
        I::Operand(op)
    } else {
        if_else(folded_left, folded_right)
    }
}

fn fold_constants_insts(fun: &Function, ctx: &mut Context, ir_ctx: &mut IrContext) -> Result<()> {
    for bb in &fun.basic_blocks {
        let bb = ir_ctx.bb_arena.get_mut(*bb).unwrap();

        let mut result = Vec::new();

        for AnnotatedInstr {
            result: var,
            inst,
            ty,
            tags: _,
        } in bb.insts.clone()
        {
            let inst = match inst {
                I::Operand(Operand::Immediate(imm)) => {
                    ctx.env.insert(var.name.clone(), imm.clone());
                    Some(I::Operand(Operand::Immediate(imm)))
                }
                I::Operand(op @ Operand::Variable(_)) => {
                    let op = fold_imm(ctx, op);
                    insert_imm(ctx, &op, &var);
                    Some(I::Operand(op))
                }

                I::Branch {
                    cond,
                    then_label,
                    else_label,
                    then_bb,
                    else_bb,
                } => {
                    let cond = fold_imm(ctx, cond);
                    Some(I::Branch {
                        cond,
                        then_label,
                        else_label,
                        then_bb,
                        else_bb,
                    })
                }

                I::Alloca { ty, count } => Some(I::Alloca {
                    ty,
                    count: fold_imm(ctx, count),
                }),

                I::Add(left, right) => Some(fold_constants_arith(
                    ctx,
                    &var,
                    left,
                    right,
                    |l, r| l + r,
                    I::Add,
                )),
                I::Sub(left, right) => Some(fold_constants_arith(
                    ctx,
                    &var,
                    left,
                    right,
                    |l, r| l - r,
                    I::Sub,
                )),
                I::Mul(left, right) => Some(fold_constants_arith(
                    ctx,
                    &var,
                    left,
                    right,
                    |l, r| l * r,
                    I::Mul,
                )),
                I::Div(left, right) => Some(fold_constants_arith(
                    ctx,
                    &var,
                    left,
                    right,
                    |l, r| l / r,
                    I::Div,
                )),
                I::Or(left, right) => Some(fold_constants_logical(
                    ctx,
                    &var,
                    left,
                    right,
                    |l, r| l | r,
                    I::Or,
                )),
                I::Shift(op, left, right) => Some(fold_constants_arith(
                    ctx,
                    &var,
                    left,
                    right,
                    |l, r| {
                        // TODO: The behavior of shift may be difference between host machine and target machine.
                        // Take care this.
                        match &op {
                            ShiftOperator::LogicalLeft => l << r,
                            ShiftOperator::LogicalRight => {
                                let ul = l as u32;
                                let ur = r;
                                (ul >> ur) as i32
                            }
                        }
                    },
                    |l, r| I::Shift(op, l, r),
                )),
                I::Store(addr, value) => {
                    let addr = fold_imm(ctx, addr);
                    let value = fold_imm(ctx, value);
                    Some(I::Store(addr, value))
                }
                I::LoadElement { addr, ty, index } => Some(I::LoadElement {
                    addr: fold_imm(ctx, addr),
                    ty,
                    index: fold_imm(ctx, index),
                }),
                I::StoreElement {
                    addr,
                    ty,
                    index,
                    value,
                } => Some(I::StoreElement {
                    addr: fold_imm(ctx, addr),
                    ty,
                    index: fold_imm(ctx, index),
                    value,
                }),
                I::Not(op) => {
                    let op = fold_imm(ctx, op);
                    if let Operand::Immediate(Immediate::Boolean(op)) = &op {
                        let not_op = Operand::Immediate(Immediate::Boolean(!op));
                        insert_imm(ctx, &not_op, &var);
                        Some(I::Operand(not_op))
                    } else {
                        Some(I::Not(op))
                    }
                }
                I::Cmp(op, left, right) => {
                    let left = fold_imm(ctx, left);
                    let right = fold_imm(ctx, right);

                    if let (
                        Operand::Immediate(Immediate::Integer(left)),
                        Operand::Immediate(Immediate::Integer(right)),
                    ) = (&left, &right)
                    {
                        let val = match op {
                            CmpOperator::Eq => left == right,
                            CmpOperator::SGE => left <= right,
                            CmpOperator::SGT => left < right,
                            CmpOperator::SLT => left > right,
                        };

                        let op = Operand::Immediate(Immediate::Boolean(val));
                        insert_imm(ctx, &op, &var);
                        Some(I::Operand(op))
                    } else {
                        Some(I::Cmp(op, left, right))
                    }
                }
                I::Call { fun, args } => {
                    let fun = fold_imm(ctx, fun);
                    let args = args.into_iter().map(|arg| fold_imm(ctx, arg)).collect();

                    Some(I::Call { fun, args })
                }
                I::SysCall { number, args } => {
                    let number = fold_imm(ctx, number);
                    let args = args.into_iter().map(|arg| fold_imm(ctx, arg)).collect();
                    Some(I::SysCall { number, args })
                }
                I::Ret(op) => Some(I::Ret(fold_imm(ctx, op))),

                I::Jump(_, _) | I::Phi(_) | I::Label(_) | I::Nop => Some(inst),
            };

            if let Some(inst) = inst {
                result.push(AnnotatedInstr::new(var, inst, ty));
            }
        }

        bb.insts = result;
    }

    Ok(())
}

pub fn optimize(funcs: &Functions, ir_ctx: &mut IrContext) -> Result<()> {
    let mut ctx = Context {
        env: FxHashMap::default(),
    };
    for fun in funcs {
        fold_constants_insts(fun, &mut ctx, ir_ctx)?;
    }

    for fun in funcs {
        remove_deadcode(fun, ir_ctx)?;
    }

    Ok(())
}
