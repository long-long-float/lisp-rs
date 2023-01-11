use std::collections::HashSet;

use anyhow::Result;
use rustc_hash::FxHashMap;

use super::super::ir::instruction::*;

use Instruction as I;

struct Context {
    env: FxHashMap<String, Immediate>,
}

fn remove_deadcode(insts: Instructions) -> Result<Instructions> {
    let mut result = Vec::new();

    let mut used_vars = HashSet::new();

    fn register_as_used(used_vars: &mut HashSet<Variable>, op: &Operand) {
        if let Operand::Variable(var) = op {
            used_vars.insert(var.clone());
        }
    }

    for AnnotatedInstr {
        result: var,
        inst,
        ty,
    } in insts.into_iter().rev()
    {
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

            Instruction::Add(l, r)
            | Instruction::Sub(l, r)
            | Instruction::Mul(l, r)
            | Instruction::Or(l, r)
            | Instruction::Store(l, r)
            | Instruction::Cmp(_, l, r) => {
                register_as_used(&mut used_vars, l);
                register_as_used(&mut used_vars, r);
            }

            Instruction::Call { fun, args } => {
                register_as_used(&mut used_vars, fun);
                args.iter()
                    .for_each(|arg| register_as_used(&mut used_vars, arg));
            }

            Instruction::Phi(nodes) => {
                nodes
                    .iter()
                    .for_each(|(op, _)| register_as_used(&mut used_vars, op));
            }

            Instruction::Operand(op) => register_as_used(&mut used_vars, op),

            Instruction::Jump(_, _) | Instruction::Label(_) => {}
        }

        if inst.is_label() || inst.is_terminal() || used_vars.contains(&var) {
            result.push(AnnotatedInstr {
                result: var,
                inst,
                ty,
            });
        }
    }

    Ok(result.into_iter().rev().collect())
}

fn fold_constants_insts(insts: Instructions) -> Result<Instructions> {
    let mut result = Vec::new();
    let mut ctx = Context {
        env: FxHashMap::default(),
    };

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
        let left = fold_imm(ctx, left);
        let right = fold_imm(ctx, right);

        if let (
            Operand::Immediate(Immediate::Integer(left)),
            Operand::Immediate(Immediate::Integer(right)),
        ) = (&left, &right)
        {
            let val = if_int(*left, *right);

            let op = Operand::Immediate(Immediate::Integer(val));
            insert_imm(ctx, &op, &var);
            I::Operand(op)
        } else {
            if_else(left, right)
        }
    }

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
        let left = fold_imm(ctx, left);
        let right = fold_imm(ctx, right);

        if let (
            Operand::Immediate(Immediate::Boolean(left)),
            Operand::Immediate(Immediate::Boolean(right)),
        ) = (&left, &right)
        {
            let val = if_int(*left, *right);

            let op = Operand::Immediate(Immediate::Boolean(val));
            insert_imm(ctx, &op, &var);
            I::Operand(op)
        } else {
            if_else(left, right)
        }
    }

    for AnnotatedInstr {
        result: var,
        inst,
        ty,
    } in insts
    {
        let inst = match inst {
            I::Operand(Operand::Immediate(imm)) => {
                ctx.env.insert(var.name.clone(), imm);
                None
            }
            I::Operand(op @ Operand::Variable(_)) => {
                let op = fold_imm(&mut ctx, op);
                insert_imm(&mut ctx, &op, &var);
                Some(I::Operand(op))
            }

            I::Branch {
                cond,
                then_label,
                else_label,
                then_bb,
                else_bb,
            } => {
                let cond = fold_imm(&mut ctx, cond);
                Some(I::Branch {
                    cond,
                    then_label,
                    else_label,
                    then_bb,
                    else_bb,
                })
            }

            I::Add(left, right) => Some(fold_constants_arith(
                &mut ctx,
                &var,
                left,
                right,
                |l, r| l + r,
                |l, r| I::Add(l, r),
            )),
            I::Sub(left, right) => Some(fold_constants_arith(
                &mut ctx,
                &var,
                left,
                right,
                |l, r| l - r,
                |l, r| I::Sub(l, r),
            )),
            I::Mul(left, right) => Some(fold_constants_arith(
                &mut ctx,
                &var,
                left,
                right,
                |l, r| l * r,
                |l, r| I::Mul(l, r),
            )),
            I::Or(left, right) => Some(fold_constants_logical(
                &mut ctx,
                &var,
                left,
                right,
                |l, r| l | r,
                |l, r| I::Or(l, r),
            )),
            I::Store(addr, value) => {
                let addr = fold_imm(&mut ctx, addr);
                let value = fold_imm(&mut ctx, value);

                Some(I::Store(addr, value))
            }

            I::Cmp(op, left, right) => {
                let left = fold_imm(&mut ctx, left);
                let right = fold_imm(&mut ctx, right);

                if let (
                    Operand::Immediate(Immediate::Integer(left)),
                    Operand::Immediate(Immediate::Integer(right)),
                ) = (&left, &right)
                {
                    let val = match op {
                        CmpOperator::SGE => left <= right,
                    };

                    let op = Operand::Immediate(Immediate::Boolean(val));
                    insert_imm(&mut ctx, &op, &var);
                    Some(I::Operand(op))
                } else {
                    Some(I::Cmp(op, left, right))
                }
            }
            I::Call { fun, args } => {
                let fun = fold_imm(&mut ctx, fun);
                let args = args
                    .into_iter()
                    .map(|arg| fold_imm(&mut ctx, arg))
                    .collect();

                Some(I::Call { fun, args })
            }

            I::Jump(_, _) | I::Ret(_) | I::Phi(_) | I::Label(_) => Some(inst),
        };

        if let Some(inst) = inst {
            result.push(AnnotatedInstr {
                result: var,
                inst,
                ty,
            });
        }
    }

    Ok(result)
}

pub fn optimize(funcs: Functions) -> Result<Functions> {
    let funcs = funcs
        .into_iter()
        .map(|f| {
            f.replace_body_with(|body| {
                let body = fold_constants_insts(body)?;
                remove_deadcode(body)
            })
        })
        .collect::<Result<Vec<_>>>()?;

    Ok(funcs)
}
