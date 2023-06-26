use anyhow::Result;

use crate::lispi::{
    ir::{basic_block::*, instruction::*, IrContext},
    ty::Type,
    unique_generator::UniqueGenerator,
};

use Instruction as I;

enum ImmediateUnfoldingMode {
    None,
    Left,
    Both,
}

#[derive(Default)]
struct Context {
    var_gen: UniqueGenerator,
}

fn unfold_immediate(
    op: Operand,
    insts: &mut Vec<AnnotatedInstr>,
    result: &Variable,
    ctx: &mut Context,
) -> Operand {
    match op {
        Operand::Variable(_) => op,
        Operand::Immediate(_) => {
            let var = Variable {
                // Set unique ID in entire program
                name: format!("var{}.uf", ctx.var_gen.gen()),
            };
            insts.push(AnnotatedInstr {
                result: var.clone(),
                inst: I::Operand(op),
                ty: Type::None,
                tags: Vec::new(),
            });
            Operand::Variable(var)
        }
    }
}

fn unfold_immediate_arith<F>(
    left: Operand,
    right: Operand,
    constructor: F,
    insts: &mut Vec<AnnotatedInstr>,
    result: &Variable,
    mode: ImmediateUnfoldingMode,
    ctx: &mut Context,
) -> Instruction
where
    F: Fn(Operand, Operand) -> Instruction,
{
    use ImmediateUnfoldingMode as m;

    match mode {
        m::None => constructor(left, right),
        m::Left => {
            let unfolded_left = unfold_immediate(left, insts, result, ctx);
            constructor(unfolded_left, right)
        }
        m::Both => {
            let unfolded_right = unfold_immediate(right, insts, result, ctx);
            let unfolded_left = unfold_immediate(left, insts, result, ctx);
            constructor(unfolded_left, unfolded_right)
        }
    }
}

pub fn optimize(
    funcs: &Functions,
    ir_ctx: &mut IrContext,
    unfolding_for_riscv: bool,
) -> Result<()> {
    let mut ctx = Context::default();

    for fun in funcs {
        for bb in &fun.basic_blocks {
            let bb = ir_ctx.bb_arena.get_mut(*bb).unwrap();

            let mut insts = Vec::new();

            for AnnotatedInstr {
                result,
                inst,
                ty,
                tags,
            } in bb.insts.drain(..)
            {
                let mode = if unfolding_for_riscv {
                    ImmediateUnfoldingMode::Left
                } else {
                    ImmediateUnfoldingMode::None
                };

                let inst = match inst {
                    I::Operand(_)
                    | I::Alloca { .. }
                    | I::Jump(_, _)
                    | I::Call { .. }
                    | I::Phi(_)
                    | I::Label(_)
                    | I::Nop => Some(inst),
                    I::Branch {
                        cond,
                        then_label,
                        else_label,
                        then_bb,
                        else_bb,
                    } => {
                        let cond = if unfolding_for_riscv {
                            unfold_immediate(cond, &mut insts, &result, &mut ctx)
                        } else {
                            cond
                        };
                        Some(I::Branch {
                            cond,
                            then_label,
                            else_label,
                            then_bb,
                            else_bb,
                        })
                    }

                    I::Add(left, right) => Some(unfold_immediate_arith(
                        left,
                        right,
                        I::Add,
                        &mut insts,
                        &result,
                        mode,
                        &mut ctx,
                    )),
                    I::Sub(left, right) => Some(unfold_immediate_arith(
                        left,
                        right,
                        I::Sub,
                        &mut insts,
                        &result,
                        ImmediateUnfoldingMode::Both,
                        &mut ctx,
                    )),
                    I::Mul(left, right) => Some(unfold_immediate_arith(
                        left,
                        right,
                        I::Mul,
                        &mut insts,
                        &result,
                        ImmediateUnfoldingMode::Both,
                        &mut ctx,
                    )),
                    I::Or(left, right) => Some(unfold_immediate_arith(
                        left,
                        right,
                        I::Or,
                        &mut insts,
                        &result,
                        mode,
                        &mut ctx,
                    )),

                    I::Shift(op, left, right) => Some(unfold_immediate_arith(
                        left,
                        right,
                        |l, r| I::Shift(op, l, r),
                        &mut insts,
                        &result,
                        mode,
                        &mut ctx,
                    )),

                    I::Store(addr, value) => {
                        if unfolding_for_riscv {
                            let addr = unfold_immediate(addr, &mut insts, &result, &mut ctx);
                            let value = unfold_immediate(value, &mut insts, &result, &mut ctx);
                            Some(I::Store(addr, value))
                        } else {
                            Some(I::Store(addr, value))
                        }
                    }
                    I::LoadElement { addr, ty, index } => Some(I::LoadElement {
                        addr: unfold_immediate(addr, &mut insts, &result, &mut ctx),
                        ty,
                        index,
                    }),
                    I::StoreElement {
                        addr,
                        ty,
                        index,
                        value,
                    } => Some(I::StoreElement {
                        addr: unfold_immediate(addr, &mut insts, &result, &mut ctx),
                        ty,
                        index,
                        value: unfold_immediate(value, &mut insts, &result, &mut ctx),
                    }),
                    // The argument of Not must be an operand.
                    I::Not(_) => Some(inst),
                    I::Cmp(op, left, right) => Some(unfold_immediate_arith(
                        left,
                        right,
                        |l, r| I::Cmp(op, l, r),
                        &mut insts,
                        &result,
                        ImmediateUnfoldingMode::Both,
                        &mut ctx,
                    )),
                    I::Ret(op) => {
                        if unfolding_for_riscv {
                            Some(I::Ret(unfold_immediate(op, &mut insts, &result, &mut ctx)))
                        } else {
                            Some(I::Ret(op))
                        }
                    }
                };

                if let Some(inst) = inst {
                    insts.push(AnnotatedInstr {
                        result,
                        inst,
                        ty,
                        tags,
                    })
                }
            }

            bb.insts = insts;
        }
    }

    Ok(())
}
