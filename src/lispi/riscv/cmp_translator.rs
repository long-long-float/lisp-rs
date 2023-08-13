use anyhow::Result;

use crate::lispi::{
    ir::{basic_block::*, instruction::*, IrContext},
    ty::Type,
};

use Instruction as I;

pub fn translate(funcs: &Functions, ir_ctx: &mut IrContext) -> Result<()> {
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
                if let I::Cmp(op, left, right) = &inst {
                    use CmpOperator::*;

                    match op {
                        Eq => todo!(),
                        // left >= right <=> !(left < right)
                        SGE => {
                            let iresult = Variable {
                                name: format!("{}-ct", result.name),
                            };
                            insts.push(
                                AnnotatedInstr::new(
                                    iresult.clone(),
                                    I::Cmp(SLT, left.clone(), right.clone()),
                                    ty,
                                )
                                .with_tags(tags),
                            );
                            insts.push(AnnotatedInstr::new(
                                result,
                                I::Not(iresult.into()),
                                Type::Boolean,
                            ));
                        }
                        // left <= right <=> !(right < left)
                        SLE => {
                            let iresult = Variable {
                                name: format!("{}-ct", result.name),
                            };
                            insts.push(
                                AnnotatedInstr::new(
                                    iresult.clone(),
                                    I::Cmp(SLT, right.clone(), left.clone()),
                                    ty,
                                )
                                .with_tags(tags),
                            );
                            insts.push(AnnotatedInstr::new(
                                result,
                                I::Not(iresult.into()),
                                Type::Boolean,
                            ));
                        }
                        // left > right <=> right < left
                        SGT => {
                            insts.push(
                                AnnotatedInstr::new(
                                    result,
                                    I::Cmp(SLT, right.clone(), left.clone()),
                                    ty,
                                )
                                .with_tags(tags),
                            );
                        }
                        SLT => insts.push(AnnotatedInstr {
                            result,
                            inst,
                            ty,
                            tags,
                        }),
                    }
                } else {
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
