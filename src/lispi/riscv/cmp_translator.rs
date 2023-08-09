use anyhow::Result;

use crate::lispi::{
    ir::{basic_block::*, instruction::*, IrContext},
    ty::Type,
    unique_generator::UniqueGenerator,
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
                        SGE => {
                            let iresult = Variable {
                                name: format!("{}-ct", result.name),
                            };
                            insts.push(AnnotatedInstr::new(
                                iresult.clone(),
                                I::Cmp(SLT, left.clone(), right.clone()),
                                ty,
                            ));
                            insts.push(AnnotatedInstr::new(
                                result,
                                I::Not(iresult.into()),
                                Type::Boolean,
                            ));
                        }
                        SLE => todo!(),
                        SGT => todo!(),
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
