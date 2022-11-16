use anyhow::Result;
use rustc_hash::FxHashMap;

use super::super::ir::*;

fn remove_deadcode(insts: Instructions) -> Result<Instructions> {
    Ok(insts)
}

fn fold_constants_insts(insts: Instructions) -> Result<Instructions> {
    let mut result = Vec::new();
    let mut env = FxHashMap::default();

    fn fold_imm(env: &mut FxHashMap<String, Immediate>, op: Operand) -> Operand {
        match op {
            Operand::Variable(var) => {
                if let Some(imm) = env.get(&var.name) {
                    Operand::Immediate(imm.clone())
                } else {
                    Operand::Variable(var)
                }
            }
            Operand::Immediate(_) | Operand::Label(_) => op,
        }
    }

    fn insert_imm(env: &mut FxHashMap<String, Immediate>, op: &Operand, var: &Variable) {
        match op {
            Operand::Immediate(imm) => {
                env.insert(var.name.clone(), imm.clone());
            }
            Operand::Variable(_) | Operand::Label(_) => {}
        }
    }

    for AnnotatedInstr {
        result: var,
        inst,
        ty,
    } in insts
    {
        match inst {
            Instruction::Operand(Operand::Immediate(imm)) => {
                env.insert(var.name, imm);
            }
            Instruction::Operand(op @ Operand::Variable(_)) => {
                let op = fold_imm(&mut env, op);
                insert_imm(&mut env, &op, &var);
                result.push(AnnotatedInstr {
                    result: var,
                    inst: Instruction::Operand(op),
                    ty,
                });
            }

            Instruction::Branch {
                cond,
                then_label,
                else_label,
            } => {
                let cond = fold_imm(&mut env, cond);
                result.push(AnnotatedInstr {
                    result: var,
                    inst: Instruction::Branch {
                        cond,
                        then_label,
                        else_label,
                    },
                    ty,
                });
            }

            Instruction::Add(left, right) => {
                let left = fold_imm(&mut env, left);
                let right = fold_imm(&mut env, right);

                if let (
                    Operand::Immediate(Immediate::Integer(left)),
                    Operand::Immediate(Immediate::Integer(right)),
                ) = (&left, &right)
                {
                    let val = left + right;

                    let op = Operand::Immediate(Immediate::Integer(val));
                    insert_imm(&mut env, &op, &var);
                    result.push(AnnotatedInstr {
                        result: var,
                        inst: Instruction::Operand(op),
                        ty,
                    })
                } else {
                    result.push(AnnotatedInstr {
                        result: var,
                        inst: Instruction::Add(left, right),
                        ty,
                    });
                }
            }

            Instruction::Sub(_, _) => todo!(),
            Instruction::Mul(_, _) => todo!(),
            Instruction::Cmp(_, _, _) => todo!(),
            Instruction::Call { fun, args } => {
                let fun = fold_imm(&mut env, fun);
                let args = args
                    .into_iter()
                    .map(|arg| fold_imm(&mut env, arg))
                    .collect();

                result.push(AnnotatedInstr {
                    result: var,
                    inst: Instruction::Call { fun, args },
                    ty,
                });
            }

            Instruction::Operand(_)
            | Instruction::Jump(_)
            | Instruction::Ret(_)
            | Instruction::Phi(_)
            | Instruction::Label(_) => result.push(AnnotatedInstr {
                result: var,
                inst,
                ty,
            }),
        }
    }

    Ok(result)
}

pub fn optimize(funcs: Functions) -> Result<Functions> {
    let funcs = funcs
        .into_iter()
        .map(
            |Function {
                 name,
                 args,
                 body,
                 ty,
             }| {
                let body = fold_constants_insts(body)?;
                let body = remove_deadcode(body)?;
                Ok(Function {
                    name,
                    args,
                    body,
                    ty,
                })
            },
        )
        .collect::<Result<Vec<_>>>()?;

    Ok(funcs)
}
