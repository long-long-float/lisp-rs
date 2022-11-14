use std::fmt::Display;

use anyhow::Result;

use super::{
    ast::*, environment::Environment, parser::*, typer::Type, unique_generator::UniqueGenerator,
};

#[derive(Clone, PartialEq, Debug)]
pub enum Instruction {
    Branch {
        cond: Operand,
        then_label: Label,
        else_label: Label,
    },
    Jump(Label),

    Add(Operand, Operand),
    Phi(Vec<(Operand, Label)>),

    Operand(Operand),
    Label(Label),
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Instruction::*;

        match self {
            Branch {
                cond,
                then_label,
                else_label,
            } => {
                write!(f, "branch {}, {}, {}", cond, then_label, else_label)
            }
            Jump(label) => {
                write!(f, "jump {}", label)
            }
            Add(left, right) => {
                write!(f, "add {}, {}", left, right)
            }
            Phi(nodes) => {
                write!(f, "phi ")?;
                for (val, label) in nodes {
                    write!(f, "[{}, {}], ", val, label)?;
                }
                Ok(())
            }
            Operand(op) => {
                write!(f, "{}", op)
            }
            Label(label) => {
                write!(f, "{}", label)
            }
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct AnnotatedInstr {
    pub result: Variable,
    pub inst: Instruction,
    pub ty: Type,
}

impl Display for AnnotatedInstr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Instruction::*;
        match &self.inst {
            Branch { .. } | Jump(_) => {
                write!(f, "  {}", self.inst)
            }

            Add(_, _) | Operand(_) | Phi(_) => {
                write!(f, "  {}:{} = {}", self.result, self.ty, self.inst)
            }

            Label(_) => {
                write!(f, "{}:", self.inst)
            }
        }
    }
}

type Instructions = Vec<AnnotatedInstr>;

#[derive(Clone, PartialEq, Debug)]
pub enum Operand {
    Variable(Variable),
    Immediate(Immediate),
}

impl Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Operand::*;

        match self {
            Variable(v) => write!(f, "{}", v),
            Immediate(v) => write!(f, "{:?}", v),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Label {
    name: String,
}

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Variable {
    name: String,
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%{}", self.name)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Immediate {
    Integer(i32),
    Boolean(bool),
}

struct Context {
    env: Environment<Variable>,
    var_gen: UniqueGenerator,
}

impl Context {
    fn gen_var(&mut self) -> Variable {
        Variable {
            name: format!("var{}", self.var_gen.gen()),
        }
    }

    fn gen_label(&mut self) -> Label {
        Label {
            name: format!("label{}", self.var_gen.gen()),
        }
    }
}

fn compile_ast(ast: &AnnotatedAst, ctx: &mut Context) -> Result<Instructions> {
    use Instruction as I;

    let AnnotatedAst {
        ast,
        location: _,
        ty: ast_ty,
    } = ast;

    let mut result = Vec::new();

    fn get_last_var(insts: &Instructions) -> AnnotatedInstr {
        insts.last().unwrap().clone()
    }

    fn compile_and_add(
        result: &mut Vec<AnnotatedInstr>,
        ast: &AnnotatedAst,
        ctx: &mut Context,
    ) -> Result<AnnotatedInstr> {
        let mut insts = compile_ast(ast, ctx)?;
        let inst = get_last_var(&insts);
        result.append(&mut insts);
        Ok(inst)
    }

    fn add_instr(result: &mut Vec<AnnotatedInstr>, ctx: &mut Context, inst: Instruction, ty: Type) {
        result.push(AnnotatedInstr {
            result: ctx.gen_var(),
            inst,
            ty,
        });
    }

    match ast {
        Ast::List(vs) => {
            if let Some((fun, args)) = vs.split_first() {
                let args = args
                    .iter()
                    .map(|arg| compile_ast(arg, ctx))
                    .collect::<Result<Vec<_>>>()?;

                result.append(&mut args.clone().into_iter().flatten().collect::<Vec<_>>());

                if let AnnotatedAst {
                    ast: Ast::Symbol(fun),
                    ..
                } = fun
                {
                    let name = fun.value.as_str();
                    match name {
                        "+" => {
                            let AnnotatedInstr {
                                result: left,
                                inst,
                                ty,
                            } = get_last_var(&args[0]);
                            let right = get_last_var(&args[1]).result;

                            add_instr(
                                &mut result,
                                ctx,
                                I::Add(Operand::Variable(left), Operand::Variable(right)),
                                ty,
                            );
                        }
                        _ => {}
                    }
                }
            } else {
            }
        }
        Ast::Quoted(_) => todo!(),
        Ast::Integer(v) => add_instr(
            &mut result,
            ctx,
            I::Operand(Operand::Immediate(Immediate::Integer(*v))),
            ast_ty.clone(),
        ),
        Ast::Float(_) => todo!(),
        Ast::Symbol(sym) => {
            let var = ctx.env.find_var(sym).unwrap();
            add_instr(
                &mut result,
                ctx,
                I::Operand(Operand::Variable(var)),
                ast_ty.clone(),
            );
        }
        Ast::SymbolWithType(_, _) => todo!(),
        Ast::Boolean(v) => add_instr(
            &mut result,
            ctx,
            I::Operand(Operand::Immediate(Immediate::Boolean(*v))),
            ast_ty.clone(),
        ),
        Ast::Char(_) => todo!(),
        Ast::String(_) => todo!(),
        Ast::Nil => todo!(),
        Ast::DefineMacro(_) => todo!(),
        Ast::Define(Define { id, init }) => {
            let inst = compile_and_add(&mut result, init, ctx)?;
            ctx.env.insert_var(id.clone(), inst.result);
        }
        Ast::Lambda(Lambda { args, body }) => todo!(),
        Ast::Assign(_) => todo!(),
        Ast::IfExpr(IfExpr {
            cond,
            then_ast,
            else_ast,
        }) => {
            let cond = compile_and_add(&mut result, cond, ctx)?;
            let then_label = ctx.gen_label();
            let else_label = ctx.gen_label();
            let end_label = ctx.gen_label();

            add_instr(
                &mut result,
                ctx,
                I::Branch {
                    cond: Operand::Variable(cond.result),
                    then_label: then_label.clone(),
                    else_label: else_label.clone(),
                },
                Type::None,
            );

            add_instr(&mut result, ctx, I::Label(then_label.clone()), Type::None);
            let then_res = compile_and_add(&mut result, then_ast, ctx)?;
            add_instr(&mut result, ctx, I::Jump(end_label.clone()), Type::None);

            add_instr(&mut result, ctx, I::Label(else_label.clone()), Type::None);
            let else_res = if let Some(else_ast) = else_ast {
                Some(compile_and_add(&mut result, else_ast, ctx)?)
            } else {
                None
            };
            add_instr(&mut result, ctx, I::Jump(end_label.clone()), Type::None);

            add_instr(&mut result, ctx, I::Label(end_label), Type::None);
            if let Some(else_res) = else_res {
                add_instr(
                    &mut result,
                    ctx,
                    I::Phi(vec![
                        (Operand::Variable(then_res.result), then_label),
                        (Operand::Variable(else_res.result), else_label),
                    ]),
                    ast_ty.clone(),
                );
            }
        }
        Ast::Cond(_) => todo!(),
        Ast::Let(_) => todo!(),
        Ast::Begin(_) => todo!(),
        Ast::BuildList(_) => todo!(),
        Ast::Loop(_) => todo!(),
        Ast::Continue(_) => todo!(),
    }

    Ok(result)
}

pub fn compile(asts: Program) -> Result<Instructions> {
    let mut result = Vec::new();

    let mut ctx = Context {
        env: Environment::new(),
        var_gen: UniqueGenerator::new(),
    };

    result.push(AnnotatedInstr {
        result: ctx.gen_var(),
        inst: Instruction::Label(Label {
            name: "main".to_string(),
        }),
        ty: Type::None,
    });

    for ast in asts {
        let mut insts = compile_ast(&ast, &mut ctx)?;
        result.append(&mut insts);
    }

    Ok(result)
}
