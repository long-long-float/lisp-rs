use std::fmt::Display;

use anyhow::Result;

use super::{ast::*, parser::*, unique_generator::UniqueGenerator};

#[derive(Clone, PartialEq, Debug)]
pub enum Instruction {
    Add(Operand, Operand),
    Immediate(Immediate),
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Instruction::*;

        match self {
            Add(left, right) => {
                write!(f, "add {}, {}", left, right)
            }
            Immediate(imm) => {
                write!(f, "{:?}", imm)
            }
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct AnnotatedInstr {
    pub result: Variable,
    pub inst: Instruction,
}

impl Display for AnnotatedInstr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.result, self.inst)
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
}

struct Context {
    var_gen: UniqueGenerator,
}

impl Context {
    fn gen_var(&mut self) -> Variable {
        Variable {
            name: format!("var{}", self.var_gen.gen()),
        }
    }
}

fn get_last_var(insts: &Instructions) -> Variable {
    insts.last().unwrap().result.clone()
}

fn compile_ast(ast: &AnnotatedAst, ctx: &mut Context) -> Result<Instructions> {
    let AnnotatedAst {
        ast,
        location: _,
        ty: _,
    } = ast;

    let mut result = Vec::new();

    match ast {
        Ast::List(vs) => {
            if let Some((fun, args)) = vs.split_first() {
                let args = args
                    .iter()
                    .map(|arg| compile_ast(arg, ctx))
                    .collect::<Result<Vec<_>>>()?;

                result = args.clone().into_iter().flatten().collect::<Vec<_>>();

                if let AnnotatedAst {
                    ast: Ast::Symbol(fun),
                    ..
                } = fun
                {
                    let name = fun.value.as_str();
                    match name {
                        "+" => {
                            let left = get_last_var(&args[0]);
                            let right = get_last_var(&args[1]);

                            result.push(AnnotatedInstr {
                                result: ctx.gen_var(),
                                inst: Instruction::Add(
                                    Operand::Variable(left),
                                    Operand::Variable(right),
                                ),
                            });
                        }
                        _ => {}
                    }
                }
            } else {
            }
        }
        Ast::Quoted(_) => todo!(),
        Ast::Integer(v) => result.push(AnnotatedInstr {
            result: ctx.gen_var(),
            inst: Instruction::Immediate(Immediate::Integer(*v)),
        }),
        Ast::Float(_) => todo!(),
        Ast::Symbol(_) => todo!(),
        Ast::SymbolWithType(_, _) => todo!(),
        Ast::Boolean(_) => todo!(),
        Ast::Char(_) => todo!(),
        Ast::String(_) => todo!(),
        Ast::Nil => todo!(),
        Ast::DefineMacro(_) => todo!(),
        Ast::Define(_) => todo!(),
        Ast::Lambda(_) => todo!(),
        Ast::Assign(_) => todo!(),
        Ast::IfExpr(_) => todo!(),
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
        var_gen: UniqueGenerator::new(),
    };

    for ast in asts {
        let mut insts = compile_ast(&ast, &mut ctx)?;
        result.append(&mut insts);
    }

    Ok(result)
}
