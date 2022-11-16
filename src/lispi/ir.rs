use std::{fmt::Display, vec};

use anyhow::Result;

use super::{
    ast::*, environment::Environment, error::Error, parser::*, typer::Type,
    unique_generator::UniqueGenerator,
};
use crate::bug;

#[derive(Clone, PartialEq, Debug)]
pub enum Instruction {
    Branch {
        cond: Operand,
        then_label: Label,
        else_label: Label,
    },
    Jump(Label),
    Ret(Operand),

    Add(Operand, Operand),
    Sub(Operand, Operand),
    Mul(Operand, Operand),
    Cmp(CmpOperator, Operand, Operand),
    Call {
        fun: Operand,
        args: Vec<Operand>,
    },
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
            Ret(val) => {
                write!(f, "ret {}", val)
            }
            Add(left, right) => {
                write!(f, "add {}, {}", left, right)
            }
            Sub(left, right) => {
                write!(f, "sub {}, {}", left, right)
            }
            Mul(left, right) => {
                write!(f, "mul {}, {}", left, right)
            }
            Cmp(op, left, right) => {
                write!(f, "cmp {}, {}, {}", op, left, right)
            }
            Call { fun, args } => {
                write!(f, "call {}", fun)?;
                for arg in args {
                    write!(f, ", {}", arg)?;
                }
                Ok(())
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
            Branch { .. } | Jump(_) | Ret(_) => {
                write!(f, "  {}", self.inst)
            }

            Add(_, _)
            | Sub(_, _)
            | Mul(_, _)
            | Cmp(_, _, _)
            | Call { .. }
            | Operand(_)
            | Phi(_) => {
                write!(f, "  {}:{} = {}", self.result, self.ty, self.inst)
            }

            Label(_) => {
                write!(f, "{}:", self.inst)
            }
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Function {
    pub name: String,
    pub args: Vec<(String, Type)>,
    pub body: Instructions,
    pub ty: Type,
}

impl Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (", self.name)?;
        for (id, ty) in &self.args {
            write!(f, "%{}: {}, ", id, ty)?;
        }
        writeln!(f, "): {} {{", self.ty)?;
        for inst in &self.body {
            writeln!(f, "{}", inst)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

pub type Instructions = Vec<AnnotatedInstr>;
pub type Functions = Vec<Function>;

#[derive(Clone, PartialEq, Debug)]
pub enum Operand {
    Variable(Variable),
    Immediate(Immediate),
    Label(Label),
}

impl Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Operand::*;

        match self {
            Variable(v) => write!(f, "{}", v),
            Immediate(v) => write!(f, "{:?}", v),
            Label(v) => write!(f, "{}", v),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum CmpOperator {
    SGE,
}

impl Display for CmpOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use CmpOperator::*;

        match self {
            SGE => write!(f, "<="),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Label {
    pub name: String,
}

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Variable {
    pub name: String,
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
    sym_table: SymbolTable,
    func_env: Environment<(Label, Function)>,
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

fn get_last_instr(insts: &Instructions) -> AnnotatedInstr {
    insts.last().unwrap().clone()
}

fn compile_and_add(
    result: &mut Vec<AnnotatedInstr>,
    ast: AnnotatedAst,
    ctx: &mut Context,
) -> Result<AnnotatedInstr> {
    let mut insts = compile_ast(ast, ctx)?;
    let inst = get_last_instr(&insts);
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

fn compile_ast(ast: AnnotatedAst, ctx: &mut Context) -> Result<Instructions> {
    use Instruction as I;

    let AnnotatedAst {
        ast,
        location: _,
        ty: ast_ty,
    } = ast;

    let mut result = Vec::new();

    match ast {
        Ast::List(vs) => {
            if let Some((fun_ast, args)) = vs.split_first() {
                let args = args
                    .iter()
                    .map(|arg| compile_and_add(&mut result, arg.clone(), ctx))
                    .collect::<Result<Vec<_>>>()?;

                // result.append(&mut args.clone().into_iter().flatten().collect::<Vec<_>>());

                if let AnnotatedAst {
                    ast: Ast::Symbol(fun),
                    ..
                } = fun_ast
                {
                    let name = fun.value.as_str();
                    match name {
                        "+" | "-" | "*" | "<=" => {
                            let AnnotatedInstr {
                                result: left,
                                inst: _inst,
                                ty,
                            } = args[0].clone();
                            let right = args[1].result.clone();

                            let inst = match name {
                                "+" => I::Add(Operand::Variable(left), Operand::Variable(right)),
                                "-" => I::Sub(Operand::Variable(left), Operand::Variable(right)),
                                "*" => I::Mul(Operand::Variable(left), Operand::Variable(right)),
                                "<=" => I::Cmp(
                                    CmpOperator::SGE,
                                    Operand::Variable(left),
                                    Operand::Variable(right),
                                ),
                                _ => return Err(bug!()),
                            };
                            add_instr(&mut result, ctx, inst, ast_ty);
                        }
                        _ => {
                            let fun = compile_and_add(&mut result, fun_ast.clone(), ctx)?;
                            // let fun_label = ctx.func_env.find_var(fun).unwrap();
                            let args = args
                                .into_iter()
                                .map(|arg| Operand::Variable(arg.result))
                                .collect();
                            add_instr(
                                &mut result,
                                ctx,
                                I::Call {
                                    fun: Operand::Variable(fun.result),
                                    args,
                                },
                                ast_ty,
                            );
                        }
                    }
                }
            } else {
            }
        }
        Ast::Quoted(_) => todo!(),
        Ast::Integer(v) => add_instr(
            &mut result,
            ctx,
            I::Operand(Operand::Immediate(Immediate::Integer(v))),
            ast_ty,
        ),
        Ast::Float(_) => todo!(),
        Ast::Symbol(sym) => {
            if let Some((label, _)) = ctx.func_env.find_var(&sym) {
                add_instr(&mut result, ctx, I::Operand(Operand::Label(label)), ast_ty);
            } else if let Some(var) = ctx.env.find_var(&sym) {
                add_instr(&mut result, ctx, I::Operand(Operand::Variable(var)), ast_ty);
            } else {
                return Err(Error::UndefinedVariable(sym.value)
                    .with_null_location()
                    .into());
            }
        }
        Ast::SymbolWithType(_, _) => todo!(),
        Ast::Boolean(v) => add_instr(
            &mut result,
            ctx,
            I::Operand(Operand::Immediate(Immediate::Boolean(v))),
            ast_ty,
        ),
        Ast::Char(_) => todo!(),
        Ast::String(_) => todo!(),
        Ast::Nil => todo!(),
        Ast::DefineMacro(_) => todo!(),
        Ast::Define(Define { id, init }) => {
            let inst = compile_and_add(&mut result, *init, ctx)?;
            ctx.env.insert_var(id.clone(), inst.result);
        }
        Ast::Assign(Assign {
            var,
            var_loc: _,
            value,
        }) => {
            let value = compile_and_add(&mut result, *value, ctx)?;
            ctx.env.update_var(var, &value.result)?;
        }
        Ast::IfExpr(IfExpr {
            cond,
            then_ast,
            else_ast,
        }) => {
            let cond = compile_and_add(&mut result, *cond, ctx)?;
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
            let then_res = compile_and_add(&mut result, *then_ast, ctx)?;
            add_instr(&mut result, ctx, I::Jump(end_label.clone()), Type::None);

            add_instr(&mut result, ctx, I::Label(else_label.clone()), Type::None);
            let else_res = if let Some(else_ast) = else_ast {
                Some(compile_and_add(&mut result, *else_ast, ctx)?)
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
                    ast_ty,
                );
            }
        }
        Ast::Cond(_) => todo!(),
        Ast::Let(Let {
            sequential,
            proc_id,
            inits,
            body,
        }) => {
            for (id, init) in inits {
                // sequential
                let inst = compile_and_add(&mut result, init, ctx)?;
                ctx.env.insert_var(id, inst.result);
            }

            result.append(&mut compile_asts(body, ctx)?);
        }
        Ast::Begin(_) => todo!(),
        Ast::BuildList(_) => todo!(),
        Ast::Loop(_) => todo!(),
        Ast::Continue(_) => todo!(),

        Ast::Lambda(_) => {}
    }

    Ok(result)
}

fn compile_lambdas_ast(ast: AnnotatedAst, ctx: &mut Context) -> Result<AnnotatedAst> {
    let AnnotatedAst { ast, location, ty } = ast;

    match ast {
        Ast::Lambda(Lambda { args, body }) => {
            let args = args
                .into_iter()
                .map(|arg| {
                    let name = arg.value.clone();
                    ctx.env.insert_var(arg, Variable { name: name.clone() });

                    (name, Type::None)
                })
                .collect::<Vec<_>>();

            let name = ctx
                .sym_table
                .create_symbol_value(format!("fun{}", ctx.var_gen.gen_string()));
            let label = Label {
                name: name.value.clone(),
            };

            ctx.env.push_local();

            let insts = compile_asts(body, ctx)?;

            ctx.env.pop_local();

            let fun = Function {
                name: name.value.clone(),
                args,
                body: insts,
                ty: ty.clone(),
            };

            ctx.func_env.insert_var(name.clone(), (label, fun));

            Ok(AnnotatedAst {
                ast: Ast::Symbol(name),
                location,
                ty,
            })
        }
        Ast::Let(Let {
            sequential,
            proc_id,
            inits,
            body,
        }) => {
            if let Some(proc_id) = proc_id {
                let mut aargs = Vec::new();
                let mut fargs = Vec::new();
                for (id, init) in inits {
                    ctx.env.insert_var(
                        id.clone(),
                        Variable {
                            name: id.value.clone(),
                        },
                    );
                    fargs.push((id.value, init.ty.clone()));
                    aargs.push(init);
                }

                let label = Label {
                    name: proc_id.value.clone(),
                };

                ctx.env.push_local();

                let mut fun = Function {
                    name: proc_id.value.clone(),
                    args: fargs,
                    body: Vec::new(),
                    ty: Type::None,
                };

                ctx.func_env
                    .insert_var(proc_id.clone(), (label.clone(), fun.clone()));

                let insts = compile_asts(body, ctx)?;

                ctx.env.pop_local();

                fun.body = insts;
                ctx.func_env.update_var(proc_id.clone(), &(label, fun))?;

                let mut apply = vec![Ast::Symbol(proc_id).with_null_location()];
                apply.append(&mut aargs);

                Ok(AnnotatedAst {
                    ast: Ast::List(apply),
                    location,
                    ty,
                })
            } else {
                AnnotatedAst {
                    ast: Ast::Let(Let {
                        sequential,
                        proc_id,
                        inits,
                        body,
                    }),
                    location,
                    ty,
                }
                .traverse(ctx, compile_lambdas_ast)
            }
        }
        _ => AnnotatedAst { ast, location, ty }.traverse(ctx, compile_lambdas_ast),
    }
}

fn compile_asts(asts: Vec<AnnotatedAst>, ctx: &mut Context) -> Result<Instructions> {
    let mut result = Vec::new();
    for ast in asts {
        let mut insts = compile_ast(ast, ctx)?;
        result.append(&mut insts);
    }
    Ok(result)
}

pub fn compile(asts: Program, sym_table: SymbolTable) -> Result<Functions> {
    let mut result = Vec::new();

    let mut ctx = Context {
        env: Environment::new(),
        sym_table,
        func_env: Environment::new(),
        var_gen: UniqueGenerator::new(),
    };

    let asts = asts
        .into_iter()
        .map(|ast| compile_lambdas_ast(ast, &mut ctx))
        .collect::<Result<Vec<_>>>()?;

    let fun_vars = ctx.func_env.current_local().variables.clone();
    for (_, (_, mut fun)) in fun_vars {
        let res = get_last_instr(&fun.body);
        add_instr(
            &mut fun.body,
            &mut ctx,
            Instruction::Ret(Operand::Variable(res.result)),
            Type::None,
        );

        result.push(fun);
    }

    {
        let mut body = Vec::new();

        for ast in asts {
            let mut insts = compile_ast(ast, &mut ctx)?;
            body.append(&mut insts);
        }

        result.push(Function {
            name: "main".to_string(),
            args: Vec::new(),
            body,
            ty: Type::None,
        });
    }

    Ok(result)
}
