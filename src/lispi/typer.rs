use anyhow::Result;

use super::{ast::*, environment::*, error::*, parser::*, SymbolValue, TokenLocation};

#[derive(Clone, PartialEq, Debug)]
pub enum Type {
    Numeric,
    Int,
    Float,
    Boolean,
    Char,
    String,
    Nil,

    Scala(String),
    Composite {
        name: String,
        inner: Vec<Box<Type>>,
    },
    Function {
        args: Vec<Box<Type>>,
        result: Box<Type>,
    },
    Any,

    Variable(String),
}

impl Type {
    fn scala(name: &str) -> Type {
        Type::Scala(name.to_string())
    }

    pub fn int() -> Type {
        Type::Int
    }

    pub fn symbol() -> Type {
        Type::scala("symbol")
    }

    pub fn list() -> Type {
        Type::Composite {
            name: "list".to_string(),
            inner: Vec::new(),
        }
    }

    pub fn function(args: Vec<Type>, result: Type) -> Type {
        Type::Function {
            args: args.iter().map(|a| Box::new(a.clone())).collect(),
            result: Box::new(result),
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Type::Numeric => write!(f, "numeric"),
            Type::Int => write!(f, "int"),
            Type::Float => write!(f, "float"),
            Type::Boolean => write!(f, "boolean"),
            Type::Char => write!(f, "char"),
            Type::String => write!(f, "string"),
            Type::Nil => write!(f, "nil"),
            Type::Scala(name) => write!(f, "{}", name),
            Type::Composite { name, inner } => {
                let inner = inner
                    .iter()
                    .map(|t| format!("{}", *t))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{}({})", name, inner)
            }
            Type::Function { args, result } => {
                let args = args
                    .iter()
                    .map(|t| format!("{}", *t))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({}) -> {}", args, *result)
            }
            Type::Any => write!(f, "any"),
            Type::Variable(v) => write!(f, "{}", v),
        }
    }
}

type TypeEnv = Environment<Type>;

#[derive(Clone, PartialEq, Debug)]
struct TypeVariable {
    name: String,
}

#[derive(Clone, PartialEq, Debug)]
struct TypeEquality {
    left: Type,
    right: Type,
}

impl TypeEquality {
    fn new(left: Type, right: Type) -> Self {
        Self { left, right }
    }
}

type Constraints = Vec<TypeEquality>;

#[derive(Clone, PartialEq, Debug)]
struct TypeVarGenerator(u32);

impl TypeVarGenerator {
    fn new() -> Self {
        Self(0)
    }

    fn gen_string(&mut self) -> String {
        let id = self.0;
        self.0 += 1;
        format!("T{}", id)
    }

    fn gen_tv(&mut self) -> Type {
        Type::Variable(self.gen_string())
    }
}

struct Context {
    env: TypeEnv,
    tv_gen: TypeVarGenerator,
}

fn find_var(id: &SymbolValue, loc: &TokenLocation, ctx: &mut Context) -> Result<Type> {
    if let Some(ty) = ctx.env.find_var(id) {
        Ok(ty)
    } else {
        Err(Error::UndefindVariable(id.value.clone())
            .with_location(loc.clone())
            .into())
    }
}

fn collect_constraints_from_ast(
    ast: AnnotatedAst,
    ctx: &mut Context,
) -> Result<(AnnotatedAst, Constraints)> {
    match &ast.ast {
        Ast::List(vs) => {
            if let Some((fun, args)) = vs.split_first() {
                let (fun, mut fct) = collect_constraints_from_ast(fun.clone(), ctx)?;
                let (mut args, mut act) = collect_constraints_from_asts(args.to_vec(), ctx)?;

                let arg_types = args
                    .iter()
                    .map(|arg| Box::new(arg.ty.as_ref().unwrap().clone()))
                    .collect();
                let result_type = ctx.tv_gen.gen_tv();

                let mut ct = vec![TypeEquality::new(
                    fun.ty.as_ref().unwrap().clone(),
                    Type::Function {
                        args: arg_types,
                        result: Box::new(result_type.clone()),
                    },
                )];
                ct.append(&mut fct);
                ct.append(&mut act);

                let mut vs = vec![fun];
                vs.append(&mut args);

                Ok((ast.with_new_ast_and_type(Ast::List(vs), result_type), ct))
            } else {
                Ok((ast.with_new_type(Type::list()), Vec::new()))
            }
        }
        Ast::Quoted(inner) => {
            let (inner, c) = collect_constraints_from_ast(*inner.clone(), ctx)?;
            Ok((ast.with_new_type(inner.ty.unwrap()), c))
        }
        Ast::Integer(_) => Ok((ast.with_new_type(Type::Int), Vec::new())),
        Ast::Float(_) => Ok((ast.with_new_type(Type::Float), Vec::new())),
        Ast::Boolean(_) => Ok((ast.with_new_type(Type::Boolean), Vec::new())),
        Ast::Char(_) => Ok((ast.with_new_type(Type::Char), Vec::new())),
        Ast::String(_) => Ok((ast.with_new_type(Type::String), Vec::new())),
        Ast::Nil => Ok((ast.with_new_type(Type::Nil), Vec::new())),
        Ast::Symbol(id) | Ast::SymbolWithType(id, _) => {
            let ty = find_var(id, &ast.location, ctx)?;
            Ok((ast.with_new_type(ty), Vec::new()))
        }
        // Ast::SymbolWithType(id, anot_ty) => {
        //     if let Some(ty) = ctx.env.find_var(&id) {
        //         ast.ty = Some(ty);
        //         Ok(vec![TypeAssignment::new()])
        //     }
        //     else {
        //     }
        // },
        Ast::Define(Define { id, init }) => {
            let (init, c) = collect_constraints_from_ast(*init.clone(), ctx)?;
            ctx.env
                .insert_var(id.clone(), init.ty.as_ref().unwrap().clone());

            let def = Ast::Define(Define {
                id: id.clone(),
                init: Box::new(init),
            });
            Ok((ast.with_new_ast_and_type(def, Type::Nil), c))
        }
        Ast::Lambda(Lambda { args, body }) => {
            let (body, cbt) = collect_constraints_from_asts(body.clone(), ctx)?;

            let result_type = if let Some(last) = body.last() {
                last.ty.as_ref().unwrap().clone()
            } else {
                Type::Nil
            };

            let fun = Ast::Lambda(Lambda {
                args: args.to_vec(),
                body,
            });
            let fun_ty = Type::Function {
                args: args.iter().map(|_| Box::new(ctx.tv_gen.gen_tv())).collect(),
                result: Box::new(result_type),
            };

            Ok((ast.with_new_ast_and_type(fun, fun_ty), cbt))
        }
        Ast::Assign(Assign {
            var,
            var_loc,
            value,
        }) => {
            let var_ty = find_var(var, var_loc, ctx)?;
            let (value, mut vct) = collect_constraints_from_ast(*value.clone(), ctx)?;

            vct.push(TypeEquality::new(
                var_ty,
                value.ty.as_ref().unwrap().clone(),
            ));

            let assign = Ast::Assign(Assign {
                var: var.clone(),
                var_loc: var_loc.clone(),
                value: Box::new(value),
            });

            Ok((ast.with_new_ast_and_type(assign, Type::Nil), vct))
        }
        Ast::IfExpr(IfExpr {
            cond,
            then_ast,
            else_ast,
        }) => {
            let (cond, mut cct) = collect_constraints_from_ast(*cond.clone(), ctx)?;
            let (then_ast, mut tct) = collect_constraints_from_ast(*then_ast.clone(), ctx)?;

            let mut ct = Vec::new();
            ct.append(&mut cct);
            ct.append(&mut tct);
            ct.push(TypeEquality::new(
                cond.ty.as_ref().unwrap().clone(),
                Type::Boolean,
            ));

            let (if_expr, result_ty) = if let Some(else_ast) = else_ast {
                let (else_ast, mut ect) = collect_constraints_from_ast(*else_ast.clone(), ctx)?;

                ct.append(&mut ect);
                ct.push(TypeEquality::new(
                    then_ast.ty.as_ref().unwrap().clone(),
                    else_ast.ty.as_ref().unwrap().clone(),
                ));

                let result_ty = then_ast.ty.as_ref().unwrap().clone();

                (
                    IfExpr {
                        cond: Box::new(cond),
                        then_ast: Box::new(then_ast),
                        else_ast: Some(Box::new(else_ast)),
                    },
                    result_ty,
                )
            } else {
                (
                    IfExpr {
                        cond: Box::new(cond),
                        then_ast: Box::new(then_ast),
                        else_ast: None,
                    },
                    Type::Nil,
                )
            };

            Ok((
                ast.with_new_ast_and_type(Ast::IfExpr(if_expr), result_ty),
                ct,
            ))
        }
        Ast::Continue(_) | Ast::DefineMacro(_) => Ok((ast, Vec::new())),
    }
}

fn collect_constraints_from_asts(
    asts: Vec<AnnotatedAst>,
    ctx: &mut Context,
) -> Result<(Vec<AnnotatedAst>, Constraints)> {
    let mut tv_asts = Vec::new();
    let mut constraints = Vec::new();
    for ast in asts {
        let (ast, mut subc) = collect_constraints_from_ast(ast, ctx)?;
        constraints.append(&mut subc);
        tv_asts.push(ast);
    }
    Ok((tv_asts, constraints))
}

pub fn check_and_inference_type(asts: Program, _env: Environment<()>) -> Result<Program> {
    let mut ctx = Context {
        env: TypeEnv::new(),
        tv_gen: TypeVarGenerator::new(),
    };
    let (ast, constraints) = collect_constraints_from_asts(asts, &mut ctx)?;
    for c in constraints {
        println!("{} = {}", c.left, c.right);
    }

    Ok(ast)
}
