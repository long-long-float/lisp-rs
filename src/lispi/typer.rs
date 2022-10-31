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
    None,

    ForAll {
        tv: TypeVariable,
        ty: Box<Type>,
    },

    Scala(String),
    Composite {
        name: String,
        inner: Vec<Box<Type>>,
    },
    List(Box<Type>),
    Function {
        args: Vec<Box<Type>>,
        result: Box<Type>,
    },
    Any,

    Variable(TypeVariable),
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
        Type::List(Box::new(Type::Any))
    }

    pub fn function(args: Vec<Type>, result: Type) -> Type {
        Type::Function {
            args: args.iter().map(|a| Box::new(a.clone())).collect(),
            result: Box::new(result),
        }
    }

    pub fn for_all<F>(ty: F) -> Type
    where
        F: Fn(Type) -> Type,
    {
        Self::for_all_with_tv("X", ty)
    }

    pub fn for_all_with_tv<F>(tv: &str, ty: F) -> Type
    where
        F: Fn(Type) -> Type,
    {
        let tv = TypeVariable {
            name: tv.to_string(),
        };
        let ttv = Type::Variable(tv.clone());
        Type::ForAll {
            tv,
            ty: Box::new(ty(ttv)),
        }
    }

    fn has_free_var(&self, tv: &TypeVariable) -> bool {
        match self {
            Type::Numeric
            | Type::Int
            | Type::Float
            | Type::Boolean
            | Type::Char
            | Type::String
            | Type::Nil
            | Type::Any
            | Type::Scala(_)
            | Type::None => false,

            Type::List(e) => e.has_free_var(tv),

            Type::Composite { name: _, inner } => inner.iter().any(|i| i.has_free_var(tv)),
            Type::Function { args, result } => {
                args.iter().any(|arg| arg.has_free_var(tv)) | result.has_free_var(tv)
            }
            Type::Variable(ttv) => ttv == tv,
            Type::ForAll { tv: ttv, ty } => tv != ttv && ty.has_free_var(tv),
        }
    }

    fn replace(self, assign: &TypeAssignment) -> Self {
        match self {
            Type::Numeric
            | Type::Int
            | Type::Float
            | Type::Boolean
            | Type::Char
            | Type::String
            | Type::Nil
            | Type::Any
            | Type::Scala(_)
            | Type::None => self,

            Type::List(e) => Type::List(Box::new(e.replace(assign))),

            Type::Composite { name, inner } => {
                let inner = inner
                    .into_iter()
                    .map(|i| Box::new(i.replace(assign)))
                    .collect();
                Type::Composite { name, inner }
            }
            Type::Function { args, result } => {
                let args = args
                    .into_iter()
                    .map(|arg| Box::new(arg.replace(assign)))
                    .collect();
                let result = Box::new(result.replace(assign));
                Type::Function { args, result }
            }
            Type::Variable(ref tv) => {
                if tv == &assign.left {
                    assign.right.clone()
                } else {
                    self
                }
            }
            Type::ForAll { ref tv, ref ty } => {
                if tv != &assign.left {
                    Type::ForAll {
                        tv: tv.clone(),
                        ty: Box::new(ty.clone().replace(assign)),
                    }
                } else {
                    self
                }
            }
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
            Type::List(e) => write!(f, "list<{}>", e),
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
            Type::Variable(v) => write!(f, "{}", v.name),
            Type::ForAll { tv, ty } => write!(f, "∀{}. {}", tv.name, ty),

            Type::None => write!(f, "(none)"),
        }
    }
}

type TypeEnv = Environment<Type>;

#[derive(Clone, PartialEq, Debug)]
pub struct TypeVariable {
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
struct TypeAssignment {
    left: TypeVariable,
    right: Type,
}

impl TypeAssignment {
    fn new(left: TypeVariable, right: Type) -> Self {
        Self { left, right }
    }
}

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
        Type::Variable(TypeVariable {
            name: self.gen_string(),
        })
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
        // ctx.env.dump_local();
        Err(Error::UndefinedVariable(id.value.clone())
            .with_location(loc.clone())
            .into())
    }
}

/// Replace all outer universal quantification type variable with refresh type variable.
fn resolve_for_all(ty: Type, ctx: &mut Context) -> Type {
    if let Type::ForAll { tv, ty } = ty {
        let ty = resolve_for_all(*ty, ctx);
        ty.replace(&TypeAssignment::new(tv, ctx.tv_gen.gen_tv()))
    } else {
        ty
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
                    .map(|arg| Box::new(arg.ty.clone()))
                    .collect::<Vec<_>>();
                let result_type = ctx.tv_gen.gen_tv();

                let fun_ty = resolve_for_all(fun.ty.clone(), ctx);

                let mut ct = vec![TypeEquality::new(
                    fun_ty,
                    Type::Function {
                        args: arg_types.clone(),
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
            Ok((
                ast.with_new_ast_and_type(Ast::Quoted(Box::new(inner.clone())), inner.ty),
                c,
            ))
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
            ctx.env.insert_var(id.clone(), init.ty.clone());

            let def = Ast::Define(Define {
                id: id.clone(),
                init: Box::new(init),
            });
            Ok((ast.with_new_ast_and_type(def, Type::Nil), c))
        }
        Ast::Lambda(Lambda { args, body }) => {
            let arg_types = args
                .iter()
                .map(|_| Box::new(ctx.tv_gen.gen_tv()))
                .collect::<Vec<_>>();

            ctx.env.push_local();

            for (arg, ty) in args.iter().zip(arg_types.clone()) {
                ctx.env.insert_var(arg.clone(), *ty);
            }

            let (body, cbt) = collect_constraints_from_asts(body.clone(), ctx)?;

            ctx.env.pop_local();

            let result_type = if let Some(last) = body.last() {
                last.ty.clone()
            } else {
                Type::Nil
            };

            let fun = Ast::Lambda(Lambda {
                args: args.to_vec(),
                body,
            });
            let fun_ty = Type::Function {
                args: arg_types,
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

            vct.push(TypeEquality::new(var_ty, value.ty.clone()));

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
            ct.push(TypeEquality::new(cond.ty.clone(), Type::Boolean));

            let (if_expr, result_ty) = if let Some(else_ast) = else_ast {
                let (else_ast, mut ect) = collect_constraints_from_ast(*else_ast.clone(), ctx)?;

                ct.append(&mut ect);
                ct.push(TypeEquality::new(then_ast.ty.clone(), else_ast.ty.clone()));

                let result_ty = then_ast.ty.clone();

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
        Ast::Let(Let {
            sequential,
            proc_id,
            inits,
            body,
        }) => {
            let sequential = *sequential;
            let proc_id = proc_id.clone();

            let mut ict = Vec::new();
            let mut new_inits = Vec::new();
            let mut vars = Vec::new();

            ctx.env.push_local();

            for (k, v) in inits {
                let (v, mut vct) = collect_constraints_from_ast(v.clone(), ctx)?;
                new_inits.push((k.clone(), v.clone()));
                ict.append(&mut vct);
                if sequential {
                    ctx.env.insert_var(k.clone(), v.ty);
                } else {
                    vars.push((k, v.ty));
                }
            }

            if !sequential {
                for (k, t) in vars {
                    ctx.env.insert_var(k.clone(), t);
                }
            }

            let proc_result;
            if let Some(proc_id) = &proc_id {
                let proc_args = new_inits
                    .iter()
                    .map(|(_, ast)| ast.ty.clone())
                    .collect::<Vec<_>>();
                proc_result = ctx.tv_gen.gen_tv();
                let proc_ty = Type::function(proc_args, proc_result.clone());
                ctx.env.insert_var(proc_id.clone(), proc_ty);
            } else {
                proc_result = Type::None;
            }

            let (body, mut bct) = collect_constraints_from_asts(body.clone(), ctx)?;

            ctx.env.pop_local();

            let mut ct = ict;
            ct.append(&mut bct);

            let result_ty = body.last().map(|a| a.ty.clone()).unwrap_or(Type::Nil);

            if proc_result != Type::None {
                ct.push(TypeEquality::new(result_ty.clone(), proc_result));
            }

            Ok((
                ast.with_new_ast_and_type(
                    Ast::Let(Let {
                        sequential,
                        proc_id,
                        inits: new_inits,
                        body,
                    }),
                    result_ty,
                ),
                ct,
            ))
        }
        Ast::Begin(Begin { body }) => {
            let (body, bct) = collect_constraints_from_asts(body.clone(), ctx)?;
            let result_ty = body.last().map(|a| a.ty.clone()).unwrap_or(Type::Nil);

            Ok((
                ast.with_new_ast_and_type(Ast::Begin(Begin { body }), result_ty),
                bct,
            ))
        }
        Ast::BuildList(vs) => {
            let (vs, mut ct) = collect_constraints_from_asts(vs.clone(), ctx)?;

            let result_ty = if let Some((fst_arg, rest_args)) = vs.split_first() {
                for rest in rest_args {
                    ct.push(TypeEquality::new(fst_arg.ty.clone(), rest.ty.clone()));
                }
                Type::List(Box::new(fst_arg.ty.clone()))
            } else {
                Type::Nil
            };

            Ok((ast.with_new_ast_and_type(Ast::BuildList(vs), result_ty), ct))
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

fn replace_constraints(constraints: &[TypeEquality], assign: &TypeAssignment) -> Vec<TypeEquality> {
    constraints
        .iter()
        .map(|c| {
            let c = c.clone();
            TypeEquality::new(c.left.replace(assign), c.right.replace(assign))
        })
        .collect()
}

fn unify(constraints: Constraints) -> Result<Vec<TypeAssignment>> {
    if let Some((c, rest)) = constraints.split_first() {
        match (&c.left, &c.right) {
            (s, t) if s == t => unify(rest.to_vec()),
            (Type::Variable(x), t) | (t, Type::Variable(x)) if !t.has_free_var(&x) => {
                let assign = TypeAssignment::new(x.clone(), t.clone());
                let rest = replace_constraints(rest, &assign);
                let mut rest = unify(rest)?;
                let mut ct = vec![assign];
                ct.append(&mut rest);
                Ok(ct)
            }
            (Type::Any, _) | (_, Type::Any) => unify(rest.to_vec()),
            (Type::Numeric, Type::Int)
            | (Type::Int, Type::Numeric)
            | (Type::Numeric, Type::Float)
            | (Type::Float, Type::Numeric) => unify(rest.to_vec()),
            (Type::List(e0), Type::List(e1)) => {
                let mut rest = rest.to_vec();
                rest.push(TypeEquality::new(*e0.clone(), *e1.clone()));
                unify(rest)
            }
            (
                f0 @ Type::Function {
                    args: args0,
                    result: result0,
                },
                f1 @ Type::Function {
                    args: args1,
                    result: result1,
                },
            ) => {
                if args0.len() != args1.len() {
                    return Err(
                        Error::Type(format!("Types {} and {} are not matched.", f0, f1))
                            .with_null_location()
                            .into(),
                    );
                }

                let mut rest = rest.to_vec();
                for (a0, a1) in args0.iter().zip(args1) {
                    rest.push(TypeEquality::new(*a0.clone(), *a1.clone()));
                }
                rest.push(TypeEquality::new(*result0.clone(), *result1.clone()));

                unify(rest)
            }
            (t0, t1) => Err(
                Error::Type(format!("Types {} and {} are not matched.", t0, t1))
                    .with_null_location()
                    .into(),
            ),
        }
    } else {
        Ok(Vec::new())
    }
}

fn replace_ast(ast: AnnotatedAst, assign: &TypeAssignment) -> AnnotatedAst {
    let new_ty = ast.ty.clone().replace(assign);

    let iast = ast.ast.clone();

    match iast {
        Ast::List(vs) => {
            ast.with_new_ast_and_type(Ast::List(replace_asts(vs.to_vec(), assign)), new_ty)
        }
        Ast::Quoted(v) => {
            ast.with_new_ast_and_type(Ast::Quoted(Box::new(replace_ast(*v, assign))), new_ty)
        }

        Ast::Integer(_)
        | Ast::Float(_)
        | Ast::Boolean(_)
        | Ast::Char(_)
        | Ast::String(_)
        | Ast::Nil
        | Ast::Symbol(_)
        | Ast::SymbolWithType(_, _)
        | Ast::DefineMacro(_)
        | Ast::Continue(_) => ast.with_new_type(new_ty),

        Ast::Define(def) => ast.with_new_ast_and_type(
            Ast::Define(Define {
                init: Box::new(replace_ast(*def.init, assign)),
                ..def
            }),
            new_ty,
        ),
        Ast::Lambda(lambda) => ast.with_new_ast_and_type(
            Ast::Lambda(Lambda {
                body: replace_asts(lambda.body, assign),
                ..lambda
            }),
            new_ty,
        ),
        Ast::Assign(ast_assign) => ast.with_new_ast_and_type(
            Ast::Assign(Assign {
                value: Box::new(replace_ast(*ast_assign.value, assign)),
                ..ast_assign
            }),
            new_ty,
        ),
        Ast::IfExpr(if_expr) => {
            let cond = Box::new(replace_ast(*if_expr.cond, assign));
            let then_ast = Box::new(replace_ast(*if_expr.then_ast, assign));

            let if_expr = if let Some(else_ast) = if_expr.else_ast {
                let else_ast = Some(Box::new(replace_ast(*else_ast, assign)));
                IfExpr {
                    cond,
                    then_ast,
                    else_ast,
                }
            } else {
                IfExpr {
                    cond,
                    then_ast,
                    else_ast: None,
                }
            };
            ast.with_new_ast_and_type(Ast::IfExpr(if_expr), new_ty)
        }
        Ast::Let(Let {
            sequential,
            proc_id,
            inits,
            body,
        }) => {
            let inits = inits
                .into_iter()
                .map(|(k, v)| (k, replace_ast(v, assign)))
                .collect();
            let body = replace_asts(body, assign);

            ast.with_new_ast_and_type(
                Ast::Let(Let {
                    sequential,
                    proc_id,
                    inits,
                    body,
                }),
                new_ty,
            )
        }
        Ast::Begin(Begin { body }) => {
            let body = replace_asts(body, assign);
            ast.with_new_ast_and_type(Ast::Begin(Begin { body }), new_ty)
        }
        Ast::BuildList(vs) => {
            let vs = replace_asts(vs, assign);
            ast.with_new_ast_and_type(Ast::BuildList(vs), new_ty)
        }
    }
}

fn replace_asts(asts: Program, assign: &TypeAssignment) -> Program {
    asts.into_iter()
        .map(|ast| replace_ast(ast, assign))
        .collect()
}

pub fn check_and_inference_type(asts: Program, env: &Environment<Type>) -> Result<Program> {
    let mut ty_env = TypeEnv::new();
    for (id, ty) in &env.current_local().variables {
        ty_env.insert_var(
            SymbolValue {
                id: *id,
                value: "".to_string(),
            },
            ty.clone(),
        );
    }

    let mut ctx = Context {
        env: ty_env,
        tv_gen: TypeVarGenerator::new(),
    };
    let (asts, constraints) = collect_constraints_from_asts(asts, &mut ctx)?;
    // for c in &constraints {
    //     println!("{} = {}", c.left, c.right);
    // }

    let assigns = unify(constraints)?;
    let mut asts = asts;
    for assign in &assigns {
        // println!("{} = {}", assign.left.name, assign.right);

        asts = replace_asts(asts, &assign);
    }

    Ok(asts)
}
