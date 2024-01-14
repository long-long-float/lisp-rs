use std::{default, fmt::Display};

use anyhow::Result;
use itertools::Itertools;
use rustc_hash::FxHashMap;

use super::{
    ast::*, environment::*, error::*, parser::*, unique_generator::UniqueGenerator, SymbolValue,
    TokenLocation,
};

#[derive(Clone, PartialEq, Debug)]
pub enum Type {
    Int,
    Float,
    Boolean,
    Char,
    String,
    Symbol,
    Void,
    None,

    ConstantInt(i32),

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
    Array(Box<Type>),
    /// Element Type, Length Type (can be a number now not a type variable)
    FixedArray(Box<Type>, usize),
    Function {
        args: Vec<Box<Type>>,
        result: Box<Type>,
    },
    Struct {
        name: String,
    },
    Any,

    Reference(Box<Type>),

    Variable(TypeVariable),
}

impl Type {
    pub fn list() -> Type {
        Type::List(Box::new(Type::Any))
    }

    pub fn string() -> Type {
        Type::Array(Box::new(Type::Char))
    }

    pub fn array(ty: Type) -> Type {
        Type::Array(Box::new(ty))
    }

    pub fn reference(ty: Type) -> Type {
        Type::Reference(Box::new(ty))
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

    pub fn element_type(&self) -> Option<&Type> {
        match self {
            Type::List(et) | Type::Array(et) | Type::FixedArray(et, _) => Some(et),
            _ => None,
        }
    }

    pub fn dereference(&self) -> Option<&Type> {
        if let Type::Reference(ty) = self {
            Some(ty)
        } else {
            None
        }
    }

    pub fn fun_result_type(&self) -> Option<&Type> {
        match self {
            Type::Function { args: _, result } => Some(result),
            _ => None,
        }
    }

    fn has_free_var(&self, tv: &TypeVariable) -> bool {
        match self {
            Type::Int
            | Type::Float
            | Type::Boolean
            | Type::Char
            | Type::String
            | Type::Void
            | Type::Any
            | Type::Scala(_)
            | Type::Symbol
            | Type::Struct { .. }
            | Type::None
            | Type::ConstantInt(_) => false,

            Type::List(e) | Type::Array(e) | Type::FixedArray(e, _) => e.has_free_var(tv),

            Type::Composite { name: _, inner } => inner.iter().any(|i| i.has_free_var(tv)),
            Type::Function { args, result } => {
                args.iter().any(|arg| arg.has_free_var(tv)) || result.has_free_var(tv)
            }
            Type::Variable(ttv) => ttv == tv,
            Type::ForAll { tv: ttv, ty } => tv != ttv && ty.has_free_var(tv),
            Type::Reference(t) => t.has_free_var(tv),
        }
    }

    fn replace(self, assign: &TypeAssignment) -> Self {
        match self {
            Type::Int
            | Type::Float
            | Type::Boolean
            | Type::Char
            | Type::String
            | Type::Void
            | Type::Any
            | Type::Scala(_)
            | Type::Symbol
            | Type::Struct { .. }
            | Type::None
            | Type::ConstantInt(_) => self,

            Type::List(e) => Type::List(Box::new(e.replace(assign))),
            Type::Array(e) => Type::Array(Box::new(e.replace(assign))),
            Type::FixedArray(e, n) => Type::FixedArray(Box::new(e.replace(assign)), n),

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
            Type::Reference(t) => Type::Reference(Box::new(t.replace(assign))),
        }
    }

    pub fn with_location(self, loc: TokenLocation, expected: bool) -> TypeWithLocation {
        TypeWithLocation {
            ty: self,
            loc: vec![loc],
            expected,
        }
    }

    pub fn with_locations(self, loc: &[TokenLocation], expected: bool) -> TypeWithLocation {
        TypeWithLocation {
            ty: self,
            loc: loc.to_vec(),
            expected,
        }
    }

    pub fn with_null_location(self) -> TypeWithLocation {
        self.with_location(TokenLocation::Null, false)
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Type::Int => write!(f, "int"),
            Type::Float => write!(f, "float"),
            Type::Boolean => write!(f, "boolean"),
            Type::Char => write!(f, "char"),
            Type::String => write!(f, "string"),
            Type::Symbol => write!(f, "symbol"),
            Type::Void => write!(f, "void"),
            Type::ConstantInt(n) => write!(f, "{}", n),
            Type::Scala(name) => write!(f, "{}", name),
            Type::List(e) => write!(f, "list<{}>", e),
            Type::Array(e) => write!(f, "array<{}>", e),
            Type::FixedArray(e, n) => write!(f, "fixed-array<{}, {}>", e, n),
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
            Type::Struct { name } => {
                write!(f, "{}", name)
            }
            Type::Any => write!(f, "any"),
            Type::Variable(v) => write!(f, "{}", v.name),
            Type::ForAll { tv, ty } => write!(f, "∀{}. {}", tv.name, ty),

            Type::Reference(t) => write!(f, "&{}", t),

            Type::None => write!(f, "(none)"),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct TStructField {
    pub name: String,
    pub ty: Box<Type>,
}

impl TStructField {
    pub fn getter_name(&self, struct_name: &String) -> String {
        format!("{}->{}", struct_name, self.name)
    }

    pub fn setter_name(&self, struct_name: &String) -> String {
        format!("{}->{}=", struct_name, self.name)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct TypeWithLocation {
    pub ty: Type,
    /// If ty is scalar, loc has just one location.
    /// If ty is a function type, loc has locations of the application and its argument.
    pub loc: Vec<TokenLocation>,
    ///
    pub expected: bool,
}

impl TypeWithLocation {
    fn replace(self, assign: &TypeAssignment, ty_loc: &TypeWithLocation) -> Self {
        let TypeWithLocation {
            ty,
            mut loc,
            mut expected,
        } = self;
        if let Type::Variable(tv) = &ty {
            if ty_loc.loc[0] != TokenLocation::Null && tv == &assign.left {
                let TypeWithLocation {
                    loc: new_loc,
                    expected: new_expected,
                    ..
                } = ty_loc.clone();
                loc = new_loc;
                expected = new_expected;
            }
        }
        TypeWithLocation {
            ty: ty.replace(assign),
            loc,
            expected,
        }
    }
}

impl std::fmt::Display for TypeWithLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} ({})", self.ty, self.loc[0])
    }
}

type TypeEnv = Environment<Type>;

#[derive(Clone, PartialEq, Debug)]
pub struct TypeVariable {
    name: String,
}

#[derive(Clone, PartialEq, Debug)]
struct TypeEquality {
    left: TypeWithLocation,
    right: TypeWithLocation,
    relation: TypeEqualityRelation,
}

impl TypeEquality {
    fn new(left: TypeWithLocation, right: TypeWithLocation) -> Self {
        Self {
            left,
            right,
            relation: TypeEqualityRelation::default(),
        }
    }

    fn new_subtyping(left: TypeWithLocation, right: TypeWithLocation) -> Self {
        Self {
            left,
            right,
            relation: TypeEqualityRelation::Subtype,
        }
    }
}

impl Display for TypeEquality {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {}", self.left, self.relation, self.right)
    }
}

#[derive(Clone, PartialEq, Debug, Default)]
enum TypeEqualityRelation {
    #[default]
    /// left == right
    Equal,
    /// left <: right
    Subtype,
}

impl Display for TypeEqualityRelation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeEqualityRelation::Equal => write!(f, "="),
            TypeEqualityRelation::Subtype => write!(f, "<:"),
        }
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
pub struct StructDefinition {
    pub name: String,
    pub fields: Vec<TStructField>,
}

impl StructDefinition {
    fn size_and_offsets(&self, align: usize) -> (usize, Vec<usize>) {
        let mut cur = 0;
        let offsets = self
            .fields
            .iter()
            .map(|field| {
                if cur % align != 0 {
                    cur = (cur + (align - 1) / align) * align;
                }
                let offset = cur;
                cur += field.ty.size();
                offset
            })
            .collect_vec();
        (cur, offsets)
    }

    /// Calculate the offsets for each fields
    pub fn offsets(&self, align: usize) -> Vec<usize> {
        self.size_and_offsets(align).1
    }

    /// Return the size in bytes.
    pub fn size(&self, align: usize) -> usize {
        self.size_and_offsets(align).0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn struct_definition_size_and_offsets() {
        let struct_def = StructDefinition {
            name: "Struct".to_string(),
            fields: vec![
                TStructField {
                    name: "f1".to_string(),
                    ty: Box::new(Type::Char),
                },
                TStructField {
                    name: "f2".to_string(),
                    ty: Box::new(Type::Int),
                },
                TStructField {
                    name: "f3".to_string(),
                    ty: Box::new(Type::Char),
                },
            ],
        };

        let (size, offsets) = struct_def.size_and_offsets(4);
        assert_eq!(4 + 4 + 1, size);
        assert_eq!(vec![0, 4, 8], offsets);
    }
}

impl Display for StructDefinition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "struct {} {{", self.name)?;
        for field in &self.fields {
            writeln!(f, "  {}: {}", field.name, field.ty)?;
        }
        write!(f, "}}")
    }
}

pub type StructDefinitions = FxHashMap<String, StructDefinition>;

struct Context {
    /// Relations between variables and corresponding types.
    env: TypeEnv,
    /// Relations between type names and types.
    type_env: TypeEnv,
    struct_defs: StructDefinitions,
    tv_gen: UniqueGenerator,
}

impl Default for Context {
    fn default() -> Self {
        fn register_type(env: &mut Environment<Type>, name: &str, ty: Type) {
            env.insert_var(name.to_owned(), ty);
        }

        let mut type_env = TypeEnv::default();

        register_type(&mut type_env, "int", Type::Int);
        register_type(&mut type_env, "float", Type::Float);
        register_type(&mut type_env, "bool", Type::Boolean);
        register_type(&mut type_env, "char", Type::Char);
        register_type(&mut type_env, "string", Type::String);

        Self {
            env: TypeEnv::default(),
            type_env,
            struct_defs: FxHashMap::default(),
            tv_gen: UniqueGenerator::default(),
        }
    }
}

impl Context {
    fn gen_tv(&mut self) -> Type {
        Type::Variable(TypeVariable {
            name: format!("T{}", self.tv_gen.gen()),
        })
    }
}

fn find_var(id: &SymbolValue, loc: &TokenLocation, ctx: &mut Context) -> Result<Type> {
    if let Some(ty) = ctx.env.find_var(id) {
        Ok(ty)
    } else {
        // ctx.env.dump_local();
        Err(Error::UndefinedVariable(id.clone(), "typing")
            .with_location(*loc)
            .into())
    }
}

/// Replace all outer universal quantification type variable with refresh type variable.
fn resolve_for_all(ty: Type, ctx: &mut Context) -> Type {
    if let Type::ForAll { tv, ty } = ty {
        let ty = resolve_for_all(*ty, ctx);
        ty.replace(&TypeAssignment::new(tv, ctx.gen_tv()))
    } else {
        ty
    }
}

fn get_result_type_with_loc(body: &[AnnotatedAst]) -> TypeWithLocation {
    body.last()
        .map(|a| a.ty.clone().with_location(a.location, false))
        .unwrap_or(Type::Void.with_null_location())
}

fn collect_constraints_from_collection_literal<TC, AC>(
    ast: AnnotatedAst,
    vs: Vec<AnnotatedAst>,
    mut type_constuctor: TC,
    mut ast_constuctor: AC,
    ctx: &mut Context,
) -> Result<(AnnotatedAst, Constraints)>
where
    TC: FnMut(Box<Type>) -> Type,
    AC: FnMut(Vec<AnnotatedAst>) -> Ast,
{
    let (vs, mut ct) = collect_constraints_from_asts(vs, ctx)?;

    let result_ty = if let Some((fst_arg, rest_args)) = vs.split_first() {
        for rest in rest_args {
            ct.push(TypeEquality::new(
                fst_arg.ty.clone().with_location(fst_arg.location, false),
                rest.ty.clone().with_location(rest.location, false),
            ));
        }
        type_constuctor(Box::new(fst_arg.ty.clone()))
    } else {
        type_constuctor(Box::new(ctx.gen_tv()))
    };

    Ok((ast.with_new_ast_and_type(ast_constuctor(vs), result_ty), ct))
}

fn collect_constraints_from_ast(
    ast: AnnotatedAst,
    ctx: &mut Context,
) -> Result<(AnnotatedAst, Constraints)> {
    fn collect_constraints_from_let_inits(
        inits: &Vec<(SymbolValue, AnnotatedAst)>,
        sequential: bool,
        ctx: &mut Context,
    ) -> Result<(Vec<(SymbolValue, AnnotatedAst)>, Constraints)> {
        let mut ict = Vec::new();
        let mut new_inits = Vec::new();
        let mut vars = Vec::new();

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

        Ok((new_inits, ict))
    }

    fn collect_constraints_from_lambda(
        lambda: Lambda,
        ctx: &mut Context,
    ) -> Result<(Lambda, Type, Constraints)> {
        let Lambda {
            args,
            arg_types: orig_arg_types,
            body,
        } = lambda;

        let arg_types = orig_arg_types
            .iter()
            .map(|ty| {
                if let Some(ty) = ty {
                    Box::new(ty.clone())
                } else {
                    Box::new(ctx.gen_tv())
                }
            })
            .collect_vec();

        ctx.env.push_local();

        for (arg, ty) in args.iter().zip(arg_types.clone()) {
            ctx.env.insert_var(arg.clone(), *ty);
        }

        let (body, cbt) = collect_constraints_from_asts(body, ctx)?;

        ctx.env.pop_local();

        let result_type = if let Some(last) = body.last() {
            last.ty.clone()
        } else {
            Type::Void
        };

        let fun = Lambda {
            args: args.to_vec(),
            arg_types: orig_arg_types,
            body,
        };
        let fun_ty = Type::Function {
            args: arg_types,
            result: Box::new(result_type),
        };

        Ok((fun, fun_ty, cbt))
    }

    match &ast.ast {
        Ast::List(vs) => {
            if let Some((fun, args)) = vs.split_first() {
                let (fun, mut fct) = collect_constraints_from_ast(fun.clone(), ctx)?;
                let (mut args, mut act) = collect_constraints_from_asts(args.to_vec(), ctx)?;

                let arg_types = args
                    .iter()
                    .map(|arg| Box::new(arg.ty.clone()))
                    .collect::<Vec<_>>();
                let result_type = ctx.gen_tv();

                let fun_ty = resolve_for_all(fun.ty.clone(), ctx);

                let mut fun_ty_locs = vec![ast.location];
                let arg_locs = args.iter().map(|arg| arg.location).collect::<Vec<_>>();
                fun_ty_locs.append(&mut arg_locs.clone());

                let fun_arg_types_tv = args.iter().map(|_| Box::new(ctx.gen_tv())).collect_vec();
                let fun_result_type_tv = ctx.gen_tv();
                let fun_ty_tv = Type::Function {
                    args: fun_arg_types_tv.clone(),
                    result: Box::new(fun_result_type_tv.clone()),
                };

                let mut ct = vec![TypeEquality::new(
                    fun_ty.with_locations(&fun_ty_locs, true),
                    fun_ty_tv.with_locations(&fun_ty_locs, false),
                )];
                for ((farg, aarg), aloc) in fun_arg_types_tv.iter().zip(arg_types).zip(arg_locs) {
                    ct.push(TypeEquality::new_subtyping(
                        aarg.clone().with_locations(&fun_ty_locs, true),
                        farg.clone().with_location(aloc, false),
                    ));
                }
                ct.push(TypeEquality::new(
                    fun_result_type_tv.with_locations(&fun_ty_locs, true),
                    result_type.clone().with_locations(&fun_ty_locs, false),
                ));

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
            if let AnnotatedAst {
                ast: Ast::Symbol(_),
                ..
            } = *inner.clone()
            {
                Ok((ast.with_new_type(Type::Symbol), Vec::new()))
            } else {
                Err(
                    Error::Type("Quote is now supported for only symbols.".to_string())
                        .with_location(inner.location)
                        .into(),
                )
            }
        }
        Ast::Integer(_) => Ok((ast.with_new_type(Type::Int), Vec::new())),
        Ast::Float(_) => Ok((ast.with_new_type(Type::Float), Vec::new())),
        Ast::Boolean(_) => Ok((ast.with_new_type(Type::Boolean), Vec::new())),
        Ast::Char(_) => Ok((ast.with_new_type(Type::Char), Vec::new())),
        Ast::String(_) => {
            // Ok((ast.with_new_type(Type::String), Vec::new()))
            Ok((
                ast.with_new_type(Type::Array(Box::new(Type::Char))),
                Vec::new(),
            ))
        }
        Ast::Nil => Ok((ast.with_new_type(Type::Void), Vec::new())),
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
            Ok((ast.with_new_ast_and_type(def, Type::Void), c))
        }
        Ast::DefineFunction(DefineFunction {
            id,
            lambda,
            // Don't use lambda_type because it must be Type::None at first.
            lambda_type: _,
        }) => {
            let (lambda, lambda_type, c) = collect_constraints_from_lambda(lambda.clone(), ctx)?;
            ctx.env.insert_var(id.clone(), lambda_type.clone());

            let def = Ast::DefineFunction(DefineFunction {
                id: id.clone(),
                lambda,
                lambda_type,
            });
            Ok((ast.with_new_ast_and_type(def, Type::Void), c))
        }
        Ast::DefineStruct(DefineStruct { name, fields }) => {
            let fields = fields
                .iter()
                .map(|StructField { name, ty }| {
                    Ok(TStructField {
                        name: name.to_owned(),
                        ty: Box::new(ty.clone()),
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            let struct_type = Type::Struct {
                name: name.to_owned(),
            };
            ctx.type_env
                .insert_var(name.to_owned(), struct_type.clone());

            ctx.struct_defs.insert(
                name.to_owned(),
                StructDefinition {
                    name: name.to_owned(),
                    fields: fields.clone(),
                },
            );

            // Define constructor
            {
                let args_types = fields.iter().map(|f| *f.ty.clone()).collect_vec();
                let ctor_type = Type::function(args_types, struct_type.clone());
                ctx.env.insert_var(name.to_owned(), ctor_type);
            }

            // Define field accessors
            for field in fields {
                let getter_type = Type::function(
                    vec![Type::reference(struct_type.clone())],
                    *field.ty.clone(),
                );
                ctx.env.insert_var(field.getter_name(name), getter_type);

                let setter_type = Type::function(
                    vec![Type::reference(struct_type.clone()), *field.ty.clone()],
                    Type::Void,
                );
                ctx.env.insert_var(field.setter_name(name), setter_type);
            }

            Ok((ast, Vec::new()))
        }
        Ast::Lambda(Lambda {
            args,
            arg_types: orig_arg_types,
            body,
        }) => {
            let arg_types = orig_arg_types
                .iter()
                .map(|ty| {
                    if let Some(ty) = ty {
                        Box::new(ty.clone())
                    } else {
                        Box::new(ctx.gen_tv())
                    }
                })
                .collect_vec();

            ctx.env.push_local();

            for (arg, ty) in args.iter().zip(arg_types.clone()) {
                ctx.env.insert_var(arg.clone(), *ty);
            }

            let (body, cbt) = collect_constraints_from_asts(body.clone(), ctx)?;

            ctx.env.pop_local();

            let result_type = if let Some(last) = body.last() {
                last.ty.clone()
            } else {
                Type::Void
            };

            let fun = Ast::Lambda(Lambda {
                args: args.to_vec(),
                arg_types: orig_arg_types.clone(),
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

            vct.push(TypeEquality::new(
                var_ty.with_location(*var_loc, false),
                value.ty.clone().with_location(value.location, false),
            ));

            let assign = Ast::Assign(Assign {
                var: var.clone(),
                var_loc: *var_loc,
                value: Box::new(value),
            });

            Ok((ast.with_new_ast_and_type(assign, Type::Void), vct))
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
                cond.ty.clone().with_location(cond.location, false),
                Type::Boolean.with_null_location(),
            ));

            let (if_expr, result_ty) = if let Some(else_ast) = else_ast {
                let (else_ast, mut ect) = collect_constraints_from_ast(*else_ast.clone(), ctx)?;

                ct.append(&mut ect);
                ct.push(TypeEquality::new(
                    then_ast.ty.clone().with_location(then_ast.location, false),
                    else_ast.ty.clone().with_location(else_ast.location, false),
                ));

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
                    Type::Void,
                )
            };

            Ok((
                ast.with_new_ast_and_type(Ast::IfExpr(if_expr), result_ty),
                ct,
            ))
        }
        Ast::As(expr, str_ty) => {
            let (expr, ct) = collect_constraints_from_ast(*expr.clone(), ctx)?;
            let Some(ty) = ctx.type_env.find_var(str_ty) else {
                return Err(Error::UndefinedVariable(str_ty.to_owned(), "typing").into());
            };
            let str_ty = str_ty.to_owned();
            Ok((
                ast.with_new_ast_and_type(Ast::As(Box::new(expr), str_ty), ty),
                ct,
            ))
        }
        Ast::Cond(Cond { clauses }) => {
            let mut ct = Vec::new();
            let clauses = clauses
                .iter()
                .map(|CondClause { cond, body }| {
                    let (cond, mut cct) = collect_constraints_from_ast(*cond.clone(), ctx)?;
                    let (body, mut bct) = collect_constraints_from_asts(body.clone(), ctx)?;

                    ct.append(&mut cct);
                    ct.append(&mut bct);

                    Ok(CondClause {
                        cond: Box::new(cond),
                        body,
                    })
                })
                .collect::<Result<Vec<_>>>()?;

            let result_ty = if let Some((fst, rest)) = clauses.split_first() {
                let fst_cond_ty = fst.cond.ty.clone().with_location(fst.cond.location, false);
                let fst_body_ty = get_result_type_with_loc(&fst.body);
                ct.push(TypeEquality::new(
                    fst_cond_ty,
                    Type::Boolean.with_null_location(),
                ));

                for c in rest {
                    let cond_ty = c.cond.ty.clone().with_location(c.cond.location, false);
                    let body_ty = get_result_type_with_loc(&c.body);
                    ct.push(TypeEquality::new(
                        cond_ty,
                        Type::Boolean.with_null_location(),
                    ));
                    ct.push(TypeEquality::new(body_ty, fst_body_ty.clone()));
                }

                fst_body_ty.ty
            } else {
                Type::Void
            };

            Ok((
                ast.with_new_ast_and_type(Ast::Cond(Cond { clauses }), result_ty),
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

            ctx.env.push_local();

            let (new_inits, ict) = collect_constraints_from_let_inits(inits, sequential, ctx)?;

            let proc_result;
            if let Some(proc_id) = &proc_id {
                let proc_args = new_inits
                    .iter()
                    .map(|(_, ast)| ast.ty.clone())
                    .collect::<Vec<_>>();
                proc_result = ctx.gen_tv();
                let proc_ty = Type::function(proc_args, proc_result.clone());
                ctx.env.insert_var(proc_id.clone(), proc_ty);
            } else {
                proc_result = Type::None;
            }

            let (body, mut bct) = collect_constraints_from_asts(body.clone(), ctx)?;

            ctx.env.pop_local();

            let mut ct = ict;
            ct.append(&mut bct);

            let result_ty = body
                .last()
                .map(|a| a.ty.clone().with_location(a.location, false))
                .unwrap_or(Type::Void.with_location(ast.location, false));

            if proc_result != Type::None {
                ct.push(TypeEquality::new(
                    result_ty.clone(),
                    proc_result.with_null_location(),
                ));
            }

            Ok((
                ast.with_new_ast_and_type(
                    Ast::Let(Let {
                        sequential,
                        proc_id,
                        inits: new_inits,
                        body,
                    }),
                    result_ty.ty,
                ),
                ct,
            ))
        }
        Ast::Begin(Begin { body }) => {
            let (body, bct) = collect_constraints_from_asts(body.clone(), ctx)?;
            let result_ty = body.last().map(|a| a.ty.clone()).unwrap_or(Type::Void);

            Ok((
                ast.with_new_ast_and_type(Ast::Begin(Begin { body }), result_ty),
                bct,
            ))
        }
        Ast::Loop(Loop { inits, label, body }) => {
            let label = label.to_string();

            ctx.env.push_local();

            let (new_inits, ict) = collect_constraints_from_let_inits(inits, true, ctx)?;
            let (body, mut bct) = collect_constraints_from_asts(body.clone(), ctx)?;

            ctx.env.pop_local();

            let result_ty = body.last().map(|a| a.ty.clone()).unwrap_or(Type::Void);

            let mut ct = ict;
            ct.append(&mut bct);

            Ok((
                ast.with_new_ast_and_type(
                    Ast::Loop(Loop {
                        inits: new_inits,
                        label,
                        body,
                    }),
                    result_ty,
                ),
                ct,
            ))
        }
        Ast::ListLiteral(vs) => {
            let vs = vs.clone();
            collect_constraints_from_collection_literal(ast, vs, Type::List, Ast::ListLiteral, ctx)
        }
        Ast::ArrayLiteral(vs, is_fixed) => {
            let vs = vs.clone();
            let len = vs.len();
            let is_fixed = *is_fixed;
            collect_constraints_from_collection_literal(
                ast,
                vs,
                |et| {
                    if is_fixed {
                        Type::FixedArray(et, len)
                    } else {
                        Type::Array(et)
                    }
                },
                |vs| Ast::ArrayLiteral(vs, is_fixed),
                ctx,
            )
        }
        Ast::Ref(v) => {
            let (v, ct) = collect_constraints_from_ast(*v.clone(), ctx)?;
            let inner_type = v.ty.clone();
            Ok((
                ast.with_new_ast_and_type(
                    Ast::Ref(Box::new(v)),
                    Type::Reference(Box::new(inner_type)),
                ),
                ct,
            ))
        }
        Ast::Continue(_) | Ast::DefineMacro(_) | Ast::Include(_) => Ok((ast, Vec::new())),
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

fn replace_constraints(
    constraints: &[TypeEquality],
    assign: &TypeAssignment,
    loc: &TypeWithLocation,
) -> Vec<TypeEquality> {
    constraints
        .iter()
        .map(|c| {
            let TypeEquality {
                left,
                right,
                relation,
            } = c.clone();
            let left = left.replace(assign, loc);
            let right = right.replace(assign, loc);
            TypeEquality {
                left,
                right,
                relation,
            }
        })
        .collect()
}

/// Replace type variable x with type t in rest.
fn unify_type_var(
    x: &TypeVariable,
    t: &Type,
    loc: &TypeWithLocation,
    rest: &[TypeEquality],
) -> Result<Vec<TypeAssignment>> {
    let assign = TypeAssignment::new(x.clone(), t.clone());
    let rest = replace_constraints(rest, &assign, loc);
    let mut rest = unify(rest)?;
    let mut ct = vec![assign];
    ct.append(&mut rest);
    Ok(ct)
}

fn unify_equal_relation(c: &TypeEquality, rest: &[TypeEquality]) -> Result<Vec<TypeAssignment>> {
    match (&c.left.ty, &c.right.ty) {
        (s, t) if s == t => unify(rest.to_vec()),

        (Type::Variable(x), t) if !t.has_free_var(x) => unify_type_var(x, t, &c.right, rest),
        (t, Type::Variable(x)) if !t.has_free_var(x) => unify_type_var(x, t, &c.left, rest),

        (Type::Any, _) | (_, Type::Any) => unify(rest.to_vec()),

        (Type::List(e0), Type::List(e1))
        | (Type::Array(e0), Type::Array(e1))
        | (Type::Reference(e0), Type::Reference(e1)) => {
            let mut rest = rest.to_vec();
            rest.push(TypeEquality::new(
                e0.clone().with_locations(&c.left.loc, c.left.expected),
                e1.clone().with_locations(&c.right.loc, c.right.expected),
            ));
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
            let args0 = args0.iter().zip(c.left.loc.iter().skip(1));
            let args1 = args1.iter().zip(c.right.loc.iter().skip(1));
            for ((a0, l0), (a1, l1)) in args0.zip(args1) {
                rest.push(TypeEquality::new(
                    a0.clone().with_location(*l0, c.left.expected),
                    a1.clone().with_location(*l1, c.right.expected),
                ));
            }
            rest.push(TypeEquality::new(
                result0
                    .clone()
                    .with_location(c.left.loc[0], c.left.expected),
                result1
                    .clone()
                    .with_location(c.right.loc[0], c.right.expected),
            ));

            // println!("=============");
            // for c in rest.iter().take(5) {
            //     println!("{}", c);
            // }
            // println!("=============");

            unify(rest)
        }
        // left != right
        (left, right) => {
            let (loc0, loc1) = if c.left.loc == c.right.loc {
                (
                    if c.left.expected {
                        TokenLocation::Null
                    } else {
                        c.left.loc[0]
                    },
                    if c.right.expected {
                        TokenLocation::Null
                    } else {
                        c.right.loc[0]
                    },
                )
            } else {
                (c.left.loc[0], c.right.loc[0])
            };

            Err(
                Error::TypeNotMatched(left.clone(), right.clone(), loc0, loc1)
                    .with_null_location()
                    .into(),
            )
        }
    }
}

fn unify_subtype_relation(c: &TypeEquality, rest: &[TypeEquality]) -> Result<Vec<TypeAssignment>> {
    match (&c.left.ty, &c.right.ty) {
        // FIXME: SIGSEGV (Segmentation fault) occurs here in a test case `complex_program_stack`.
        (s, t) if s == t => unify(rest.to_vec()),

        (Type::Variable(x), t) if !t.has_free_var(x) => unify_type_var(x, t, &c.right, rest),
        (t, Type::Variable(x)) if !t.has_free_var(x) => unify_type_var(x, t, &c.left, rest),

        (Type::Any, _) | (_, Type::Any) => unify(rest.to_vec()),

        (Type::List(e0), Type::List(e1))
        | (Type::Array(e0), Type::Array(e1))
        | (Type::Reference(e0), Type::Reference(e1)) => {
            let mut rest = rest.to_vec();
            // Covariant
            rest.push(TypeEquality::new_subtyping(
                e0.clone().with_locations(&c.left.loc, c.left.expected),
                e1.clone().with_locations(&c.right.loc, c.right.expected),
            ));
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
            let args0 = args0.iter().zip(c.left.loc.iter().skip(1));
            let args1 = args1.iter().zip(c.right.loc.iter().skip(1));
            for ((a0, l0), (a1, l1)) in args0.zip(args1) {
                // Contravariant in argment types
                rest.push(TypeEquality::new_subtyping(
                    a1.clone().with_location(*l1, c.right.expected),
                    a0.clone().with_location(*l0, c.left.expected),
                ));
            }
            // Covariant in return type
            rest.push(TypeEquality::new_subtyping(
                result0
                    .clone()
                    .with_location(c.left.loc[0], c.left.expected),
                result1
                    .clone()
                    .with_location(c.right.loc[0], c.right.expected),
            ));

            unify(rest)
        }
        (left, right) => {
            let mut rest = rest.to_vec();

            // Check left <: right
            let is_subtyping = match (left, right) {
                (Type::FixedArray(lt, _), Type::Array(rt)) => {
                    rest.push(TypeEquality::new_subtyping(
                        lt.clone().with_location(c.left.loc[0], c.left.expected),
                        rt.clone().with_location(c.right.loc[0], c.right.expected),
                    ));

                    true
                }
                _ => false,
            };

            if is_subtyping {
                unify(rest)
            } else {
                let (loc0, loc1) = if c.left.loc == c.right.loc {
                    (
                        if c.left.expected {
                            TokenLocation::Null
                        } else {
                            c.left.loc[0]
                        },
                        if c.right.expected {
                            TokenLocation::Null
                        } else {
                            c.right.loc[0]
                        },
                    )
                } else {
                    (c.left.loc[0], c.right.loc[0])
                };

                Err(
                    Error::TypeNotMatched(left.clone(), right.clone(), loc0, loc1)
                        .with_null_location()
                        .into(),
                )
            }
        }
    }
}

fn unify(mut constraints: Constraints) -> Result<Vec<TypeAssignment>> {
    let first_equal_pos = constraints
        .iter()
        .find_position(|c| c.relation == TypeEqualityRelation::Equal)
        .map(|(pos, _)| pos);

    if let Some(pos) = first_equal_pos {
        let c = constraints.remove(pos);
        unify_equal_relation(&c, &constraints)
    } else if let Some((c, rest)) = constraints.split_first() {
        match &c.relation {
            TypeEqualityRelation::Equal => unify_equal_relation(c, rest),
            TypeEqualityRelation::Subtype => unify_subtype_relation(c, rest),
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
        | Ast::DefineStruct(_)
        | Ast::Include(_)
        | Ast::Continue(_) => ast.with_new_type(new_ty),

        Ast::Define(def) => ast.with_new_ast_and_type(
            Ast::Define(Define {
                init: Box::new(replace_ast(*def.init, assign)),
                ..def
            }),
            new_ty,
        ),
        Ast::DefineFunction(def) => ast.with_new_ast_and_type(
            Ast::DefineFunction(DefineFunction {
                lambda: Lambda {
                    body: replace_asts(def.lambda.body, assign),
                    ..def.lambda
                },
                lambda_type: def.lambda_type.replace(assign),
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
        Ast::Cond(Cond { clauses }) => {
            let clauses = clauses
                .into_iter()
                .map(|CondClause { cond, body }| CondClause {
                    cond: Box::new(replace_ast(*cond, assign)),
                    body: replace_asts(body, assign),
                })
                .collect();
            ast.with_new_ast_and_type(Ast::Cond(Cond { clauses }), new_ty)
        }
        Ast::As(expr, ty) => {
            ast.with_new_ast_and_type(Ast::As(Box::new(replace_ast(*expr, assign)), ty), new_ty)
        }
        Ast::Begin(Begin { body }) => {
            let body = replace_asts(body, assign);
            ast.with_new_ast_and_type(Ast::Begin(Begin { body }), new_ty)
        }
        Ast::Loop(Loop { inits, label, body }) => {
            let inits = inits
                .into_iter()
                .map(|(k, v)| (k, replace_ast(v, assign)))
                .collect();
            let body = replace_asts(body, assign);
            ast.with_new_ast_and_type(Ast::Loop(Loop { inits, label, body }), new_ty)
        }
        Ast::ListLiteral(vs) => {
            let vs = replace_asts(vs, assign);
            ast.with_new_ast_and_type(Ast::ListLiteral(vs), new_ty)
        }
        Ast::ArrayLiteral(vs, is_fixed) => {
            let vs = replace_asts(vs, assign);
            ast.with_new_ast_and_type(Ast::ArrayLiteral(vs, is_fixed), new_ty)
        }
        Ast::Ref(v) => {
            let v = replace_ast(*v, assign);
            ast.with_new_ast_and_type(Ast::Ref(Box::new(v)), new_ty)
        }
    }
}

fn replace_asts(asts: Program, assign: &TypeAssignment) -> Program {
    asts.into_iter()
        .map(|ast| replace_ast(ast, assign))
        .collect()
}

pub fn check_and_inference_type(
    asts: Program,
    env: &Environment<Type>,
    dump: bool,
) -> Result<(Program, StructDefinitions)> {
    let mut ctx = Context::default();

    for (id, ty) in &env.current_local().variables {
        ctx.env.insert_var(id.clone(), ty.clone());
    }

    let (asts, constraints) = collect_constraints_from_asts(asts, &mut ctx)?;

    if dump {
        for c in &constraints {
            println!("{}", c);
        }
        println!();
    }

    let assigns = unify(constraints)?;
    let mut asts = asts;
    for assign in &assigns {
        asts = replace_asts(asts, assign);
    }

    // Replace types for ctx.struct_defs
    let skeys = ctx.struct_defs.keys().map(|s| s.to_owned()).collect_vec();
    for name in skeys {
        let def = ctx.struct_defs.get_mut(&name).unwrap();
        for field in def.fields.iter_mut() {
            let mut new_ty = *field.ty.clone();
            for assign in &assigns {
                new_ty = new_ty.replace(assign);
            }
            field.ty = Box::new(new_ty);
        }
    }

    Ok((asts, ctx.struct_defs))
}
