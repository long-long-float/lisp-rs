use anyhow::{anyhow, Result};

use super::{
    ast::*, console::*, environment::*, error::*, parser::*, typer::*, SymbolValue, TokenLocation,
};

#[macro_export]
macro_rules! bug {
    () => {
        bug!("".to_string())
    };
    ( $msg:expr ) => {
        Error::Bug {
            message: $msg.to_string(),
            file: file!(),
            line: line!(),
        }
        .with_null_location()
        .into()
    };
}

#[macro_export]
macro_rules! unimplemented {
    () => {
        Error::Bug {
            message: "Unimplemented".to_string(),
            file: file!(),
            line: line!(),
        }
        .with_null_location()
        .into()
    };
}

/// This macro is for ease to get arguments with patterns.
macro_rules! match_call_args {
    ( $args:expr, $p:pat, $b:block, $index:expr ) => {
        if let Some($p) = $args.get($index) {
            $b
        }
        else {
            Err(bug!(format!("Cannot match {} with {:?}", stringify!($p), $args.get($index))))
        }
    };

    ( $args:expr, $p:pat, $( $ps:pat ),*, $b:block, $index:expr ) => {
        if let Some($p) = $args.get($index) {
            match_call_args!($args, $( $ps ),*, $b, ($index + 1))
        }
        else {
            Err(bug!(format!("Cannot match {} with {:?}", stringify!($p), $args.get($index))))
        }
    };

    ( $args:expr, $( $ps:pat ),+, $b:block ) => {
        match_call_args!($args, $( $ps ),+, $b, 0)
    };
}

pub type Env = Environment<Value>;

pub fn get_location(ast: Option<&AnnotatedAst>) -> TokenLocation {
    ast.map(|arg| arg.location).unwrap_or(TokenLocation::Null)
}

#[macro_export]
macro_rules! match_special_args {
    ( $args:expr, $p:pat, $b:block, $index:expr ) => {
        if let Some($p) = $args.get($index) {
            if $index != $args.len() - 1 {
                let loc = $crate::lispi::evaluator::get_location($args.get($index));
                Err(anyhow!(Error::Parse(format!("The length of argument is invalid")).with_location(loc)))
            }
            else {
                $b
            }
        }
        else {
            let loc = $crate::lispi::evaluator::get_location($args.last());
            Err(Error::Parse(format!("Cannot match {} with {:?}", stringify!($p), $args.get($index))).with_location(loc).into())
        }
    };

    ( $args:expr, $p:pat, $( $ps:pat ),+, $b:block, $index:expr ) => {
        if let Some($p) = $args.get($index) {
            match_special_args!($args, $( $ps ),*, $b, ($index + 1))
        }
        else {
            let loc = $crate::lispi::evaluator::get_location($args.last());
            Err(Error::Parse(format!("Cannot match {} with {:?}", stringify!($p), $args.get($index))).with_location(loc).into())
        }
    };

    ( $args:expr, $( $ps:pat ),+, $b:block ) => {
        match_special_args!($args, $( $ps ),+, $b, 0)
    };
}

#[macro_export]
macro_rules! match_special_args_with_rest {
    ( $args:expr, $rest:ident, $p:pat, $b:block, $index:expr ) => {
        if let (Some($p), (_, $rest)) = ($args.get($index), $args.split_at($index + 1)) {
            $b
        }
        else {
            let loc = $crate::lispi::evaluator::get_location($args.last());
            Err(Error::Parse(format!("Cannot match {} with {:?}", stringify!($p), $args.get($index))).with_location(loc).into())
        }
    };

    ( $args:expr, $rest:ident, $p:pat, $( $ps:pat ),+, $b:block, $index:expr ) => {
        if let Some($p) = $args.get($index) {
            match_special_args_with_rest!($args, $rest, $( $ps ),*, $b, ($index + 1))
        }
        else {
            let loc = $crate::lispi::evaluator::get_location($args.last());
            Err(Error::Parse(format!("Cannot match {} with {:?}", stringify!($p), $args.get($index))).with_location(loc).into())
        }
    };

    ( $args:expr, $rest:ident, $( $ps:pat ),+, $b:block ) => {
        match_special_args_with_rest!($args, $rest, $( $ps ),+, $b, 0)
    };
}

#[macro_export]
macro_rules! ast_pat {
    ( $p:pat ) => {
        AnnotatedAst {
            ast: $p,
            location: _,
            ty: _,
        }
    };

    ( $p:pat, $loc:pat ) => {
        AnnotatedAst {
            ast: $p,
            location: $loc,
            ty: _,
        }
    };
}

pub type EvalResult = Result<Value>;

#[derive(Clone, Debug)]
pub enum Value {
    Integer(i32),
    Float(f32),
    Boolean(bool),
    Char(char),
    String(String),
    Symbol(SymbolValue),
    List(Vec<Value>),
    Function {
        name: SymbolValue,
        args: Vec<SymbolValue>,
        body: Vec<AnnotatedAst>,
        is_macro: bool,
        parent_local: LocalRef<Value>,
    },
    NativeFunction {
        name: SymbolValue,
        func: fn(Vec<Value>) -> EvalResult,
    },

    /// For macro expansion
    RawAst(AnnotatedAst),

    /// For optimizing tail recursion
    Continue(Continue),
}

impl Value {
    pub fn nil() -> Value {
        Value::List(Vec::new())
    }

    fn is_true(&self) -> bool {
        !matches!(self, Value::Boolean(false))
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Value::Integer(v) => write!(f, "{}", v),
            Value::Float(v) => write!(f, "{}", v),
            Value::Symbol(v) => write!(f, "{}", v),
            Value::Boolean(v) => write!(f, "{}", v),
            Value::Char(v) => write!(f, "{}", v),
            Value::String(v) => write!(f, "{}", v),
            Value::List(vs) => {
                if vs.is_empty() {
                    write!(f, "Nil")
                } else {
                    write!(f, "(")?;
                    for (i, v) in vs.iter().enumerate() {
                        write!(f, "{}", v)?;
                        if i < vs.len() - 1 {
                            write!(f, " ")?;
                        }
                    }
                    write!(f, ")")?;
                    Ok(())
                }
            }
            Value::Function {
                name,
                is_macro,
                body,
                ..
            } => {
                if *is_macro {
                    write!(f, "MACRO {}", name)
                } else {
                    writeln!(f, "FUNCTION {}", name)?;
                    for ast in body {
                        writeln!(f, "  {}", ast)?;
                    }
                    Ok(())
                }
            }
            Value::NativeFunction { name, func: _ } => {
                write!(f, "FUNCTION {}", name)
            }
            Value::RawAst(ast) => write!(f, "AST {:?}", ast),
            Value::Continue(name) => write!(f, "CONINUE {:?}", name),
        }
    }
}

impl From<&Ast> for Value {
    fn from(ast: &Ast) -> Self {
        match ast {
            Ast::Integer(v) => Value::Integer(*v),
            Ast::Float(v) => Value::Float(*v),
            Ast::Boolean(v) => Value::Boolean(*v),
            Ast::Char(v) => Value::Char(*v),
            Ast::String(v) => Value::String(v.clone()),
            Ast::Symbol(v) => Value::Symbol(v.clone()),
            Ast::SymbolWithType(v, _) => Value::Symbol(v.clone()),
            Ast::Quoted(v) => Value::from(&v.ast),
            Ast::List(vs) => {
                let vs = vs.iter().map(|v| Value::from(&v.ast)).collect();
                Value::List(vs)
            }

            Ast::Nil => Value::nil(),
            // These must be converted in eval_ast.
            Ast::Lambda(_)
            | Ast::Include(_)
            | Ast::DefineMacro(_)
            | Ast::Define(_)
            | Ast::DefineStruct(_)
            | Ast::Assign(_)
            | Ast::IfExpr(_)
            | Ast::Let(_)
            | Ast::Begin(_)
            | Ast::Loop(_)
            | Ast::ListLiteral(_)
            | Ast::ArrayLiteral(_)
            | Ast::As(_, _)
            | Ast::Cond(_) => Value::nil(),

            Ast::Continue(v) => Value::Continue(v.clone()),
        }
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Value::Boolean(value)
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (&Value::Integer(x), &Value::Integer(y)) => x == y,
            (&Value::Float(x), &Value::Float(y)) => x == y,
            (&Value::Boolean(x), &Value::Boolean(y)) => x == y,
            (&Value::Char(x), &Value::Char(y)) => x == y,
            (Value::String(x), Value::String(y)) => x == y,
            (Value::Symbol(x), Value::Symbol(y)) => x == y,
            (Value::List(x), Value::List(y)) => x == y,
            (Value::Function { name: x, .. }, Value::Function { name: y, .. }) => x == y,
            (Value::NativeFunction { name: x, .. }, Value::NativeFunction { name: y, .. }) => {
                x == y
            }
            // These values cannot compare.
            (Value::RawAst(_), Value::RawAst(_)) => false,
            (Value::Continue(_), Value::Continue(_)) => false,
            _ => false,
        }
    }
}

pub fn eval_asts(asts: &[AnnotatedAst], env: &mut Env) -> Result<Vec<Value>> {
    asts.iter()
        .map(|arg| eval_ast(arg, env))
        .collect::<Result<Vec<_>>>()
}

pub fn get_last_result(results: Vec<Value>) -> Value {
    results.into_iter().last().unwrap_or(Value::nil())
}

pub fn get_symbol_values(symbols: &[AnnotatedAst]) -> Result<Vec<SymbolValue>> {
    symbols
        .iter()
        .map(|symbol| {
            if let Some(v) = symbol.ast.get_symbol_value() {
                Ok(v.clone())
            } else {
                Err(Error::Eval(format!("{:?} is not an symbol", symbol.ast))
                    .with_location(symbol.location)
                    .into())
            }
        })
        .collect()
}

/// Evaluate special forms. The difference from eval_function is whether arguments are evaluated.
/// Arguments of special froms are not evaluated before processing arguments.
///
/// This is useful for `if` for example.
/// In the second arm `(print "Never evaluated")` is not expected to be evaluated.
///
/// ```lisp
/// (if #t (print "Hi") (print "Never evaluated"))
/// ```
fn eval_special_form(
    name_ast: &AnnotatedAst,
    raw_args: &[AnnotatedAst],
    env: &mut Env,
) -> EvalResult {
    if let Ast::Symbol(name) = &name_ast.ast {
        let name = name.as_str();
        match name {
            "function" => {
                if let Some(func) = raw_args.first() {
                    let result = eval_ast(func, env)?;
                    if let Value::Symbol(name) = result {
                        Ok(eval_ast(&Ast::Symbol(name).with_null_location(), env)?)
                    } else {
                        Ok(result)
                    }
                } else {
                    Err(
                        Error::Eval("'function' is formed as (function name)".to_string())
                            .with_location(name_ast.location)
                            .into(),
                    )
                }
            }
            _ => {
                let mac = eval_ast(name_ast, env)?;
                if let Value::Function {
                    args,
                    body,
                    is_macro: true,
                    ..
                } = mac
                {
                    env.push_local();

                    for (name, value) in args.iter().zip(raw_args) {
                        env.insert_var(name.clone(), Value::RawAst(value.clone()));
                    }

                    let result = eval_asts(&body, env);

                    env.pop_local();

                    let result = get_last_result(result?);
                    eval_ast(&Ast::from_value(result)?.with_null_location(), env)
                } else {
                    Err(Error::DoNothing.with_null_location().into())
                }
            }
        }
    } else {
        Err(Error::DoNothing.with_null_location().into())
    }
}

fn eval_function(name: &AnnotatedAst, args: &[AnnotatedAst], env: &mut Env) -> EvalResult {
    let name_loc = &name.location;
    let name = eval_ast(name, env)?;
    let arg_locs = args.iter().map(|arg| arg.location).collect::<Vec<_>>();
    let args = eval_asts(args, env)?;

    apply_function(&name, *name_loc, &args, &arg_locs, env)
}

/// Apply a function to args under env.
/// It's formed as `(func args...)`.
fn apply_function(
    func: &Value,
    func_loc: TokenLocation,
    args: &[Value],
    arg_locs: &[TokenLocation],
    env: &mut Env,
) -> EvalResult {
    match &func {
        // Embedded functions
        Value::Symbol(func_name) => {
            let func_name = func_name.as_str();

            match func_name {
                // Functions
                "+" | "-" | "*" | "/" | ">" | ">=" | "<" | "<=" => {
                    // Arithmetic function accepts both integer and float values.
                    // If a float value exists in arguments, all arguments are treated as float values.
                    // Otherwise, there are calcurated as integer.
                    enum Number {
                        Int(i32),
                        Float(f32),
                    }

                    let mut has_float_arg = false;
                    let args = args
                        .iter()
                        .zip(arg_locs)
                        .map(|(arg, loc)| match *arg {
                            Value::Integer(v) => Ok(Number::Int(v)),
                            Value::Float(v) => {
                                has_float_arg = true;
                                Ok(Number::Float(v))
                            }
                            _ => Err(Error::Eval(format!("`{}` is not an integer.", arg))
                                .with_location(*loc)
                                .into()),
                        })
                        .collect::<Result<Vec<Number>>>()?;

                    // To prevent duplicate definitions for integer and float, a macro `calc` is defined.
                    macro_rules! calc {
                        ( $args:expr, $elem_type:ty ) => {
                            match func_name {
                                "+" => $args.fold(0.0 as $elem_type, |sum, v| sum + v),
                                "*" => $args.fold(1.0 as $elem_type, |acc, v| acc * v),
                                "-" | "/" => {
                                    let sub = func_name == "-";
                                    if args.len() >= 2 {
                                        $args
                                            .reduce(|acc, v| if sub { acc - v } else { acc / v })
                                            .unwrap()
                                    } else if args.len() == 1 {
                                        let value = $args.nth(0).unwrap();
                                        if sub {
                                            0.0 as $elem_type - value
                                        } else {
                                            1.0 as $elem_type / value
                                        }
                                    } else {
                                        return Err(Error::Eval(format!(
                                            "Function {} needs least one value",
                                            func_name
                                        ))
                                        .with_location(func_loc)
                                        .into());
                                    }
                                }
                                ">" | ">=" | "<" | "<=" => {
                                    let args = $args.collect::<Vec<_>>();
                                    let x = args.get(0);
                                    let y = args.get(1);
                                    let res = match func_name {
                                        ">" => x > y,
                                        ">=" => x >= y,
                                        "<" => x < y,
                                        "<=" => x <= y,
                                        _ => return Err(bug!()),
                                    };
                                    return Ok(Value::from(res));
                                }
                                _ => {
                                    return Err(Error::Eval(format!(
                                        "Unknown function: {}",
                                        func_name
                                    ))
                                    .with_location(func_loc)
                                    .into())
                                }
                            }
                        };
                    }

                    if has_float_arg {
                        let mut args = args.iter().map(|arg| match *arg {
                            Number::Int(v) => v as f32,
                            Number::Float(v) => v,
                        });
                        Ok(Value::Float(calc!(args, f32)))
                    } else {
                        let mut args = args.iter().map(|arg| match *arg {
                            Number::Int(v) => v,
                            Number::Float(v) => v as i32,
                        });
                        Ok(Value::Integer(calc!(args, i32)))
                    }
                }
                "or" => Ok(Value::Boolean(args.iter().any(|arg| arg.is_true()))),
                "and" => Ok(Value::Boolean(args.iter().all(|arg| arg.is_true()))),
                "print" => {
                    for arg in args {
                        printlnuw(&arg);
                    }
                    Ok(Value::nil())
                }
                "display" => {
                    for arg in args {
                        printuw(arg);
                    }
                    Ok(Value::nil())
                }
                "map" => {
                    let err =
                        Error::Eval("'map' is formed as (mapcar function list ...)".to_string())
                            .with_location(func_loc);

                    if let Some((func, lists)) = args.split_first() {
                        let lists = lists
                            .iter()
                            .map(|list| {
                                if let Value::List(elements) = &list {
                                    Ok(elements)
                                } else {
                                    Err(anyhow!(err.clone()))
                                }
                            })
                            .collect::<Result<Vec<_>>>()?;

                        if lists.is_empty() {
                            return Err(anyhow!(err.clone()));
                        }

                        let mut result = Vec::new();
                        let list0_len = lists.get(0).unwrap().len();
                        for idx in 0..list0_len {
                            let mut args = Vec::new();
                            for list in &lists {
                                args.push(list.get(idx).cloned().unwrap_or(Value::nil()));
                            }
                            let arg_locs = [TokenLocation::Null].repeat(lists.len());

                            result.push(apply_function(
                                func,
                                TokenLocation::Null,
                                &args,
                                &arg_locs,
                                env,
                            )?);
                        }

                        Ok(Value::List(result))
                    } else {
                        Err(anyhow!(err))
                    }
                }
                _ => Err(Error::Eval(format!("Unknown function: {}", func_name))
                    .with_location(func_loc)
                    .into()),
            }
        }
        // Function defined in lisp
        Value::Function {
            args: arg_names,
            body,
            is_macro: false,
            parent_local,
            ..
        } => {
            env.push_local();

            for (name, value) in arg_names.iter().zip(args) {
                env.insert_var(name.clone(), value.clone());
            }

            // TODO: Support nested lambda calling.
            if parent_local.is_some() {
                env.lambda_local = parent_local.clone();
            }

            let result = eval_asts(body, env);

            env.lambda_local = None;

            env.pop_local();

            Ok(get_last_result(result?))
        }
        // Function defined in Rust (`init_env`).
        Value::NativeFunction { name: _, func } => func(args.to_vec()),
        _ => Err(Error::Eval(format!("{} is not a function", func))
            .with_location(func_loc)
            .into()),
    }
}

/// Evaluate a single AST such as lists and symbols.
/// Other values (ATOM) are evaluated at `Value::from`.
fn eval_ast(ast: &AnnotatedAst, env: &mut Env) -> EvalResult {
    match &ast.ast {
        Ast::DefineMacro(DefineMacro { id, args, body }) => {
            let func = Value::Function {
                name: id.clone(),
                args: args.clone(),
                body: body.to_vec(),
                is_macro: true,
                parent_local: None,
            };
            env.insert_var(id.clone(), func);

            Ok(Value::nil())
        }
        Ast::Define(Define { id, init }) => {
            let value = eval_ast(init, env)?;
            env.insert_var(id.clone(), value);
            Ok(Value::nil())
        }
        Ast::Lambda(Lambda {
            args,
            arg_types: _,
            body,
        }) => {
            let func = Value::Function {
                name: SymbolValue::new(),
                args: args.to_vec(),
                body: body.to_vec(),
                is_macro: false,
                parent_local: env.head_local.clone(),
            };
            Ok(func)
        }
        Ast::Assign(Assign {
            var,
            var_loc: _loc,
            value,
        }) => {
            let value = eval_ast(value, env)?;
            if env.update_var(var.clone(), &value).is_ok() {
                return Ok(Value::nil());
            }

            if let Some(local) = env.lambda_local.clone() {
                if local.borrow_mut().update_var(var.to_owned(), &value) {
                    return Ok(Value::nil());
                }
            }

            // .or_else(|err| Err(anyhow!(err.with_location(name_ast.location))))?;
            Ok(Value::nil())
        }
        Ast::IfExpr(IfExpr {
            cond,
            then_ast,
            else_ast,
        }) => {
            let cond = eval_ast(cond, env)?.is_true();
            if cond {
                eval_ast(then_ast, env)
            } else if let Some(else_ast) = else_ast {
                eval_ast(else_ast, env)
            } else {
                Ok(Value::nil())
            }
        }
        Ast::Let(Let {
            sequential,
            proc_id,
            inits,
            body,
        }) => {
            let sequential = *sequential;

            if let Some(proc_id) = proc_id {
                // named let

                let mut arg_exprs = Vec::new();
                for (id, expr) in inits {
                    arg_exprs.push((id.clone(), expr.clone()));
                }
                let (args, exprs): (Vec<SymbolValue>, Vec<_>) = arg_exprs.into_iter().unzip();

                let func = Value::Function {
                    name: proc_id.clone(),
                    args,
                    body: body.to_vec(),
                    is_macro: false,
                    parent_local: None,
                };

                env.push_local();
                env.insert_var(proc_id.clone(), func);

                let mut call_args = vec![Ast::Symbol(proc_id.clone()).with_null_location()];
                let mut exprs = exprs;
                call_args.append(&mut exprs);

                let result = eval_asts(&[Ast::List(call_args).with_null_location()], env);

                env.pop_local();

                Ok(get_last_result(result?))
            } else {
                env.push_local();

                let mut exprs = Vec::new();

                for (id, expr) in inits {
                    let expr = eval_ast(expr, env)?;
                    if sequential {
                        env.insert_var(id.clone(), expr);
                    } else {
                        exprs.push((id, expr));
                    }
                }

                if !sequential {
                    for (id, expr) in exprs {
                        env.insert_var(id.clone(), expr);
                    }
                }

                let result = eval_asts(body, env);

                env.pop_local();

                Ok(get_last_result(result?))
            }
        }
        Ast::Begin(Begin { body }) => Ok(get_last_result(eval_asts(body, env)?)),
        Ast::Loop(Loop { inits, label, body }) => {
            env.push_local();

            // Sequencial initialization
            for (id, expr) in inits {
                let expr = eval_ast(expr, env)?;
                env.insert_var(id.clone(), expr);
            }

            let result = loop {
                let results = eval_asts(body, env);
                let result = get_last_result(results?);
                if let Value::Continue(Continue { label: id, updates }) = &result {
                    if id == label {
                        // continue
                        eval_asts(updates, env)?;
                    } else {
                        break result;
                    }
                } else {
                    break result;
                }
            };

            env.pop_local();

            Ok(result)
        }
        Ast::ListLiteral(vs) => Ok(Value::List(eval_asts(vs, env)?)),
        Ast::Cond(Cond { clauses }) => {
            for CondClause { cond, body } in clauses {
                let cond = eval_ast(cond, env)?;
                if cond.is_true() {
                    return Ok(get_last_result(eval_asts(body, env)?));
                }
            }

            Ok(Value::nil())
        }
        Ast::List(elements) => {
            if let Some((first, rest)) = elements.split_first() {
                let result = eval_special_form(first, rest, env);
                if let Err(err) = result {
                    if let Some(ErrorWithLocation {
                        err: Error::DoNothing,
                        location: _,
                    }) = err.downcast_ref::<ErrorWithLocation>()
                    {
                        eval_function(first, rest, env)
                    } else {
                        Err(anyhow!(err))
                    }
                } else {
                    result
                }
            } else {
                Ok(Value::nil())
            }
        }
        Ast::Symbol(value) => {
            if let Some(var) = env.find_var(value) {
                return Ok(var);
            }

            if let Some(local) = env.lambda_local.clone() {
                if let Some(var) = local.borrow_mut().find_var(value.to_owned()) {
                    return Ok(var);
                }
            }

            Err(Error::UndefinedVariable(value.clone(), "evaluation")
                .with_location(ast.location)
                .into())
        }
        _ => Ok(Value::from(&ast.ast)),
    }
}

/// Define embedded functions to insert to the root of environment.
pub fn init_env(env: &mut Env, ty_env: &mut Environment<Type>) {
    let s = |value: &str| value.to_owned();

    fn insert_function(
        env: &mut Env,
        ty_env: &mut Environment<Type>,
        name: SymbolValue,
        ty: Type,
        func: fn(Vec<Value>) -> EvalResult,
    ) {
        env.insert_var(
            name.clone(),
            Value::NativeFunction {
                name: name.clone(),
                func,
            },
        );
        ty_env.insert_var(name, ty);
    }

    fn insert_variable_as_symbol_and_type(
        env: &mut Env,
        ty_env: &mut Environment<Type>,
        name: SymbolValue,
        ty: Type,
    ) {
        env.insert_var(name.clone(), Value::Symbol(name.clone()));
        ty_env.insert_var(name, ty);
    }

    // Pre-defined functions and special forms
    insert_function(
        env,
        ty_env,
        s("even?"),
        Type::function(vec![Type::int()], Type::Boolean),
        |args| match_call_args!(args, Value::Integer(v), { Ok(Value::from(v % 2 == 0)) }),
    );
    insert_function(
        env,
        ty_env,
        s("not"),
        Type::function(vec![Type::Boolean], Type::Boolean),
        |args| match_call_args!(args, Value::Boolean(v), { Ok(Value::from(!v)) }),
    );
    insert_function(
        env,
        ty_env,
        s("="),
        Type::function(vec![Type::Any, Type::Any], Type::Boolean),
        |args| match_call_args!(args, v1, v2, { Ok(Value::from(v1 == v2)) }),
    );
    insert_function(
        env,
        ty_env,
        s("car"),
        Type::for_all(|tv| Type::function(vec![Type::List(Box::new(tv.clone()))], tv)),
        |args| {
            match_call_args!(args, Value::List(vs), {
                let first = vs.first().map(|v| (*v).clone());
                Ok(first.unwrap_or(Value::nil()))
            })
        },
    );
    insert_function(
        env,
        ty_env,
        s("cdr"),
        Type::for_all(|tv| {
            Type::function(
                vec![Type::List(Box::new(tv.clone()))],
                Type::List(Box::new(tv)),
            )
        }),
        |args| {
            match_call_args!(args, Value::List(vs), {
                if let Some((_, rest)) = vs.split_first() {
                    if rest.is_empty() {
                        Ok(Value::nil())
                    } else {
                        Ok(Value::List(rest.to_vec()))
                    }
                } else {
                    Ok(Value::nil())
                }
            })
        },
    );
    insert_function(
        env,
        ty_env,
        s("<<"),
        Type::function(vec![Type::int(), Type::int()], Type::int()),
        |args| {
            match_call_args!(args, Value::Integer(left), Value::Integer(right), {
                Ok(Value::Integer(left << right))
            })
        },
    );
    insert_function(
        env,
        ty_env,
        s(">>"),
        Type::function(vec![Type::int(), Type::int()], Type::int()),
        |args| {
            match_call_args!(args, Value::Integer(left), Value::Integer(right), {
                Ok(Value::Integer(left >> right))
            })
        },
    );
    // TODO: Make mod to accept number
    insert_function(
        env,
        ty_env,
        s("mod"),
        Type::function(vec![Type::int(), Type::int()], Type::int()),
        |args| {
            match_call_args!(args, Value::Integer(num), Value::Integer(divisor), {
                Ok(Value::Integer(num % divisor))
            })
        },
    );
    insert_function(
        env,
        ty_env,
        s("cons"),
        Type::for_all(|tv| {
            Type::function(
                vec![tv.clone(), Type::List(Box::new(tv.clone()))],
                Type::List(Box::new(tv)),
            )
        }),
        |args| {
            match_call_args!(args, v, Value::List(vs), {
                let mut vs = vs.clone();
                vs.insert(0, v.clone());
                Ok(Value::List(vs))
            })
        },
    );
    insert_function(
        env,
        ty_env,
        s("length"),
        Type::for_all(|tv| Type::function(vec![Type::List(Box::new(tv))], Type::Int)),
        |args| {
            match_call_args!(args, Value::List(vs), {
                Ok(Value::Integer(vs.len() as i32))
            })
        },
    );
    insert_function(
        env,
        ty_env,
        s("list-ref"),
        Type::for_all(|tv| Type::function(vec![Type::List(Box::new(tv.clone())), Type::Int], tv)),
        |args| {
            match_call_args!(args, Value::List(vs), Value::Integer(idx), {
                if let Some(v) = vs.get(*idx as usize) {
                    Ok(v.clone())
                } else {
                    // TODO: Annotate the location
                    Err(Error::Eval("out of range".to_string())
                        .with_null_location()
                        .into())
                }
            })
        },
    );
    insert_function(
        env,
        ty_env,
        s("string->list"),
        Type::function(vec![Type::String], Type::List(Box::new(Type::Char))),
        |args| {
            match_call_args!(args, Value::String(value), {
                let chars = value.chars().map(Value::Char).collect();
                Ok(Value::List(chars))
            })
        },
    );
    insert_function(
        env,
        ty_env,
        s("int->string"),
        Type::function(vec![Type::Int], Type::String),
        |args| {
            match_call_args!(args, Value::Integer(value), {
                let str = value.to_string();
                Ok(Value::String(str))
            })
        },
    );
    insert_function(
        env,
        ty_env,
        s("array->len"),
        Type::for_all(|tv| Type::function(vec![Type::Array(Box::new(tv.clone()))], tv)),
        |args| {
            match_call_args!(args, Value::List(vs), {
                Ok(Value::Integer(vs.len() as i32))
            })
        },
    );
    insert_function(
        env,
        ty_env,
        s("array->get"),
        Type::for_all(|tv| Type::function(vec![Type::Array(Box::new(tv.clone())), Type::Int], tv)),
        |args| {
            match_call_args!(args, Value::List(vs), Value::Integer(idx), {
                if let Some(v) = vs.get(*idx as usize) {
                    Ok(v.clone())
                } else {
                    // TODO: Annotate the location
                    Err(Error::Eval("out of range".to_string())
                        .with_null_location()
                        .into())
                }
            })
        },
    );
    insert_function(
        env,
        ty_env,
        s("array->set"),
        Type::for_all(|tv| {
            Type::function(
                vec![Type::Array(Box::new(tv.clone())), Type::Int, tv],
                Type::Nil,
            )
        }),
        |args| {
            match_call_args!(args, Value::List(_vs), Value::Integer(_idx), _value, {
                todo!()
                // We cannot implement this function because 'vs' is immutable.
                // let idx = *idx as usize;
                // if idx < vs.len() {
                //     vs[idx] = value.clone();
                //     Ok(Value::nil())
                // } else {
                //     // TODO: Annotate the location
                //     Err(Error::Eval("out of range".to_string())
                //         .with_null_location()
                //         .into())
                // }
            })
        },
    );

    insert_function(
        env,
        ty_env,
        s("newline"),
        Type::function(vec![], Type::Any),
        |_| {
            newlineuw();
            Ok(Value::List(vec![]))
        },
    );
    insert_function(
        env,
        ty_env,
        s("write"),
        Type::function(vec![Type::string()], Type::Nil),
        |args| {
            match_call_args!(args, Value::String(str), {
                printuw(str);
                Ok(Value::nil())
            })
        },
    );
    insert_function(
        env,
        ty_env,
        s("io-write"),
        Type::function(vec![Type::Int, Type::Int], Type::Nil),
        |_| {
            printlnuw("Cannot call io-write in interpreter mode.");
            Ok(Value::nil())
        },
    );

    // These functions cannot be defined using `match_call_args!` due to variable arguments.
    // These are defined at `apply_function`.
    insert_variable_as_symbol_and_type(
        env,
        ty_env,
        s("print"),
        Type::for_all(|tv| Type::function(vec![tv], Type::Nil)),
    );
    insert_variable_as_symbol_and_type(
        env,
        ty_env,
        s("display"),
        Type::for_all(|tv| Type::function(vec![tv], Type::Nil)),
    );
    insert_variable_as_symbol_and_type(
        env,
        ty_env,
        s("+"),
        Type::function(vec![Type::Numeric, Type::Numeric], Type::Numeric),
    );
    insert_variable_as_symbol_and_type(
        env,
        ty_env,
        s("-"),
        Type::function(vec![Type::Numeric, Type::Numeric], Type::Numeric),
    );
    insert_variable_as_symbol_and_type(
        env,
        ty_env,
        s("*"),
        Type::function(vec![Type::Numeric, Type::Numeric], Type::Numeric),
    );
    insert_variable_as_symbol_and_type(
        env,
        ty_env,
        s("/"),
        Type::function(vec![Type::Numeric, Type::Numeric], Type::Numeric),
    );
    insert_variable_as_symbol_and_type(
        env,
        ty_env,
        s("or"),
        Type::function(vec![Type::Boolean, Type::Boolean], Type::Boolean),
    );
    insert_variable_as_symbol_and_type(
        env,
        ty_env,
        s("and"),
        Type::function(vec![Type::Boolean, Type::Boolean], Type::Boolean),
    );

    insert_variable_as_symbol_and_type(
        env,
        ty_env,
        s("map"),
        Type::for_all_with_tv("X", |tv| {
            Type::for_all_with_tv("Y", |result| {
                Type::function(
                    vec![
                        Type::function(vec![tv.clone()], result.clone()),
                        Type::List(Box::new(tv.clone())),
                    ],
                    Type::List(Box::new(result)),
                )
            })
        }),
    );
    insert_variable_as_symbol_and_type(
        env,
        ty_env,
        s(">"),
        Type::function(vec![Type::Numeric, Type::Numeric], Type::Boolean),
    );
    insert_variable_as_symbol_and_type(
        env,
        ty_env,
        s(">="),
        Type::function(vec![Type::Numeric, Type::Numeric], Type::Boolean),
    );
    insert_variable_as_symbol_and_type(
        env,
        ty_env,
        s("<"),
        Type::function(vec![Type::Numeric, Type::Numeric], Type::Boolean),
    );
    insert_variable_as_symbol_and_type(
        env,
        ty_env,
        s("<="),
        Type::function(vec![Type::Numeric, Type::Numeric], Type::Boolean),
    );

    // For visibility of Environment.dump_local()
    // env.push_local();
}

/// Evaluate ASTs and return the these results.
///
/// This function visits AST node recursively and process each nodes.
pub fn eval_program(asts: &Program, env: &mut Env) -> Result<Vec<(Value, Type)>> {
    let types = asts.iter().map(|ast| ast.ty.clone()).collect::<Vec<_>>();
    Ok(eval_asts(asts, env)?.into_iter().zip(types).collect())
}
