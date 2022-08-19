use std::collections::HashMap;

use super::{error::*, parser::*};

macro_rules! bug {
    () => {
        bug!("".to_string())
    };
    ( $msg:expr ) => {
        Error::Bug {
            message: $msg,
            file: file!(),
            line: line!(),
        }
    };
}

macro_rules! match_args {
    ( $args:expr, $p:pat, $b:block, $index:expr ) => {
        if let Some(ValueWithType { value: $p, type_: _ }) = $args.get($index) {
            $b
        }
        else {
            Err(bug!(format!("Cannot match {} with {:?}", stringify!($p), $args.get($index))))
        }
    };

    ( $args:expr, $p:pat, $( $ps:pat ),*, $b:block, $index:expr ) => {
        if let Some(ValueWithType { value: $p, type_: _ }) = $args.get($index) {
            match_args!($args, $( $ps ),*, $b, ($index + 1))
        }
        else {
            Err(bug!(format!("Cannot match {} with {:?}", stringify!($p), $args.get($index))))
        }
    };

    ( $args:expr, $( $ps:pat ),+, $b:block ) => {
        // Patterns must be matched because args are passed type checking
        match_args!($args, $( $ps ),+, $b, 0)
    };
}

type EvalResult = Result<ValueWithType, Error>;

#[derive(Clone, PartialEq, Debug)]
pub enum Value {
    Integer(i32),
    Float(f32),
    Boolean(bool),
    Char(char),
    Symbol(String),
    List(Vec<ValueWithType>),
    Function {
        name: String,
        args: Vec<String>,
        body: Vec<Ast>,
        is_macro: bool,
    },
    NativeFunction {
        name: String,
        func: fn(Vec<ValueWithType>) -> EvalResult,
    },

    // For macro expansion
    RawAst(Ast),
}

impl Value {
    pub fn nil() -> Value {
        Value::List(Vec::new())
    }

    fn is_true(&self) -> bool {
        match self {
            Value::Boolean(false) => false,
            _ => true,
        }
    }

    fn get_type(&self) -> Type {
        match self {
            Value::Integer(_) => Type::int(),
            Value::Float(_) => Type::float(),
            Value::Symbol(_) => Type::symbol(),
            Value::Boolean(_) => Type::scala("boolean"),
            Value::Char(_) => Type::scala("char"),
            Value::List(_) => Type::list(),
            Value::Function {
                name: _,
                args: _,
                body: _,
                is_macro: _,
            } => {
                // TODO: Return concrete type
                Type::Any
            }
            Value::NativeFunction { name: _, func: _ } => {
                // TODO: Return concrete type
                Type::Any
            }
            Value::RawAst(_) => Type::Any,
        }
    }

    pub fn with_type(self) -> ValueWithType {
        let type_ = self.get_type();
        ValueWithType { value: self, type_ }
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
            Value::List(vs) => {
                if vs.len() == 0 {
                    write!(f, "Nil")
                } else {
                    write!(f, "(")?;
                    for (i, v) in vs.iter().enumerate() {
                        write!(f, "{}", v.value)?;
                        if i < vs.len() - 1 {
                            write!(f, ", ")?;
                        }
                    }
                    write!(f, ")")?;
                    Ok(())
                }
            }
            Value::Function {
                name,
                args: _,
                body: _,
                is_macro,
            } => {
                if *is_macro {
                    write!(f, "MACRO {}", name)
                } else {
                    write!(f, "FUNCTION {}", name)
                }
            }
            Value::NativeFunction { name, func: _ } => {
                write!(f, "FUNCTION {}", name)
            }
            Value::RawAst(ast) => write!(f, "AST {:?}", ast),
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
            Ast::Symbol(v) => Value::Symbol(v.clone()),
            Ast::Quoted(v) => (&**v).into(),
            Ast::List(vs) => {
                let vs = vs.iter().map(|v| Value::from(v).with_type()).collect();
                Value::List(vs)
            }
            Ast::Nil => Value::nil(),
        }
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Value::Boolean(value)
    }
}

struct Environment {
    local_stack: Vec<Local>,
}

impl Environment {
    fn new() -> Environment {
        let mut env = Environment {
            local_stack: Vec::new(),
        };
        env.push_local();
        env
    }

    fn update_var(&mut self, name: String, value: ValueWithType) -> Result<(), Error> {
        if let Some(found) = self.find_var_mut(&name) {
            // TODO: Check type
            found.value = value.value;
            Ok(())
        } else {
            Err(Error::Eval(format!("{} is not defined.", name)))
        }
    }

    fn insert_var(&mut self, name: String, value: ValueWithType) {
        // local_stack must have least one local
        let local = self.local_stack.last_mut().unwrap();
        local.variables.insert(name, value);
    }

    fn find_var(&self, name: &String) -> Option<&ValueWithType> {
        for local in self.local_stack.iter().rev() {
            if let Some(value) = local.variables.get(name) {
                return Some(value);
            }
        }
        None
    }

    fn find_var_mut(&mut self, name: &String) -> Option<&mut ValueWithType> {
        for local in self.local_stack.iter_mut().rev() {
            if let Some(value) = local.variables.get_mut(name) {
                return Some(value);
            }
        }
        None
    }

    fn insert_function(
        &mut self,
        name: &str,
        type_: Type,
        func: fn(Vec<ValueWithType>) -> EvalResult,
    ) {
        let name = name.to_string();
        self.insert_var(
            name.clone(),
            ValueWithType {
                value: Value::NativeFunction { name, func },
                type_,
            },
        );
    }

    fn insert_variable_as_symbol(&mut self, name: &str) {
        let name = name.to_string();
        self.insert_var(name.clone(), Value::Symbol(name).with_type());
    }

    fn push_local(&mut self) {
        self.local_stack.push(Local {
            variables: HashMap::new(),
        });
    }

    fn pop_local(&mut self) {
        self.local_stack.pop();
    }
}

struct Local {
    variables: HashMap<String, ValueWithType>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct ValueWithType {
    pub value: Value,
    pub type_: Type,
}

#[derive(Clone, PartialEq, Debug)]
pub enum Type {
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
}

impl Type {
    fn scala(name: &str) -> Type {
        Type::Scala(name.to_string())
    }

    fn int() -> Type {
        Type::scala("int")
    }

    fn float() -> Type {
        Type::scala("float")
    }

    fn symbol() -> Type {
        Type::scala("symbol")
    }

    fn list() -> Type {
        Type::Composite {
            name: "list".to_string(),
            inner: Vec::new(),
        }
    }

    fn function(args: Vec<Type>, result: Type) -> Type {
        Type::Function {
            args: args.iter().map(|a| Box::new(a.clone())).collect(),
            result: Box::new(result),
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
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
        }
    }
}

fn check_arg_types(func_name: &str, args: &[ValueWithType], types: &[Type]) -> Result<(), Error> {
    if args.len() != types.len() {
        return Err(Error::Type(format!(
            "{} arguments are expected, but {} arguments are specified.",
            types.len(),
            args.len()
        )));
    }

    for (i, (a, t)) in args.iter().zip(types).enumerate() {
        match (&a.type_, t) {
            (Type::Any, _) | (_, Type::Any) => (), // Pass-through
            (actual, expected) => {
                if actual != expected {
                    return Err(Error::Type(format!("Expected the type {} , but the type {} is specified in {}th argument in {} function", expected, actual, i, func_name)));
                }
            }
        }
    }

    Ok(())
}

fn eval_asts(asts: &[Ast], env: &mut Environment) -> Result<Vec<ValueWithType>, Error> {
    asts.iter()
        .map(|arg| eval_ast(arg, env))
        .collect::<Result<Vec<ValueWithType>, Error>>()
}

fn get_last_result(results: Vec<ValueWithType>) -> ValueWithType {
    results
        .into_iter()
        .last()
        .unwrap_or(Value::nil().with_type())
}

fn get_symbol_values(symbols: &Vec<Ast>) -> Result<Vec<String>, Error> {
    symbols
        .iter()
        .map(|symbol| {
            if let Ast::Symbol(v) = symbol {
                Ok(v.clone())
            } else {
                Err(Error::Eval(format!("{:?} is not an symbol.", symbol)))
            }
        })
        .collect()
}

fn eval_special_form(name_ast: &Ast, raw_args: &[Ast], env: &mut Environment) -> EvalResult {
    if let Ast::Symbol(name) = name_ast {
        let name = name.as_str();
        match name {
            "set!" => {
                if let (Some(Ast::Symbol(name)), Some(value)) = (raw_args.get(0), raw_args.get(1)) {
                    let value = eval_ast(value, env)?;
                    env.update_var(name.clone(), value)?;
                    Ok(Value::nil().with_type())
                } else {
                    Err(Error::Eval(
                        "'set!' is formed as (set! symbol value)".to_string(),
                    ))
                }
            }
            "define" => {
                if let (Some(Ast::Symbol(name)), Some(value)) = (raw_args.get(0), raw_args.get(1)) {
                    let value = eval_ast(value, env)?;

                    env.insert_var(name.clone(), value);

                    Ok(Value::nil().with_type())
                } else {
                    Err(Error::Eval(
                        "'define' is formed as (define name (arg ...) body ...)".to_string(),
                    ))
                }
            }
            "define-macro" => {
                if let (Some(Ast::Symbol(fun_name)), Some(Ast::List(args)), (_, body)) =
                    (raw_args.get(0), raw_args.get(1), raw_args.split_at(2))
                {
                    let is_macro = name == "define-macro";

                    let args = get_symbol_values(args)?;

                    let arg_types = args.iter().map(|_| Type::Any).collect();
                    let func = Value::Function {
                        name: fun_name.clone(),
                        args: args,
                        body: body.to_vec(),
                        is_macro,
                    };
                    env.insert_var(
                        fun_name.clone(),
                        ValueWithType {
                            value: func,
                            type_: Type::function(arg_types, Type::Any),
                        },
                    );

                    Ok(Value::nil().with_type())
                } else {
                    Err(Error::Eval(
                        "'define' is formed as (define name (arg ...) body ...)".to_string(),
                    ))
                }
            }
            "lambda" => {
                if let Some((Ast::List(args), body)) = raw_args.split_first() {
                    let args = get_symbol_values(args)?;

                    let arg_types = args.iter().map(|_| Type::Any).collect();
                    let func = Value::Function {
                        name: "".to_string(),
                        args: args,
                        body: body.to_vec(),
                        is_macro: false,
                    };

                    Ok(ValueWithType {
                        value: func,
                        type_: Type::function(arg_types, Type::Any),
                    })
                } else {
                    Err(Error::Eval(
                        "'lambda' is formed as (lambda (arg ...) body ...)".to_string(),
                    ))
                }
            }
            "let" | "let*" => {
                let err = Err(Error::Eval(
                    "'let' is formed as (let ([id expr] ...) body ...) or named let (let proc-id ([id expr] ...) body ...)".to_string(),
                ));

                let sequence = name == "let*";

                if let Some((Ast::List(vars), body)) = raw_args.split_first() {
                    env.push_local();

                    let mut exprs = Vec::new();

                    for var in vars {
                        if let Ast::List(var) = var {
                            if let (Some(Ast::Symbol(id)), Some(expr)) = (var.get(0), var.get(1)) {
                                let expr = eval_ast(expr, env)?;
                                if sequence {
                                    env.insert_var(id.clone(), expr);
                                } else {
                                    exprs.push((id, expr));
                                }
                            } else {
                                return err;
                            }
                        } else {
                            return err;
                        }
                    }

                    if !sequence {
                        for (id, expr) in exprs {
                            env.insert_var(id.clone(), expr);
                        }
                    }

                    let result = eval_asts(body, env);

                    env.pop_local();

                    Ok(get_last_result(result?))
                } else if let (Some(Ast::Symbol(proc_id)), Some(Ast::List(args)), (_, body)) =
                    (raw_args.get(0), raw_args.get(1), raw_args.split_at(2))
                {
                    let mut arg_exprs = Vec::new();
                    for arg in args {
                        if let Ast::List(var) = arg {
                            if let (Some(Ast::Symbol(id)), Some(expr)) = (var.get(0), var.get(1)) {
                                arg_exprs.push((id.clone(), expr.clone()));
                            } else {
                                return err;
                            }
                        } else {
                            return err;
                        }
                    }
                    let (args, exprs): (_, Vec<Ast>) = arg_exprs.into_iter().unzip();

                    let func = Value::Function {
                        name: proc_id.clone(),
                        args,
                        body: body.to_vec(),
                        is_macro: false,
                    };

                    env.push_local();
                    env.insert_var(proc_id.clone(), func.with_type());

                    let mut call_args = vec![Ast::Symbol(proc_id.clone())];
                    let mut exprs = exprs;
                    call_args.append(&mut exprs);

                    let result = eval_asts(&vec![Ast::List(call_args)], env);

                    env.pop_local();

                    Ok(get_last_result(result?))
                } else {
                    err
                }
            }
            "begin" => Ok(get_last_result(eval_asts(raw_args, env)?)),
            "if" => {
                if let (Some(cond), Some(then_ast)) = (raw_args.get(0), raw_args.get(1)) {
                    let cond = eval_ast(cond, env)?.value.is_true();
                    if cond {
                        eval_ast(then_ast, env)
                    } else {
                        if let Some(else_ast) = raw_args.get(2) {
                            eval_ast(else_ast, env)
                        } else {
                            Ok(Value::nil().with_type())
                        }
                    }
                } else {
                    Err(Error::Eval(
                        "'if' is formed as (if cond then else)".to_string(),
                    ))
                }
            }
            "when" | "unless" => {
                let invert = name == "unless";
                if let Some((cond, forms)) = raw_args.split_first() {
                    let cond = eval_ast(cond, env)?.value.is_true();
                    let cond = if invert { !cond } else { cond };
                    if cond {
                        Ok(get_last_result(eval_asts(forms, env)?))
                    } else {
                        Ok(Value::nil().with_type())
                    }
                } else {
                    Err(Error::Eval(format!(
                        "'{}' is formed as (if cond then else)",
                        name
                    )))
                }
            }
            "cond" => {
                let err = "'cond' is formed as (cond (cond body ...) ...)";

                for arg in raw_args {
                    if let Ast::List(arm) = arg {
                        if let Some((cond, body)) = arm.split_first() {
                            let cond = eval_ast(cond, env)?;
                            if cond.value.is_true() {
                                return Ok(get_last_result(eval_asts(body, env)?));
                            }
                        } else {
                            return Err(Error::Eval(err.to_string()));
                        }
                    } else {
                        return Err(Error::Eval(err.to_string()));
                    }
                }

                Ok(Value::nil().with_type())
            }
            "function" => {
                if let Some(func) = raw_args.first() {
                    let result = eval_ast(func, env)?;
                    if let Value::Symbol(name) = result.value {
                        Ok(eval_ast(&Ast::Symbol(name), env)?)
                    } else {
                        Ok(result)
                    }
                } else {
                    Err(Error::Eval(
                        "'function' is formed as (function name)".to_string(),
                    ))
                }
            }
            _ => {
                let mac = eval_ast(name_ast, env)?;
                if let Value::Function {
                    name: _,
                    args,
                    body,
                    is_macro: true,
                } = mac.value
                {
                    env.push_local();

                    for (name, value) in args.iter().zip(raw_args) {
                        env.insert_var(name.clone(), Value::RawAst(value.clone()).with_type());
                    }

                    let result = eval_asts(&body, env);

                    env.pop_local();

                    let result = get_last_result(result?);
                    eval_ast(&Ast::from(result.value), env)
                } else {
                    Err(Error::DoNothing)
                }
            }
        }
    } else {
        Err(Error::DoNothing)
    }
}

fn eval_function(name: &Ast, args: &[Ast], env: &mut Environment) -> EvalResult {
    let name = eval_ast(name, env)?;
    let args = eval_asts(args, env)?;

    apply_function(&name, &args, env)
}

fn apply_function(
    func: &ValueWithType,
    args: &[ValueWithType],
    env: &mut Environment,
) -> EvalResult {
    if let ValueWithType {
        value,
        type_: Type::Function {
            args: arg_types,
            result: _,
        },
    } = &func
    {
        let name = match value {
            Value::Symbol(name) => name,
            Value::Function {
                name,
                args: _,
                body: _,
                is_macro: _,
            } => name,
            Value::NativeFunction { name, func: _ } => name,
            _ => {
                println!("{:?}", value);
                return Err(bug!());
            }
        };
        let arg_types = arg_types.iter().map(|a| *a.clone()).collect::<Vec<Type>>();
        check_arg_types(name, args, &arg_types)?;
    }

    match &func.value {
        Value::Symbol(func_name) => {
            let func_name = func_name.as_str();

            match func_name {
                // Functions
                "+" | "-" | "*" | "/" => {
                    enum Number {
                        Int(i32),
                        Float(f32),
                    }

                    let mut has_float_arg = false;
                    let args = args
                        .iter()
                        .map(|arg| match arg.value {
                            Value::Integer(v) => Ok(Number::Int(v)),
                            Value::Float(v) => {
                                has_float_arg = true;
                                Ok(Number::Float(v))
                            }
                            _ => Err(Error::Eval(format!("{:?} is not an integer.", arg))),
                        })
                        .collect::<Result<Vec<Number>, Error>>()?;

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
                                        )));
                                    }
                                }
                                _ => {
                                    return Err(Error::Eval(format!(
                                        "Unknown function: {}",
                                        func_name
                                    )))
                                }
                            };
                        };
                    }

                    if has_float_arg {
                        let mut args = args.iter().map(|arg| match arg {
                            &Number::Int(v) => v as f32,
                            &Number::Float(v) => v,
                        });
                        Ok(Value::Float(calc!(args, f32)).with_type())
                    } else {
                        let mut args = args.iter().map(|arg| match arg {
                            &Number::Int(v) => v,
                            &Number::Float(v) => v as i32,
                        });
                        Ok(Value::Integer(calc!(args, i32)).with_type())
                    }
                }
                "print" => {
                    for arg in args {
                        println!("{}", arg.value);
                    }
                    Ok(Value::nil().with_type())
                }
                "display" => {
                    for arg in args {
                        print!("{}", arg.value);
                    }
                    Ok(Value::nil().with_type())
                }
                "list" => Ok(Value::List(args.to_vec()).with_type()),
                "map" => {
                    let err = "'map' is formed as (mapcar function list ...)";

                    if let Some((func, lists)) = args.split_first() {
                        let lists = lists
                            .iter()
                            .map(|list| {
                                if let Value::List(elements) = &list.value {
                                    Ok(elements)
                                } else {
                                    Err(Error::Eval(err.to_string()))
                                }
                            })
                            .collect::<Result<Vec<_>, Error>>()?;

                        if lists.len() == 0 {
                            return Err(Error::Eval(err.to_string()));
                        }

                        let mut result = Vec::new();
                        let list0_len = lists.get(0).unwrap().len();
                        for idx in 0..list0_len {
                            let mut args = Vec::new();
                            for list in &lists {
                                args.push(
                                    list.get(idx)
                                        .map(|v| v.clone())
                                        .unwrap_or(Value::nil().with_type()),
                                );
                            }

                            result.push(apply_function(func, &args, env)?);
                        }

                        Ok(Value::List(result).with_type())
                    } else {
                        Err(Error::Eval(err.to_string()))
                    }
                }
                _ => Err(Error::Eval(format!("Unknown function: {}", func_name))),
            }
        }
        Value::Function {
            name: _,
            args: arg_names,
            body,
            is_macro: false,
        } => {
            env.push_local();

            for (name, value) in arg_names.iter().zip(args) {
                env.insert_var(name.clone(), value.clone());
            }

            let result = eval_asts(&body, env);

            env.pop_local();

            Ok(get_last_result(result?))
        }
        Value::NativeFunction { name: _, func } => func(args.to_vec()),
        _ => Err(Error::Eval(format!("{:?} is not a function", func.value))),
    }
}

fn eval_ast(ast: &Ast, env: &mut Environment) -> EvalResult {
    match ast {
        Ast::List(elements) => {
            if let Some((first, rest)) = elements.split_first() {
                let result = eval_special_form(first, rest, env);
                match result {
                    Err(Error::DoNothing) => eval_function(first, rest, env),
                    _ => result,
                }
            } else {
                Ok(Value::nil().with_type())
            }
        }
        Ast::Symbol(value) => {
            // println!("{:#?}", env.variables);
            if let Some(var) = env.find_var(value) {
                Ok(var.clone())
            } else {
                Err(Error::Eval(format!("{:?} is not defined", value)))
            }
        }
        _ => Ok(Value::from(ast).with_type()),
    }
}

pub fn eval_program(asts: &Program) -> Result<Vec<ValueWithType>, Error> {
    let mut env = Environment::new();

    // Pre-defined functions and special forms
    // TODO: Add function symbols with its definition
    env.insert_function(
        "even?",
        Type::function(vec![Type::int()], Type::Any),
        |args| {
            match_args!(args, Value::Integer(v), {
                Ok(Value::from(v % 2 == 0).with_type())
            })
        },
    );
    env.insert_function(
        "=",
        Type::function(vec![Type::Any, Type::Any], Type::Any),
        |args| match_args!(args, v1, v2, { Ok(Value::from(v1 == v2).with_type()) }),
    );
    env.insert_function(
        "car",
        Type::function(vec![Type::list()], Type::Any),
        |args| {
            match_args!(args, Value::List(vs), {
                let first = vs.first().map(|v| (*v).clone());
                Ok(first.unwrap_or(Value::nil().with_type()))
            })
        },
    );
    env.insert_function(
        "cdr",
        Type::function(vec![Type::list()], Type::Any),
        |args| {
            match_args!(args, Value::List(vs), {
                if let Some((_, rest)) = vs.split_first() {
                    if rest.is_empty() {
                        Ok(Value::nil().with_type())
                    } else {
                        Ok(Value::List(rest.to_vec()).with_type())
                    }
                } else {
                    Ok(Value::nil().with_type())
                }
            })
        },
    );
    // TODO: Make mod to accept number
    env.insert_function(
        "mod",
        Type::function(vec![Type::int(), Type::int()], Type::int()),
        |args| {
            match_args!(args, Value::Integer(num), Value::Integer(divisor), {
                Ok(Value::Integer(num % divisor).with_type())
            })
        },
    );
    env.insert_function(
        ">",
        Type::function(vec![Type::int(), Type::int()], Type::Any),
        |args| {
            match_args!(args, Value::Integer(x), Value::Integer(y), {
                Ok(Value::from(x > y).with_type())
            })
        },
    );
    env.insert_function(
        "<",
        Type::function(vec![Type::int(), Type::int()], Type::Any),
        |args| {
            match_args!(args, Value::Integer(x), Value::Integer(y), {
                Ok(Value::from(x < y).with_type())
            })
        },
    );
    env.insert_function(
        "cons",
        Type::function(vec![Type::Any, Type::list()], Type::list()),
        |args| {
            match_args!(args, v, Value::List(vs), {
                let mut vs = vs.clone();
                vs.insert(0, v.clone().with_type());
                Ok(Value::List(vs).with_type())
            })
        },
    );
    env.insert_function("newline", Type::function(vec![], Type::Any), |args| {
        println!();
        Ok(Value::List(vec![]).with_type())
    });

    env.insert_variable_as_symbol("print");
    env.insert_variable_as_symbol("display");
    env.insert_variable_as_symbol("list");
    env.insert_variable_as_symbol("+");
    env.insert_variable_as_symbol("-");
    env.insert_variable_as_symbol("*");
    env.insert_variable_as_symbol("/");
    env.insert_variable_as_symbol("map");

    eval_asts(asts, &mut env)
}
