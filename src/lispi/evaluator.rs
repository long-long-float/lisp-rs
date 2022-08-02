use std::{collections::HashMap, f32::consts::E, fmt::format, os::macos::raw};

use super::{error::*, parser::*};

macro_rules! bug {
    () => {
        Error::Bug {
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
            Err(bug!())
        }
    };

    ( $args:expr, $p:pat, $( $ps:pat ),*, $b:block, $index:expr ) => {
        if let Some(ValueWithType { value: $p, type_: _ }) = $args.get($index) {
            match_args!($args, $( $ps ),*, $b, ($index + 1))
        }
        else {
            Err(bug!())
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
    Symbol(String),
    List(Vec<ValueWithType>),
    Function {
        name: String,
        args: Vec<String>,
        body: Vec<Ast>,
    },
    NativeFunction {
        name: String,
        func: fn(Vec<ValueWithType>) -> EvalResult,
    },
    Nil,
}

impl Value {
    fn is_true(&self) -> bool {
        *self != Value::Nil
    }

    fn get_type(&self) -> Type {
        match self {
            Value::Integer(_) => Type::int(),
            Value::Symbol(_) => Type::symbol(),
            Value::List(_) => Type::list(),
            Value::Function {
                name: _,
                args: _,
                body: _,
            } => {
                // TODO: Return concrete type
                Type::Any
            }
            Value::NativeFunction { name: _, func } => {
                // TODO: Return concrete type
                Type::Any
            }
            Value::Nil => Type::list(),
        }
    }

    pub fn with_type(self) -> ValueWithType {
        let type_ = self.get_type();
        ValueWithType { value: self, type_ }
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        if value {
            Value::Symbol("T".to_string())
        } else {
            Value::Nil
        }
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

    fn update_or_insert_var(&mut self, name: String, value: ValueWithType) {
        if let Some(found) = self.find_var_mut(&name) {
            // TODO: Check type
            found.value = value.value;
        } else {
            self.insert_var(name, value);
        }
    }

    // TODO: Take ValueWithType
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

fn eval_special_form(name: &Ast, raw_args: &[Ast], env: &mut Environment) -> EvalResult {
    if let Ast::Symbol(name) = name {
        let name = name.as_str();
        match name {
            "setq" => {
                if let (Some(Ast::Symbol(name)), Some(value)) = (raw_args.get(0), raw_args.get(1)) {
                    let value = eval_ast(value, env)?;
                    env.update_or_insert_var(name.clone(), value);
                    Ok(Value::Nil.with_type())
                } else {
                    Err(Error::Eval(
                        "'setq' is formed as (setq symbol value)".to_string(),
                    ))
                }
            }
            "defun" => {
                if let (Some(Ast::Symbol(name)), Some(Ast::List(args)), (_, body)) =
                    (raw_args.get(0), raw_args.get(1), raw_args.split_at(2))
                {
                    let args = args
                        .iter()
                        .map(|arg| {
                            if let Ast::Symbol(v) = arg {
                                Ok(v.clone())
                            } else {
                                Err(Error::Eval(format!("{:?} is not an symbol.", arg)))
                            }
                        })
                        .collect::<Result<Vec<String>, Error>>()?;

                    let arg_types = args.iter().map(|_| Type::Any).collect();
                    let func = Value::Function {
                        name: name.clone(),
                        args: args,
                        body: body.to_vec(),
                    };
                    env.insert_var(
                        name.clone(),
                        ValueWithType {
                            value: func,
                            type_: Type::function(arg_types, Type::Any),
                        },
                    );

                    Ok(Value::Nil.with_type())
                } else {
                    Err(Error::Eval(
                        "'defun' is formed as (defun name (arg ...) body ...)".to_string(),
                    ))
                }
            }
            "if" => {
                if let (Some(cond), Some(then_ast)) = (raw_args.get(0), raw_args.get(1)) {
                    let cond = eval_ast(cond, env)?.value.is_true();
                    if cond {
                        eval_ast(then_ast, env)
                    } else {
                        println!("{:?}", raw_args.get(2));
                        if let Some(else_ast) = raw_args.get(2) {
                            eval_ast(else_ast, env)
                        } else {
                            Ok(Value::Nil.with_type())
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
                        let result = eval_asts(forms, env)?;
                        Ok(result.last().unwrap_or(&Value::Nil.with_type()).clone())
                    } else {
                        Ok(Value::Nil.with_type())
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
                                let result = eval_asts(body, env)?;
                                return Ok(result
                                    .last()
                                    .unwrap_or(&Value::Nil.with_type())
                                    .clone());
                            }
                        } else {
                            return Err(Error::Eval(err.to_string()));
                        }
                    } else {
                        return Err(Error::Eval(err.to_string()));
                    }
                }

                Ok(Value::Nil.with_type())
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
            _ => Err(Error::DoNothing),
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
                "+" | "-" | "*" => {
                    let args = args
                        .iter()
                        .map(|arg| {
                            if let Value::Integer(v) = arg.value {
                                Ok(v)
                            } else {
                                Err(Error::Eval(format!("{:?} is not an integer.", arg)))
                            }
                        })
                        .collect::<Result<Vec<i32>, Error>>()?;

                    let sum = match func_name {
                        "+" => args.iter().sum(),
                        "-" => {
                            if args.len() >= 1 {
                                let (head, args) = args.split_first().unwrap();
                                let mut res = *head;
                                for arg in args {
                                    res -= arg;
                                }
                                res
                            } else {
                                0
                            }
                        }
                        "*" => args.iter().fold(1, |acc, arg| acc * arg),
                        _ => return Err(Error::Eval(format!("Unknown function: {}", func_name))),
                    };
                    Ok(Value::Integer(sum).with_type())
                }
                "print" => {
                    for arg in args {
                        println!("{:?}", arg);
                    }
                    Ok(Value::Nil.with_type())
                }
                "mapcar" => {
                    let err = "'mapcar' is formed as (mapcar function list ...)";

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
                                        .unwrap_or(Value::Nil.with_type()),
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
        } => {
            env.push_local();

            for (name, value) in arg_names.iter().zip(args) {
                env.insert_var(name.clone(), value.clone());
            }

            let result = eval_asts(&body, env);

            env.pop_local();

            let result = result?;
            Ok(result.last().unwrap_or(&Value::Nil.with_type()).clone())
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
                Ok(Value::Nil.with_type())
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
        _ => Ok(ast_to_value(ast).with_type()),
    }
}

fn ast_to_value(node: &Ast) -> Value {
    match node {
        Ast::Integer(v) => Value::Integer(*v),
        Ast::Symbol(v) => Value::Symbol(v.clone()),
        Ast::Quoted(v) => ast_to_value(&*v),
        Ast::List(vs) => {
            let vs = vs.iter().map(|v| ast_to_value(v).with_type()).collect();
            Value::List(vs)
        }
        Ast::Nil => Value::Nil,
    }
}

pub fn eval_program(asts: &Program) -> Result<Vec<ValueWithType>, Error> {
    let mut env = Environment::new();

    // Pre-defined functions and special forms
    // TODO: Add function symbols with its definition
    env.insert_function(
        "evenp",
        Type::function(vec![Type::int()], Type::Any),
        |args| {
            match_args!(args, Value::Integer(v), {
                Ok(Value::from(v % 2 == 0).with_type())
            })
        },
    );
    env.insert_function(
        "car",
        Type::function(vec![Type::list()], Type::Any),
        |args| {
            match_args!(args, Value::List(vs), {
                let first = vs.first().map(|v| (*v).clone());
                Ok(first.unwrap_or(Value::Nil.with_type()))
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
                        Ok(Value::Nil.with_type())
                    } else {
                        Ok(Value::List(rest.to_vec()).with_type())
                    }
                } else {
                    Ok(Value::Nil.with_type())
                }
            })
        },
    );
    // TODO: Make zerop and mod to accept number
    env.insert_function(
        "zerop",
        Type::function(vec![Type::int()], Type::Any),
        |args| {
            match_args!(args, Value::Integer(v), {
                Ok(Value::from(*v == 0).with_type())
            })
        },
    );
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

    env.insert_variable_as_symbol("print");
    env.insert_variable_as_symbol("+");
    env.insert_variable_as_symbol("-");
    env.insert_variable_as_symbol("*");
    env.insert_variable_as_symbol("mapcar");

    // Pre-defined symbols
    env.insert_variable_as_symbol("T");

    eval_asts(asts, &mut env)
}
