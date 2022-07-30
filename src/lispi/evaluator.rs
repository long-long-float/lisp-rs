use std::{collections::HashMap, fmt::format};

use super::{error::*, parser::*};

macro_rules! match_args {
    ( $args:expr, $p:pat, $b:block, $index:expr ) => {
        #[allow(unused_must_use)]
        if let Some($p) = $args.get($index) {
            $b
        }
        else {
            Err(())
        }
    };

    ( $args:expr, $p:pat, $( $ps:pat ),*, $b:block, $index:expr ) => {
        if let Some($p) = $args.get($index) {
            match_args!($args, $( $ps ),*, $b, ($index + 1))
        }
        else {
            Err(())
        }
    };

    ( $args:expr, $( $ps:pat ),+, $b:block ) => {
        // Patterns must be matched because args are passed type checking
        Ok(match_args!($args, $( $ps ),+, $b, 0).unwrap())
    };
}

#[derive(Clone, PartialEq, Debug)]
pub enum Value {
    Integer(i32),
    Symbol(String),
    List(Vec<Box<Value>>),
    Function {
        name: String,
        args: Vec<String>,
        body: Vec<Ast>,
    },
    Nil,
}

impl Value {
    fn is_true(&self) -> bool {
        *self != Value::Nil
    }

    fn get_type(&self) -> Type {
        match self {
            Value::Integer(_) => Type::scala("int"),
            Value::Symbol(_) => Type::scala("symbol"),
            Value::List(_) => Type::list(),
            Value::Function {
                name: _,
                args: _,
                body: _,
            } => {
                // TODO: Return concrete type
                Type::Any
            }
            Value::Nil => Type::Any,
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

    fn insert_var(&mut self, name: String, value: Value) {
        // local_stack must have least one local
        let local = self.local_stack.last_mut().unwrap();
        local.variables.insert(name, value);
    }

    fn find_var(&self, name: &String) -> Option<&Value> {
        for local in self.local_stack.iter().rev() {
            if let Some(value) = local.variables.get(name) {
                return Some(value);
            }
        }
        None
    }

    fn insert_variable_as_symbol(&mut self, name: &str) {
        let name = name.to_string();
        self.insert_var(name.clone(), Value::Symbol(name));
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
    variables: HashMap<String, Value>,
}

#[derive(Clone, PartialEq, Debug)]
enum Type {
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

fn check_arg_types(func_name: &str, args: &Vec<Value>, types: &Vec<Type>) -> Result<(), Error> {
    if args.len() != types.len() {
        return Err(Error::Type(format!(
            "{} arguments are expected, but {} arguments are specified.",
            types.len(),
            args.len()
        )));
    }

    for (i, (a, t)) in args.iter().zip(types).enumerate() {
        match (a.get_type(), t) {
            (Type::Any, _) | (_, Type::Any) => (), // Pass-through
            (actual, expected) => {
                if actual != *expected {
                    return Err(Error::Type(format!("Expected the type {} , but the type {} is specified in {}th argument in {} function", expected, actual, i, func_name)));
                }
            }
        }
    }

    Ok(())
}

fn eval_asts(asts: &[Ast], env: &mut Environment) -> Result<Vec<Value>, Error> {
    asts.iter()
        .map(|arg| eval_ast(arg, env))
        .collect::<Result<Vec<Value>, Error>>()
}

fn eval_ast(ast: &Ast, env: &mut Environment) -> Result<Value, Error> {
    match ast {
        Ast::List(elements) => {
            if let Some((first, rest)) = elements.split_first() {
                let first = eval_ast(first, env)?;
                match first {
                    Value::Symbol(func_name) => {
                        let func_name = func_name.as_str();
                        let raw_args = rest;
                        match func_name {
                            // Functions
                            "+" | "-" | "*" => {
                                let args = eval_asts(raw_args, env)?;
                                let args = args
                                    .iter()
                                    .map(|arg| {
                                        if let Value::Integer(v) = arg {
                                            Ok(*v)
                                        } else {
                                            Err(Error::Eval(format!(
                                                "{:?} is not an integer.",
                                                arg
                                            )))
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
                                    _ => {
                                        return Err(Error::Eval(format!(
                                            "Unknown function: {}",
                                            func_name
                                        )))
                                    }
                                };
                                Ok(Value::Integer(sum))
                            }
                            "evenp" => {
                                let args = eval_asts(raw_args, env)?;
                                check_arg_types(func_name, &args, &vec![Type::scala("int")])?;

                                match_args!(args, Value::Integer(v), {
                                    let ret = if v % 2 == 0 {
                                        Value::Symbol("T".to_string())
                                    } else {
                                        Value::Nil
                                    };
                                    Ok(ret)
                                })
                            }
                            "car" => {
                                let args = eval_asts(raw_args, env)?;
                                check_arg_types(func_name, &args, &vec![Type::list()])?;

                                match_args!(args, Value::List(vs), {
                                    let first = vs.first().map(|v| (**v).clone());
                                    Ok(first.unwrap_or(Value::Nil))
                                })
                            }
                            "cdr" => {
                                let args = eval_asts(raw_args, env)?;
                                check_arg_types(func_name, &args, &vec![Type::list()])?;

                                match_args!(args, Value::List(vs), {
                                    if let Some((_, rest)) = vs.split_first() {
                                        if rest.is_empty() {
                                            Ok(Value::Nil)
                                        } else {
                                            Ok(Value::List(rest.to_vec()))
                                        }
                                    } else {
                                        Ok(Value::Nil)
                                    }
                                })
                            }

                            // Special forms
                            "setq" => {
                                if let (Some(Ast::Symbol(name)), Some(value)) =
                                    (raw_args.get(0), raw_args.get(1))
                                {
                                    let value = eval_ast(value, env)?;
                                    env.insert_var(name.clone(), value);
                                    Ok(Value::Nil)
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
                                                Err(Error::Eval(format!(
                                                    "{:?} is not an symbol.",
                                                    arg
                                                )))
                                            }
                                        })
                                        .collect::<Result<Vec<String>, Error>>()?;

                                    let func = Value::Function {
                                        name: name.clone(),
                                        args: args,
                                        body: body.to_vec(),
                                    };
                                    env.insert_var(name.clone(), func);

                                    Ok(Value::Nil)
                                } else {
                                    Err(Error::Eval(
                                        "'defun' is formed as (defun name (arg ...) body ...)"
                                            .to_string(),
                                    ))
                                }
                            }
                            "print" => {
                                let args = eval_asts(raw_args, env)?;
                                for arg in args {
                                    println!("{:?}", arg);
                                }
                                Ok(Value::Nil)
                            }
                            "if" => {
                                if let (Some(cond), Some(then_ast)) =
                                    (raw_args.get(0), raw_args.get(1))
                                {
                                    let cond = eval_ast(cond, env)?;
                                    if cond.is_true() {
                                        eval_ast(then_ast, env)
                                    } else {
                                        if let Some(else_ast) = raw_args.get(2) {
                                            eval_ast(else_ast, env)
                                        } else {
                                            Ok(Value::Nil)
                                        }
                                    }
                                } else {
                                    Err(Error::Eval(
                                        "'if' is formed as (if cond then else)".to_string(),
                                    ))
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
                        let args = eval_asts(rest, env)?;

                        env.push_local();

                        for (name, value) in arg_names.iter().zip(args) {
                            env.insert_var(name.clone(), value);
                        }

                        let result = eval_asts(&body[..], env);

                        env.pop_local();

                        let result = result?;
                        Ok(result.last().unwrap_or(&Value::Nil).clone())
                    }
                    _ => Err(Error::Eval(format!("{:?} is not a function", first))),
                }
            } else {
                Ok(Value::Nil)
            }
        }
        Ast::Symbol(value) => {
            // println!("{:#?}", env.variables);
            if let Some(value) = env.find_var(value) {
                Ok(value.clone())
            } else {
                Err(Error::Eval(format!("{:?} is not defined", value)))
            }
        }
        _ => Ok(ast_to_value(ast)),
    }
}

fn ast_to_value(node: &Ast) -> Value {
    match node {
        Ast::Integer(v) => Value::Integer(*v),
        Ast::Symbol(v) => Value::Symbol(v.clone()),
        Ast::Quoted(v) => ast_to_value(&*v),
        Ast::List(vs) => {
            let vs = vs.iter().map(|v| Box::new(ast_to_value(v))).collect();
            Value::List(vs)
        }
        Ast::Nil => Value::Nil,
    }
}

pub fn eval_program(asts: &Program) -> Result<Vec<Value>, Error> {
    let mut env = Environment::new();

    // Pre-defined functions
    // TODO: Add function symbols with its definition
    env.insert_variable_as_symbol("print");
    env.insert_variable_as_symbol("evenp");
    env.insert_variable_as_symbol("+");
    env.insert_variable_as_symbol("-");
    env.insert_variable_as_symbol("*");
    env.insert_variable_as_symbol("car");
    env.insert_variable_as_symbol("cdr");
    env.insert_variable_as_symbol("defun");
    env.insert_variable_as_symbol("setq");
    env.insert_variable_as_symbol("if");

    // Pre-defined symbols
    env.insert_variable_as_symbol("T");

    eval_asts(asts, &mut env)
}
