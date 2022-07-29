use std::collections::{HashMap, LinkedList};

use super::{error::*, parser::*};

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
        let mut local = self.local_stack.last_mut().unwrap();
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
                            "car" => {
                                let args = eval_asts(raw_args, env)?;
                                if let Some(Value::List(vs)) = args.get(0) {
                                    let first = vs.first().map(|v| (**v).clone());
                                    Ok(first.unwrap_or(Value::Nil))
                                } else {
                                    Err(Error::Eval(
                                        "'car' is formed as (car list_value)".to_string(),
                                    ))
                                }
                            }
                            "cdr" => {
                                let args = eval_asts(raw_args, env)?;
                                if let Some(Value::List(vs)) = args.get(0) {
                                    if let Some((_, rest)) = vs.split_first() {
                                        if rest.is_empty() {
                                            Ok(Value::Nil)
                                        } else {
                                            Ok(Value::List(rest.to_vec()))
                                        }
                                    } else {
                                        Ok(Value::Nil)
                                    }
                                } else {
                                    Err(Error::Eval(
                                        "'cdr' is formed as (cdr list_value)".to_string(),
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
                            _ => Err(Error::Eval(format!("Unknown function: {}", func_name))),
                        }
                    }
                    Value::Function {
                        name,
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
        Ast::Integer(value) => Ok(Value::Integer(*value)),
        Ast::Symbol(value) => {
            // println!("{:#?}", env.variables);
            if let Some(value) = env.find_var(value) {
                Ok(value.clone())
            } else {
                Err(Error::Eval(format!("{:?} is not defined", value)))
            }
        }
        Ast::Quoted(value) => Ok(ast_to_value(&**value)),
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
    }
}

pub fn eval_program(asts: &Program) -> Result<Vec<Value>, Error> {
    let mut env = Environment::new();

    // Pre-defined functions
    // TODO: Add function symbols with its definition
    env.insert_variable_as_symbol("print");
    env.insert_variable_as_symbol("+");
    env.insert_variable_as_symbol("-");
    env.insert_variable_as_symbol("*");
    env.insert_variable_as_symbol("car");
    env.insert_variable_as_symbol("cdr");
    env.insert_variable_as_symbol("defun");
    env.insert_variable_as_symbol("setq");

    eval_asts(asts, &mut env)
}
