use std::collections::HashMap;

use super::{error::*, parser::*};

#[derive(Clone, Debug)]
pub enum Value {
    Integer(i32),
    Symbol(String),
    List(Vec<Box<Value>>),
    Nil,
}

struct Environment {
    variables: HashMap<String, Value>,
}

impl Environment {
    fn insert_variable_as_symbol(&mut self, name: &str) {
        let name = name.to_string();
        self.variables.insert(name.clone(), Value::Symbol(name));
    }
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
                                    env.variables.insert(name.clone(), value.clone());
                                    Ok(Value::Nil)
                                } else {
                                    Err(Error::Eval(
                                        "'setq' is formed as (setq symbol value)".to_string(),
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
                    _ => Err(Error::Eval(format!("{:?} is not a function", first))),
                }
            } else {
                Ok(Value::Nil)
            }
        }
        Ast::Integer(value) => Ok(Value::Integer(*value)),
        Ast::Symbol(value) => {
            // println!("{:#?}", env.variables);
            if let Some(value) = env.variables.get(value) {
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
    let mut env = Environment {
        variables: HashMap::new(),
    };
    // Pre-defined functions
    env.insert_variable_as_symbol("print");
    env.insert_variable_as_symbol("+");
    env.insert_variable_as_symbol("-");
    env.insert_variable_as_symbol("*");
    env.insert_variable_as_symbol("setq");

    asts.iter()
        .map(|ast| eval_ast(ast, &mut env))
        .collect::<Result<Vec<Value>, Error>>()
}
