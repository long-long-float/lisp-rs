use super::{error::*, parser::*};

#[derive(Debug)]
pub enum Value {
    Integer(i32),
    Symbol(String),
    Nil,
}

fn eval_ast(ast: &Ast) -> Result<Value, Error> {
    match ast {
        Ast::List(elements) => {
            if let Some((first, rest)) = elements.split_first() {
                let first = eval_ast(first)?;
                match first {
                    Value::Symbol(func_name) => {
                        let func_name = func_name.as_str();
                        let args = rest
                            .iter()
                            .map(|arg| eval_ast(arg))
                            .collect::<Result<Vec<Value>, Error>>()?;
                        match func_name {
                            "+" | "-" | "*" => {
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
                            "print" => {
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
        Ast::Symbol(value) => Ok(Value::Symbol(value.clone())),
    }
}

pub fn eval_program(asts: &Program) -> Result<Vec<Value>, Error> {
    asts.iter()
        .map(eval_ast)
        .collect::<Result<Vec<Value>, Error>>()
}
