use lisp_rs::lispi::{error::Error, evaluator::*, parser::*, tokenizer::*};

fn interp(program: &str) -> Result<Value, Error> {
    let lines = program.split('\n').map(|l| l.to_string()).collect();
    let result = tokenize(lines)
        .and_then(parse)
        .and_then(|ast| eval_program(&ast))?;
    Ok(result.last().unwrap().clone())
}

fn has_eval_error(value: &Result<Value, Error>) -> bool {
    match value {
        Err(Error::Eval(_)) => true,
        _ => false,
    }
}

fn build_list(vs: Vec<i32>) -> Value {
    let vs = vs.iter().map(|v| Box::new(Value::Integer(*v))).collect();
    Value::List(vs)
}

#[test]
fn arithmetic_test() {
    assert_eq!(Ok(Value::Integer(3)), interp("(+ 1 2)"));
    assert_eq!(Ok(Value::Integer(-1)), interp("(- 1 2)"));
    assert_eq!(Ok(Value::Integer(6)), interp("(* 2 3)"));
    assert_eq!(Ok(Value::Integer(60)), interp("(+ 10 20 30)"));
    assert_eq!(Ok(Value::Integer(1)), interp("(+ (* 1 2) (- 3 4))"));
}

#[test]
fn undefined_function_test() {
    assert_eq!(true, has_eval_error(&interp("(x 1 2)")));
    assert_eq!(true, has_eval_error(&interp("(** 1 2)")));
}

#[test]
fn variable_test() {
    assert_eq!(Ok(Value::Integer(3)), interp(r#"
(setq x 1)
(setq y 2)
(+ x y)"#));
}

#[test]
fn setq_error_test() {
    assert_eq!(true, has_eval_error(&interp("(setq 1 2)")));
}

#[test]
fn list_test() {
    assert_eq!(Ok(build_list(vec![1, 2, 3])), interp("'(1 2 3)"));
    assert_eq!(Ok(build_list(vec![1, 2, 3])), interp(r#"
(setq xs '(1 2 3))
xs"#));
}
