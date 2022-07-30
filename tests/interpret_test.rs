use lisp_rs::lispi::{error::Error, evaluator::*, parser::*, tokenizer::*};
use std::stringify;

fn interp(program: &str) -> Result<Value, Error> {
    let lines = program.split('\n').map(|l| l.to_string()).collect();
    let result = tokenize(lines)
        .and_then(parse)
        .and_then(|ast| eval_program(&ast))?;
    Ok(result.last().unwrap().clone())
}

macro_rules! assert_error {
    ( $value:expr, $p:pat ) => {
        let has_error = match $value {
            Err($p) => true,
            _ => false,
        };
        assert_eq!(
            true,
            has_error,
            "{} must have an error {}",
            stringify!($value),
            stringify!($p)
        );
    };
}

fn build_list(vs: Vec<i32>) -> Value {
    let vs = vs.iter().map(|v| Box::new(Value::Integer(*v))).collect();
    Value::List(vs)
}

fn build_sym_list(vs: Vec<&str>) -> Value {
    let vs = vs
        .iter()
        .map(|v| Box::new(Value::Symbol((*v).to_owned())))
        .collect();
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
    assert_error!(&interp("(x 1 2)"), Error::Eval(_));
    assert_error!(&interp("(** 1 2)"), Error::Eval(_));
}

#[test]
fn variable_test() {
    assert_eq!(
        Ok(Value::Integer(3)),
        interp(
            r#"
(setq x 1)
(setq y 2)
(+ x y)"#
        )
    );
}

#[test]
fn type_test() {
    assert_error!(&interp("(car 1)"), Error::Type(_));
}

#[test]
fn setq_error_test() {
    assert_error!(&interp("(setq 1 2)"), Error::Eval(_));
    assert_error!(&interp("(setq x 2 'err)"), Error::Eval(_));
}

#[test]
fn if_test() {
    assert_eq!(Ok(Value::Integer(3)), interp("(if 1 (+ 1 2) (+ 3 4))"));
    assert_eq!(Ok(Value::Integer(3)), interp("(if T (+ 1 2) (+ 3 4))"));
    assert_eq!(Ok(Value::Integer(7)), interp("(if Nil (+ 1 2) (+ 3 4))"));

    assert_eq!(Ok(Value::Integer(2)), interp("(if 1 2 3)"));
    assert_eq!(Ok(Value::Integer(2)), interp("(if (evenp 2) 2 3)"));
    assert_eq!(Ok(Value::Integer(3)), interp("(if (evenp 1) 2 3)"));

    assert_eq!(Ok(Value::Integer(3)), interp("(if 1 (+ 1 2))"));
    assert_eq!(Ok(Value::Nil), interp("(if Nil (+ 1 2))"));
}

#[test]
fn list_test() {
    assert_eq!(Ok(build_list(vec![1, 2, 3])), interp("'(1 2 3)"));
    assert_eq!(
        Ok(build_list(vec![1, 2, 3])),
        interp(
            r#"
(setq xs '(1 2 3))
xs"#
        )
    );
    assert_eq!(
        Ok(build_sym_list(vec!["a", "b"])),
        interp("(car '((a b) (c d) (e f)))")
    );
    assert_eq!(
        Ok(Value::List(vec![
            Box::new(build_sym_list(vec!["c", "d"])),
            Box::new(build_sym_list(vec!["e", "f"])),
        ])),
        interp("(cdr '((a b) (c d) (e f)))")
    );

    assert_eq!(Ok(Value::Nil), interp("(cdr '(a))"));
}

#[test]
fn funcion_test() {
    assert_eq!(
        Ok(Value::Integer(25)),
        interp(
            r#"
(defun square (x) (* x x))
(square 5)"#
        )
    );

    assert_eq!(
        Ok(Value::Integer(25)),
        interp(
            r#"
(setq x 10)
(defun square (x) (* x x))
(square 5)"#
        )
    );

    assert_eq!(
        Ok(Value::Integer(10)),
        interp(
            r#"
(setq x 10)
(defun square (x) (* x x))
(square 5)
x"#
        )
    );
}
