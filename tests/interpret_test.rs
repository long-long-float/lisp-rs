use lisp_rs::lispi::{error::Error, evaluator::*, parser::*, tokenizer::*};
use std::stringify;

fn interp(program: &str) -> Result<Value, Error> {
    let lines = program.split('\n').map(|l| l.to_string()).collect();
    let result = tokenize(lines)
        .and_then(parse)
        .and_then(|ast| eval_program(&ast))?;
    Ok(result.last().unwrap().clone().value)
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
    let vs = vs.iter().map(|v| Value::Integer(*v).with_type()).collect();
    Value::List(vs)
}

fn build_sym_list(vs: Vec<&str>) -> Value {
    let vs = vs
        .iter()
        .map(|v| Value::Symbol((*v).to_owned()).with_type())
        .collect();
    Value::List(vs)
}

#[test]
fn literal_test() {
    assert_eq!(Ok(Value::Integer(3)), interp("3"));
    assert_eq!(Ok(Value::Float(3.14)), interp("3.14"));
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
fn map_test() {
    assert_eq!(
        Ok(build_list(vec![11, 22, 33])),
        interp("(map + '(1 2 3) '(10 20 30))")
    );

    assert_eq!(
        Ok(build_list(vec![1, 9, 16])),
        interp(
            r#"
(define square (lambda (x) (* x x)))
(map square '(1 3 4))
"#
        )
    );
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
(define x 1)
(define y 2)
(+ x y)"#
        )
    );
}

#[test]
fn type_test() {
    assert_error!(&interp("(car 1)"), Error::Type(_));
    assert_error!(&interp("(car '(1 2) 1)"), Error::Type(_));
}

#[test]
fn define_error_test() {
    assert_error!(&interp("(define 1 2)"), Error::Eval(_));
    assert_error!(&interp("(define x 2 'err)"), Error::Eval(_));
}

#[test]
fn if_test() {
    assert_eq!(Ok(Value::Integer(3)), interp("(if 1 (+ 1 2) (+ 3 4))"));
    assert_eq!(Ok(Value::Integer(3)), interp("(if #t (+ 1 2) (+ 3 4))"));
    assert_eq!(Ok(Value::Integer(7)), interp("(if #f (+ 1 2) (+ 3 4))"));

    assert_eq!(Ok(Value::Integer(2)), interp("(if 1 2 3)"));
    assert_eq!(Ok(Value::Integer(2)), interp("(if (even? 2) 2 3)"));
    assert_eq!(Ok(Value::Integer(3)), interp("(if (even? 1) 2 3)"));

    assert_eq!(Ok(Value::Integer(3)), interp("(if 1 (+ 1 2))"));
    assert_eq!(Ok(Value::nil()), interp("(if #f (+ 1 2))"));
}

#[test]
fn list_test() {
    assert_eq!(Ok(build_list(vec![1, 2, 3])), interp("'(1 2 3)"));
    assert_eq!(
        Ok(build_list(vec![1, 2, 3])),
        interp(
            r#"
(define xs '(1 2 3))
xs"#
        )
    );
    assert_eq!(
        Ok(build_sym_list(vec!["a", "b"])),
        interp("(car '((a b) (c d) (e f)))")
    );
    assert_eq!(
        Ok(Value::List(vec![
            build_sym_list(vec!["c", "d"]).with_type(),
            build_sym_list(vec!["e", "f"]).with_type(),
        ])),
        interp("(cdr '((a b) (c d) (e f)))")
    );

    assert_eq!(Ok(Value::nil()), interp("(cdr '(a))"));
}

#[test]
fn function_test() {
    assert_eq!(
        Ok(Value::Integer(25)),
        interp(
            r#"
(define square (lambda (x) (* x x)))
(square 5)"#
        )
    );

    assert_eq!(
        Ok(Value::Integer(25)),
        interp(
            r#"
(define x 10)
(define square (lambda (x) (* x x)))
(square 5)"#
        )
    );

    assert_eq!(
        Ok(Value::Integer(10)),
        interp(
            r#"
(define x 10)
(define square (lambda (x) (* x x)))
(square 5)
x"#
        )
    );

    assert_eq!(
        Ok(Value::Integer(10)),
        interp(
            r#"
(define y 10)
(define set-y (lambda (x) 
    (set! y x)))
(set-y 5)
y
"#
        )
    );

    assert_eq!(
        Ok(Value::Integer(24)),
        interp(
            r#"
(define fact (lambda (x)
  (if (= x 0)
      1
    (* x (fact (- x 1))))))

(fact 4)
"#
        )
    );
}

#[test]
fn lambda_test() {
    assert_eq!(Ok(Value::Integer(25)), interp("((lambda (x) (* x x)) 5)"));

    assert_eq!(
        Ok(Value::Integer(25)),
        interp(
            r#"
(define x 10)
((lambda (x) (* x x)) 5)"#
        )
    );
}

#[test]
fn macro_test() {
    assert_eq!(
        Ok(build_list(vec![20, 10])),
        interp(
            r#"
(define-macro my-push (item place)
  (list 'set!
        place
        (list 'cons item place)))

(define stack '())
(my-push 10 stack)
(my-push 20 stack)
stack"#
        )
    );
}

#[test]
fn let_test() {
    assert_eq!(
        Ok(Value::Integer(6)),
        interp("(let ((a 1) (b 2) (c 3)) (+ a b c))")
    );

    assert_eq!(
        Ok(Value::Integer(0)),
        interp(
            r#"
(define a 0)
(let ((a 1) (b 2) (c 3))
    (+ a b c)
    (set! a 9))
a"#
        )
    );

    assert_error!(
        interp("(let ((a 1) (b a) (c b)) (+ a b c))"),
        Error::Eval(_)
    );
}

#[test]
fn let_star_test() {
    assert_eq!(
        Ok(Value::Integer(6)),
        interp("(let* ((a 1) (b 2) (c 3)) (+ a b c))")
    );

    assert_eq!(
        Ok(Value::Integer(0)),
        interp(
            r#"
(define a 0)
(let* ((a 1) (b 2) (c 3))
    (+ a b c)
    (set! a 9))
a"#
        )
    );

    assert_eq!(
        Ok(Value::Integer(3)),
        interp("(let* ((a 1) (b a) (c b)) (+ a b c))")
    );
}

#[test]
fn named_let_test() {
    assert_eq!(
        Ok(Value::Integer(10)),
        interp(
            r#"
(define a 0)
(let loop ((i 0)) (if (< i 10)
    (set! (+ a 1))
    (loop (+ i 1))))
a"#
        )
    );
}
