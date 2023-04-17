use std::stringify;

mod common;

use lisp_rs::lispi::{
    cli_option::CliOption,
    error::{Error, ErrorWithLocation},
    evaluator::*,
    interpret, SymbolValue,
};

fn interp(program: &str) -> Result<Value, Error> {
    let lines = program.split('\n').map(|l| l.to_string()).collect();

    let opt = CliOption {
        filename: None,
        compile: false,
        dump: false,
        without_opts: false,
    };

    let result = interpret(lines, &opt);
    match result {
        Ok(result) => Ok(result.last().unwrap().0.clone()),
        Err(err) => {
            if let Some(err) = err.downcast_ref::<ErrorWithLocation>() {
                Err(err.err.clone())
            } else {
                // Must not reach here
                Err(Error::DoNothing)
            }
        }
    }
}

fn build_list(vs: Vec<i32>) -> Value {
    let vs = vs.iter().map(|v| Value::Integer(*v)).collect();
    Value::List(vs)
}

#[test]
fn literal_test() {
    assert_eq!(Ok(Value::Integer(3)), interp("3"));
    assert_eq!(Ok(Value::Float(3.15)), interp("3.15"));
    assert_eq!(Ok(Value::Integer(3)), interp("+3"));
    assert_eq!(Ok(Value::Integer(-3)), interp("-3"));

    assert_eq!(
        Ok(Value::String("Hello World! こんにちは".to_string())),
        interp("\"Hello World! こんにちは\"")
    );

    assert_eq!(
        Ok(Value::Symbol(SymbolValue {
            value: "hello".to_string(),
            id: 0
        })),
        interp("'hello")
    );

    assert_error!(interp("'(1 2 3)"), Error::Type(_));
}

#[test]
fn arithmetic_test() {
    assert_eq!(Ok(Value::Integer(3)), interp("(+ 1 2)"));
    assert_eq!(Ok(Value::Integer(-1)), interp("(- 1 2)"));
    assert_eq!(Ok(Value::Integer(6)), interp("(* 2 3)"));
    // assert_eq!(Ok(Value::Integer(60)), interp("(+ 10 20 30)"));
    assert_eq!(Ok(Value::Integer(1)), interp("(+ (* 1 2) (- 3 4))"));

    // assert_eq!(Ok(Value::Integer(0)), interp("(+)"));
    assert_eq_eps!(2.2, interp("(+ 1 1.2)"));
    // assert_eq_eps!(6.0, interp("(+ 1 2 3.0)"));
    assert_eq_eps!(3.3, interp("(+ 1.1 2.2)"));

    // assert_eq!(Ok(Value::Integer(-1)), interp("(- 1)"));
    assert_eq_eps!(-0.2, interp("(- 1 1.2)"));
    // assert_eq_eps!(-4.0, interp("(- 1 2 3.0)"));
    assert_eq_eps!(-1.1, interp("(- 1.1 2.2)"));

    // assert_eq!(Ok(Value::Integer(1)), interp("(*)"));
    assert_eq!(Ok(Value::Integer(2)), interp("(* 1 2)"));
    assert_eq_eps!(2.0, interp("(* 1 2.0)"));

    // assert_eq_eps!(0.5, interp("(/ 2.0)"));
    assert_eq!(Ok(Value::Integer(0)), interp("(/ 1 2)"));
    assert_eq_eps!(0.5, interp("(/ 1 2.0)"));
}

#[test]
fn map_test() {
    // assert_eq!(
    //     Ok(build_list(vec![11, 22, 33])),
    //     interp("(map + '(1 2 3) '(10 20 30))")
    // );

    assert_eq!(
        Ok(build_list(vec![1, 9, 16])),
        interp(
            r#"
(define square (lambda (x) (* x x)))
(map square (list 1 3 4))
"#
        )
    );
}

#[test]
fn undefined_function_test() {
    assert_error!(&interp("(x 1 2)"), Error::UndefinedVariable(_));
    assert_error!(&interp("(** 1 2)"), Error::UndefinedVariable(_));
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
    assert_error!(&interp("(car 1)"), Error::TypeNotMatched(_, _, _, _));
    assert_error!(&interp("(car '(1 2) 1)"), Error::Type(_));
}

#[test]
fn define_error_test() {
    assert_error!(&interp("(define 1 2)"), Error::Parse(_));
    assert_error!(&interp("(define x 2 'err)"), Error::Parse(_));
}

#[test]
fn if_test() {
    // assert_eq!(Ok(Value::Integer(3)), interp("(if 1 (+ 1 2) (+ 3 4))"));
    assert_eq!(Ok(Value::Integer(3)), interp("(if #t (+ 1 2) (+ 3 4))"));
    assert_eq!(Ok(Value::Integer(7)), interp("(if #f (+ 1 2) (+ 3 4))"));

    // assert_eq!(Ok(Value::Integer(2)), interp("(if 1 2 3)"));
    assert_eq!(Ok(Value::Integer(2)), interp("(if (even? 2) 2 3)"));
    assert_eq!(Ok(Value::Integer(3)), interp("(if (even? 1) 2 3)"));

    // assert_eq!(Ok(Value::Integer(3)), interp("(if 1 (+ 1 2))"));
    assert_eq!(Ok(Value::nil()), interp("(if #f (+ 1 2))"));
}

#[test]
fn cond_test() {
    assert_eq!(
        Ok(Value::List(
            vec!["zero", "one", "other"]
                .iter()
                .map(|s| Value::String(s.to_string()))
                .collect()
        )),
        interp(
            r#"
(define f (lambda (x)
  (cond
   ((= x 0) "zero")
   ((= x 1) "one")
   (#t "other"))))

(list (f 0) (f 1) (f 2))
"#
        )
    );
}

#[test]
fn list_test() {
    assert_eq!(Ok(build_list(vec![1, 2, 3])), interp("(list 1 2 3)"));
    assert_error!(
        interp("(list 1 \"2\" 3)"),
        Error::TypeNotMatched(_, _, _, _)
    );

    assert_eq!(
        Ok(build_list(vec![1, 2, 3])),
        interp(
            r#"
(define xs (list 1 2 3))
xs"#
        )
    );
    assert_eq!(Ok(Value::Integer(1)), interp("(car (list 1 2))"));
    assert_eq!(Ok(build_list(vec![2]),), interp("(cdr (list 1 2))"));

    assert_eq!(Ok(Value::nil()), interp("(cdr (list 0))"));
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
    (define y 0)
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
(let fact ([x 4]) 
  (if (= x 0)
      1
    (* x (fact (- x 1)))))
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
fn closure_test() {
    assert_eq!(
        Ok(build_list(vec![1, 2, 1, 3])),
        interp(
            r#"
(define make-counter (lambda () 
    (define c 0)
    (lambda () 
        (set! c (+ c 1))
        c)))

(define c1 (make-counter))
(define c2 (make-counter))

(list (c1) (c1) (c2) (c1))"#
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

(define stack (list))
(my-push 10 stack)
(my-push 20 stack)
stack"#
        )
    );
}

#[test]
fn let_test() {
    assert_eq!(Ok(Value::Integer(3)), interp("(let ([a 1] [b 2]) (+ a b))"));

    assert_eq!(
        Ok(Value::Integer(0)),
        interp(
            r#"
(define a 0)
(let ([a 1] [b 2])
    (+ a b)
    (set! a 9))
a"#
        )
    );

    assert_error!(
        interp("(let ([a 1] [b a]) (+ a b))"),
        Error::UndefinedVariable(_)
    );
}

#[test]
fn let_star_test() {
    assert_eq!(
        Ok(Value::Integer(3)),
        interp("(let* ((a 1) (b 2)) (+ a b))")
    );

    assert_eq!(
        Ok(Value::Integer(0)),
        interp(
            r#"
(define a 0)
(let* ((a 1) (b 2))
    (+ a b)
    (set! a 9))
a"#
        )
    );

    assert_eq!(
        Ok(Value::Integer(2)),
        interp("(let* ((a 1) (b a)) (+ a b))")
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
    (begin
        (set! a (+ a 1))
        (loop (+ i 1)))))
a"#
        )
    );
}

#[test]
fn optimizing_tail_recursion_test() {
    assert_eq!(
        Ok(Value::Integer(1000)),
        interp(
            r#"
(define a 0)
(let loop ((i 0)) (if (< i 1000)
    (begin
        (set! a (+ a 1))
        (loop (+ i 1)))))
a"#
        )
    );
}
