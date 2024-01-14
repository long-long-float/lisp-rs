mod common;

use lisp_rs::lispi::{
    cli_option::CliOption,
    error::{Error, ErrorWithLocation},
    frontend, pass,
    typer::Type,
};

fn typing(program: &str) -> Result<Type, Error> {
    let lines = program.split('\n').map(|l| l.to_string()).collect();

    let opt = CliOption::default();

    let result = frontend(lines, &opt, &pass::Optimize::all());
    match result {
        Ok((asts, _, _)) => Ok(asts.last().unwrap().ty.clone()),
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

#[test]
fn literal_test() {
    assert_eq!(
        typing("(array 1 2 3)"),
        Ok(Type::Array(Box::new(Type::Int)))
    );
}

#[test]
fn list_test() {
    assert_error!(&typing("(car 1)"), Error::TypeNotMatched(_, _, _, _));
    assert_error!(&typing("(car '(1 2) 1)"), Error::Type(_));
}

#[test]
fn type_annot_lambda_test() {
    assert!(typing(
        r#"
(define not (lambda (x: bool)
    (if x #f #t)
))
    "#
    )
    .is_ok());

    assert_error!(
        &typing(
            r#"
(define invalid-not (lambda (x: int)
    (if x #f #t)
))
"#
        ),
        Error::TypeNotMatched(_, _, _, _)
    );
}
