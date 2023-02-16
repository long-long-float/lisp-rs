mod common;

use lisp_rs::lispi::{
    cli_option::CliOption,
    error::{Error, ErrorWithLocation},
    frontend,
    typer::Type,
};

fn typing(program: &str) -> Result<Type, Error> {
    let lines = program.split('\n').map(|l| l.to_string()).collect();

    let opt = CliOption {
        filename: None,
        compile: false,
        dump: false,
    };

    let result = frontend(lines, &opt);
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
fn list_test() {
    assert_error!(&typing("(car 1)"), Error::TypeNotMatched(_, _, _, _));
    assert_error!(&typing("(car '(1 2) 1)"), Error::Type(_));
}
