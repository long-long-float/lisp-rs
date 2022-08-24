use std::env;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use std::result::Result;

use lisp_rs::lispi::{error::Error, evaluator::*, parser::*, tokenizer::*};

fn main() {
    let args: Vec<String> = env::args().collect();

    let result = read_lines(&args[1])
        .and_then(tokenize)
        .and_then(parse)
        // .and_then(show_ast)
        .and_then(|(ast, env)| eval_program(&ast, env))
        .unwrap_or_else(|err| {
            println!("{:?}", err);
            vec![]
        });

    if let Some(result) = result.last() {
        println!("{}: {}", result.value, result.type_);
    }
}

fn read_lines<P>(filename: P) -> Result<Vec<String>, Error>
where
    P: AsRef<Path>,
{
    if let Ok(file) = File::open(filename) {
        let lines = io::BufReader::new(file)
            .lines()
            .filter_map(|line| line.ok())
            .collect::<Vec<String>>();
        Ok(lines)
    } else {
        Err(Error::Io("Cannot open soure file".to_string()))
    }
}
