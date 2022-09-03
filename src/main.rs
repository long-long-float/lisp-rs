use std::env;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use std::result::Result;

use lisp_rs::lispi::error::ErrorWithLocation;
use lisp_rs::lispi::{error::Error, evaluator::*, parser::*, tokenizer::*};
use lisp_rs::lispi::{Location, LocationRange, TokenLocation};

fn main() {
    let args: Vec<String> = env::args().collect();
    let filename = &args[1];

    match process_frontend(filename) {
        Ok(((ast, env), lines)) => match eval_program(&ast, env) {
            Ok(result) => {
                if let Some(result) = result.last() {
                    println!("{}: {}", result.value, result.type_);
                }
            }
            Err(err) => {
                if let Some(ErrorWithLocation {
                    err,
                    location: TokenLocation::Range(range),
                }) = err.downcast_ref::<ErrorWithLocation>()
                {
                    let LocationRange { begin, end } = range;
                    let Location {
                        line: bline,
                        column: bcol,
                    } = begin.humanize();
                    let Location {
                        line: eline,
                        column: ecol,
                    } = end.humanize();

                    println!("{} at {}:{}:{}", err, filename, bline, bcol);

                    if bline == eline {
                        let lineno = bline.to_string();
                        let left = " ".repeat(lineno.len()) + " |";
                        println!("{}", left);
                        let underline = " ".repeat(bcol - 1) + "^".repeat(ecol - bcol).as_str();

                        println!("{} | {}", lineno, lines[bline - 1]);
                        println!("{} {}", left, underline);
                    } else {
                        let max_lineno_len = eline.to_string().len();
                        let left = " ".repeat(max_lineno_len) + " |";
                        println!("{}", left);

                        for line in bline..=eline {
                            let lineno = line.to_string();
                            println!(
                                "{}{} | > {}",
                                lineno,
                                " ".repeat(max_lineno_len - lineno.len()),
                                lines[line - 1]
                            );
                        }
                        println!("{}", left);
                    }
                } else {
                    println!("{}", err);
                }
            }
        },
        Err(err) => {
            println!("{}", err);
        }
    };
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

fn process_frontend(
    filename: &String,
) -> Result<((Vec<AstWithLocation>, Environment), Vec<String>), Error> {
    let lines = read_lines(filename)?;
    let result = tokenize(lines.clone()).and_then(parse)?;
    Ok((result, lines))
}
