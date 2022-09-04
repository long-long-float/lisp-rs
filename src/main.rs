use anyhow::Result;
use std::env;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;

use lisp_rs::lispi::error::ErrorWithLocation;
use lisp_rs::lispi::{error::Error, evaluator::*, parser::*, tokenizer::*};
use lisp_rs::lispi::{Location, LocationRange, TokenLocation};

fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();
    let filename = &args[1];

    let lines = read_lines(filename)?;
    let result = process_frontend(lines.clone()).and_then(|(ast, env)| eval_program(&ast, env));

    match result {
        Ok(result) => {
            if let Some(result) = result.last() {
                println!("{}: {}", result.value, result.type_);
            }
        }
        Err(err) => {
            if let Some(ErrorWithLocation { err, location }) =
                err.downcast_ref::<ErrorWithLocation>()
            {
                let range = match location {
                    TokenLocation::Range(range) => Some(*range),
                    TokenLocation::EOF => {
                        // let line = lines.len() - 1;
                        let last_line = lines
                            .iter()
                            .rev()
                            .enumerate()
                            .find(|(_, line)| !line.is_empty());
                        let (line, column) = last_line
                            .map(|(lineno, line)| (lineno - 1, line.len()))
                            .unwrap_or((0, 0));
                        Some(LocationRange {
                            begin: Location { line, column },
                            end: Location {
                                line,
                                column: column + 1,
                            },
                        })
                    }
                    TokenLocation::Null => None,
                };
                if let Some(LocationRange { begin, end }) = range {
                    let Location {
                        line: bline,
                        column: bcol,
                    } = begin.humanize();
                    let Location {
                        line: eline,
                        column: ecol,
                    } = end.humanize();

                    if bline == eline {
                        println!("{} at {}:{}:{}", err, filename, bline, bcol);

                        let lineno = bline.to_string();
                        let left = " ".repeat(lineno.len()) + " |";
                        println!("{}", left);
                        let underline = " ".repeat(bcol - 1) + "^".repeat(ecol - bcol).as_str();

                        println!(
                            "{} | {}",
                            lineno,
                            lines
                                .get(bline - 1)
                                .map(|l| l.to_string())
                                .unwrap_or_else(|| "".to_string())
                        );
                        println!("{} {}", left, underline);
                    } else {
                        println!(
                            "{} at {}:{}:{} - {}:{}",
                            err, filename, bline, bcol, eline, ecol
                        );

                        let max_lineno_len = eline.to_string().len();
                        let left = " ".repeat(max_lineno_len) + " |";
                        println!("{}", left);

                        for line in bline..=eline {
                            let lineno = line.to_string();
                            println!(
                                "{}{} | > {}",
                                lineno,
                                " ".repeat(max_lineno_len - lineno.len()),
                                lines
                                    .get(line - 1)
                                    .map(|l| l.to_string())
                                    .unwrap_or_else(|| "".to_string())
                            );
                        }
                        println!("{}", left);
                    }
                } else {
                    println!("{}", err);
                }
            } else {
                println!("{}", err);
            }
        }
    }

    Ok(())
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

fn process_frontend(lines: Vec<String>) -> Result<(Vec<AstWithLocation>, Environment)> {
    tokenize(lines).and_then(parse)
}
