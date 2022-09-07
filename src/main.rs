use anyhow::Result;
use clap::Parser;
use std::fs::File;
use std::io::{self, BufRead, Write};
use std::path::Path;

use lisp_rs::lispi::error::ErrorWithLocation;
use lisp_rs::lispi::{error::Error, evaluator as e, parser as p, tokenizer as t};
use lisp_rs::lispi::{Location, LocationRange, TokenLocation};

#[derive(Parser)]
#[clap(author, version, about, long_about=None)]
/// An interpreter of Scheme (subset)
struct Cli {
    /// Path of the script. If this option is not specified, it will run in REPL mode.
    #[clap(value_parser)]
    filename: Option<String>,
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    if let Some(filename) = cli.filename {
        let lines = read_lines(&filename)?;
        let result = t::tokenize(lines.clone())
            .and_then(p::parse)
            .and_then(|(ast, env)| e::eval_program(&ast, env));

        match result {
            Ok(result) => {
                if let Some(result) = result.last() {
                    println!("{}: {}", result.value, result.type_);
                }
            }
            Err(err) => show_error(err, filename, lines),
        }
    } else {
        // let mut sym_env = Environment::new();
        let mut env = e::Environment::new();
        e::init_env(&mut env);
        loop {
            print!("(lisp-rs) > ");
            io::stdout().flush()?;

            let mut buf = String::new();
            io::stdin().read_line(&mut buf)?;
            let lines = vec![buf];

            let results = t::tokenize(lines.clone())
                .and_then(|tokens| p::parse_with_env(tokens, &mut env))
                .and_then(|asts| e::eval_asts(&asts, &mut env));
            match results {
                Ok(results) => {
                    if let Some(result) = results.last() {
                        println!("{}: {}", result.value, result.type_);
                    }
                }
                Err(err) => show_error(err, "".to_string(), lines),
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

fn show_error(err: anyhow::Error, filename: String, lines: Vec<String>) {
    if let Some(ErrorWithLocation { err, location }) = err.downcast_ref::<ErrorWithLocation>() {
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
