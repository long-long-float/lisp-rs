use anyhow::Result;
use clap::Parser;
use crossterm::cursor;
use crossterm::event;
use crossterm::event::{read, Event, KeyEvent};
use crossterm::terminal;
use crossterm::ExecutableCommand;
use std::collections::VecDeque;
use std::fs::File;
use std::io::{self, stdout, BufRead};
use std::path::Path;

use lisp_rs::lispi::error::ErrorWithLocation;
use lisp_rs::lispi::{console as c, error::Error, evaluator as e, parser as p, tokenizer as t};
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
        // Run the program from file

        let lines = read_lines(&filename)?;

        // Run the program as following steps.
        // Program as text --(tokenize)-->
        //   Tokens --(parse)-->
        //   Abstract Syntax Tree (AST) --(eval_program)-->
        //   Evaluated result value
        //
        // Functions of each steps return Result to express errors.
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
        // REPL mode

        terminal::enable_raw_mode()?;

        let prompt = "(lisp-rs) > ";

        c::print(prompt)?;

        let mut history: VecDeque<Vec<String>> = VecDeque::new();
        history.push_front(Vec::new());

        // 0 is the position where a user is inputing.
        let mut history_pos = 0;

        let mut cursor_pos = 0;

        let set_program = |prog: String, cursor_pos: &mut usize| -> std::io::Result<()> {
            stdout()
                .execute(cursor::MoveToColumn(1))?
                .execute(terminal::Clear(terminal::ClearType::CurrentLine))?;
            c::print(prompt)?;
            c::print(&prog)?;

            *cursor_pos = prog.len();

            Ok(())
        };

        let mut env = e::Environment::new();
        e::init_env(&mut env);

        loop {
            let buffer = &mut history[history_pos];

            match read()? {
                Event::Key(KeyEvent { code, modifiers }) => match code {
                    event::KeyCode::Char(ch) => {
                        if ch == 'c' && modifiers == event::KeyModifiers::CONTROL {
                            c::newline()?;
                            c::print(prompt)?;

                            if history_pos == 0 {
                                buffer.clear();
                            }

                            history_pos = 0;
                            cursor_pos = 0;

                            continue;
                        }

                        if ch == 'd' && modifiers == event::KeyModifiers::CONTROL {
                            terminal::disable_raw_mode()?;
                            return Ok(());
                        }

                        if cursor_pos < buffer.len() {
                            buffer.insert(cursor_pos, ch.to_string());
                        } else {
                            buffer.push(ch.to_string());
                        }

                        let left_shift = buffer.len() - cursor_pos - 1;

                        set_program(buffer.join(""), &mut cursor_pos)?;

                        cursor_pos -= left_shift;
                        stdout().execute(cursor::MoveLeft(left_shift.try_into().unwrap()))?;
                    }
                    event::KeyCode::Backspace => {
                        if cursor_pos > 0 {
                            buffer.remove(cursor_pos - 1);

                            let left_shift = buffer.len() + 1 - cursor_pos;

                            set_program(buffer.join(""), &mut cursor_pos)?;

                            cursor_pos -= left_shift;
                            stdout().execute(cursor::MoveLeft(left_shift.try_into().unwrap()))?;
                        }
                    }
                    event::KeyCode::Enter => {
                        c::newline()?;

                        if !buffer.is_empty() {
                            let lines = vec![buffer.join("")];
                            let results = t::tokenize(lines.clone())
                                .and_then(|tokens| p::parse_with_env(tokens, &mut env))
                                .and_then(|asts| e::eval_asts(&asts, &mut env));
                            match results {
                                Ok(results) => {
                                    if let Some(result) = results.last() {
                                        c::printlnuw(&format!(
                                            "{}: {}",
                                            result.value, result.type_
                                        ));
                                    }
                                }
                                Err(err) => show_error(err, "".to_string(), lines),
                            }
                        }

                        c::print(prompt)?;

                        if history_pos >= 2 {
                            history[0] = buffer.clone();
                        }

                        if !history[0].is_empty() {
                            history.push_front(Vec::new());
                        }

                        history_pos = 0;
                        cursor_pos = 0;
                    }
                    event::KeyCode::Right => {
                        if cursor_pos < buffer.len() {
                            stdout().execute(cursor::MoveRight(1))?;
                            cursor_pos += 1;
                        }
                    }
                    event::KeyCode::Left => {
                        if cursor_pos > 0 {
                            stdout().execute(cursor::MoveLeft(1))?;
                            cursor_pos -= 1;
                        }
                    }
                    event::KeyCode::Up => {
                        if history_pos < history.len() - 1 {
                            history_pos += 1;

                            let program = history[history_pos].join("");
                            set_program(program, &mut cursor_pos)?;
                        }
                    }
                    event::KeyCode::Down => {
                        if history_pos > 0 {
                            history_pos -= 1;

                            let program = history[history_pos].join("");
                            set_program(program, &mut cursor_pos)?;
                        }
                    }
                    _ => {}
                },
                _ => {}
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

/// Show an error as human readable format (like rustc)
fn show_error(err: anyhow::Error, filename: String, lines: Vec<String>) {
    if let Some(ErrorWithLocation { err, location }) = err.downcast_ref::<ErrorWithLocation>() {
        let range = match location {
            TokenLocation::Range(range) => Some(*range),
            TokenLocation::EOF => {
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
                c::printlnuw(&format!("{} at {}:{}:{}", err, filename, bline, bcol));

                let lineno = bline.to_string();
                let left = " ".repeat(lineno.len()) + " |";
                c::printlnuw(&left);
                let underline = " ".repeat(bcol - 1) + "^".repeat(ecol - bcol).as_str();

                c::printlnuw(&format!(
                    "{} | {}",
                    lineno,
                    lines
                        .get(bline - 1)
                        .map(|l| l.to_string())
                        .unwrap_or_else(|| "".to_string())
                ));
                c::printlnuw(&format!("{} {}", left, underline));
            } else {
                c::printlnuw(&format!(
                    "{} at {}:{}:{} - {}:{}",
                    err, filename, bline, bcol, eline, ecol
                ));

                let max_lineno_len = eline.to_string().len();
                let left = " ".repeat(max_lineno_len) + " |";
                c::printlnuw(&left);

                for line in bline..=eline {
                    let lineno = line.to_string();
                    c::printlnuw(&format!(
                        "{}{} | > {}",
                        lineno,
                        " ".repeat(max_lineno_len - lineno.len()),
                        lines
                            .get(line - 1)
                            .map(|l| l.to_string())
                            .unwrap_or_else(|| "".to_string())
                    ));
                }
                c::printlnuw(&left);
            }
        } else {
            c::printlnuw(&err);
        }
    } else {
        c::printlnuw(&err);
    }
}
