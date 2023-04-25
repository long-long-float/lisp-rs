use anyhow::Result;
use clap::Parser;
use crossterm::cursor;
use crossterm::event;
use crossterm::event::{read, Event, KeyEvent};
use crossterm::terminal;
use crossterm::ExecutableCommand;
use lisp_rs::lispi::interpret_with_env;
use std::collections::VecDeque;
use std::fs::File;
use std::io::{self, stdout, BufRead};
use std::path::Path;

use lisp_rs::lispi::cli_option::CliOption;
use lisp_rs::lispi::error::ErrorWithLocation;
use lisp_rs::lispi::*;
use lisp_rs::lispi::{console as c, environment as env, error::Error, evaluator as e};
use lisp_rs::lispi::{Location, LocationRange, TokenLocation};

fn main() -> Result<()> {
    let cli = CliOption::parse();

    if let Some(filename) = &cli.filename {
        let filename = filename.to_owned();

        // Run the program from file
        let lines = read_lines(&filename)?;

        if cli.compile {
            let result = compile(lines.clone(), &cli);
            match result {
                Ok(_) => {}
                Err(err) => show_error(err, filename, lines),
            }
        } else {
            let result = interpret(lines.clone(), &cli);
            match result {
                Ok(result) => {
                    if let Some((result, ty)) = result.last() {
                        println!("{}: {}", result, ty);
                    }
                }
                Err(err) => show_error(err, filename, lines),
            }
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

        let mut env = env::Environment::default();
        let mut ty_env = env::Environment::default();
        e::init_env(&mut env, &mut ty_env);

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

                            let results = interpret_with_env(lines.clone(), &mut env, &mut ty_env);
                            match results {
                                Ok(results) => {
                                    if let Some((result, ty)) = results.iter().last() {
                                        c::printlnuw(&format!("{}: {}", result, ty));
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
        Err(Error::Io("Cannot open source file".to_string()))
    }
}

/// Show an error as human readable format (like rustc)
fn show_error(err: anyhow::Error, filename: String, lines: Vec<String>) {
    if let Some(ErrorWithLocation { err, location }) = err.downcast_ref::<ErrorWithLocation>() {
        match err {
            Error::TypeNotMatched(t0, t1, loc0, loc1) => {
                let (expected_ty, actual_ty, loc) = match (loc0, loc1) {
                    (&TokenLocation::Null, &TokenLocation::Null) => {
                        c::printlnuw(&err);
                        return;
                    }
                    (loc, &TokenLocation::Null) => (t1, t0, loc),
                    (&TokenLocation::Null, loc) => (t0, t1, loc),
                    (loc0, loc1) => {
                        if loc0 != loc1 {
                            c::printlnuw(&format!(
                                "Type error: {} and {} are not matched at {}",
                                t0, t1, filename,
                            ));
                            c::printlnuw(&format!("First type: {}", t0));
                            show_error_location(loc0, &lines);
                            c::printlnuw(&format!("Second type: {}", t1));
                            show_error_location(loc1, &lines);
                            return;
                        } else {
                            (t1, t0, loc0)
                        }
                    }
                };
                c::printlnuw(&format!(
                    "Type error: {} is expected but {} is taken at {}:{}",
                    expected_ty, actual_ty, filename, loc
                ));
                show_error_location(loc, &lines);
            }
            _ => {
                match location {
                    TokenLocation::Range(_) | TokenLocation::EOF => {
                        c::printlnuw(&format!("{} at {}:{}", err, filename, location))
                    }
                    TokenLocation::Null => c::printlnuw(&format!("{} at {}", err, filename)),
                }
                show_error_location(location, &lines);
            }
        }
    } else {
        c::printlnuw(&err);
    }
}

fn show_error_location(location: &TokenLocation, lines: &[String]) {
    let range = match location {
        TokenLocation::Range(range) => Some(*range),
        TokenLocation::EOF => {
            let last_line = lines
                .iter()
                .rev()
                .enumerate()
                .find(|(_, line)| !line.is_empty());
            let (line, column) = last_line
                .map(|(lineno, line)| (if lineno >= 1 { lineno - 1 } else { 0 }, line.len()))
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
    }
}
