pub mod console;
pub mod error;

pub mod ast;
pub mod environment;
pub mod evaluator;
pub mod macro_expander;
pub mod parser;
pub mod tokenizer;
pub mod typer;

use anyhow::Result;

use crate::lispi::{
    environment as env, evaluator as e, macro_expander as m, parser as p, tokenizer as t,
    typer as ty,
};

use self::environment::Environment;

#[derive(Clone, Debug)]
pub struct SymbolValue {
    pub value: String,
    pub id: u32,
}

impl PartialEq for SymbolValue {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl SymbolValue {
    pub fn empty() -> SymbolValue {
        SymbolValue {
            value: "".to_string(),
            id: 0,
        }
    }

    pub fn without_id(value: String) -> SymbolValue {
        SymbolValue { value, id: 0 }
    }
}

/// A location in file
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Location {
    /// zero-based line no
    pub line: usize,
    /// zero-based column no
    pub column: usize,
}

impl Location {
    fn head() -> Location {
        Location { line: 0, column: 0 }
    }

    fn newline(self: &mut Self) {
        self.line += 1;
        self.column = 0;
    }

    pub fn humanize(self) -> Location {
        Location {
            line: self.line + 1,
            column: self.column + 1,
        }
    }
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:{}", self.line + 1, self.column + 1)
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum TokenLocation {
    Range(LocationRange),
    EOF,
    Null,
}

impl std::fmt::Display for TokenLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            TokenLocation::Range(range) => write!(f, "{}", range),
            TokenLocation::Null => write!(f, "NULL"),
            TokenLocation::EOF => write!(f, "EOF"),
        }
    }
}

/// A range in file, `[begin, end)`.
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct LocationRange {
    pub begin: Location,
    pub end: Location,
}

impl LocationRange {
    fn new(begin: Location, end: Location) -> LocationRange {
        LocationRange { begin, end }
    }

    fn merge(self, other: &LocationRange) -> LocationRange {
        LocationRange {
            begin: self.begin,
            end: other.end,
        }
    }
}

impl std::fmt::Display for LocationRange {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} - {}", self.begin, self.end)
    }
}

/// Run the program as following steps.
/// ```text
/// Program as text --(tokenize)-->
///   Tokens --(parse)-->
///   Abstract Syntax Tree (AST) --(eval_program)-->
///   Evaluated result value
/// ```
///
/// Functions of each steps return Result to express errors.
pub fn interpret(program: Vec<String>) -> Result<Vec<e::ValueWithType>> {
    let tokens = t::tokenize(program)?;
    let (program, mut sym_table) = p::parse(tokens)?;
    let program = m::expand_macros(program, &mut sym_table)?;
    let program = ty::check_and_inference_type(program, Environment::new())?;
    for ast in &program {
        println!("{}", ast);
    }
    let env = env::Environment::new();
    e::eval_program(&program, env, sym_table)
}
