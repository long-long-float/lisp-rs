pub mod console;
pub mod error;

pub mod ir;
pub mod opt;

pub mod ast;
pub mod environment;
pub mod evaluator;
pub mod macro_expander;
pub mod parser;
pub mod riscv;
pub mod tokenizer;
pub mod typer;

pub mod unique_generator;

use object::elf::*;
use object::write::elf::{FileHeader, ProgramHeader, Writer};
use object::write::StreamingBuffer;
use object::Endianness;
use std::{fs::File, io::BufWriter, io::Write};

use anyhow::Result;

use crate::lispi::{
    environment as env, evaluator as e, macro_expander as m, parser as p, tokenizer as t,
    typer as ty,
};

use self::{
    environment::Environment,
    evaluator::Value,
    parser::{Program, SymbolTable},
};

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
        if self.begin.line == self.end.line {
            write!(f, "{}", self.begin)
        } else {
            write!(f, "{} - {}", self.begin, self.end)
        }
    }
}

pub fn frontend(program: Vec<String>) -> Result<(Program, Environment<Value>, SymbolTable)> {
    // println!("{:#?}", program);
    let tokens = t::tokenize(program)?;
    // println!("{:#?}", tokens);
    let (program, mut sym_table) = p::parse(tokens)?;
    // println!("{:#?}", program);
    let program = m::expand_macros(program, &mut sym_table)?;
    // println!("{:#?}", program);
    let mut env = env::Environment::new();
    let mut ty_env = env::Environment::new();

    e::init_env(&mut env, &mut ty_env, &mut sym_table);
    // sym_table.dump();

    let program = ty::check_and_inference_type(program, &ty_env)?;
    // for ast in &program {
    //     println!("{}", ast);
    // }
    let program = opt::tail_recursion::optimize(program)?;
    // for ast in &program {
    //     println!("{}", ast);
    // }
    Ok((program, env, sym_table))
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
pub fn interpret(program: Vec<String>) -> Result<Vec<(e::Value, ty::Type)>> {
    let (program, mut env, _) = frontend(program)?;
    e::eval_program(&program, &mut env)
}

pub fn compile(program: Vec<String>) -> Result<()> {
    let (program, mut _env, sym_table) = frontend(program)?;

    let mut ir_ctx = ir::IrContext::new();

    let funcs = ir::compiler::compile(program, sym_table, &mut ir_ctx)?;
    for fun in &funcs {
        fun.dump(&ir_ctx.bb_arena);
    }
    let funcs = opt::constant_folding::optimize(funcs)?;
    for fun in &funcs {
        fun.dump(&ir_ctx.bb_arena);
    }
    let codes = riscv::generate_code(funcs, &mut ir_ctx)?;

    let big_endian = true;

    let mut codes = codes
        .into_iter()
        .map(|code| {
            let mut codes = code.to_be_bytes();
            if big_endian {
                codes.reverse();
            }
            codes
        })
        .flatten()
        .collect::<Vec<_>>();

    let mut output = StreamingBuffer::new(BufWriter::new(File::create("out.elf")?));
    let mut writer = Writer::new(Endianness::Little, false, &mut output);
    // References: https://keens.github.io/blog/2020/04/12/saishougennoelf/
    writer.reserve_file_header();
    writer.reserve_program_headers(1);

    let p_offset = writer.reserve(codes.len(), 4) as u64;

    writer.write_file_header(&FileHeader {
        os_abi: 0x00,
        abi_version: 0x00,
        e_type: ET_EXEC,
        e_machine: EM_RISCV,
        e_entry: 0x000000,
        e_flags: 0x00,
    })?;
    writer.write_program_header(&ProgramHeader {
        p_type: PT_LOAD,
        p_flags: 0x05,
        p_offset,
        p_vaddr: 0x000000,
        p_paddr: 0x000000,
        p_filesz: codes.len() as u64,
        p_memsz: codes.len() as u64,
        p_align: 0x200000,
    });
    writer.write(&codes);

    let mut output = File::create("out.bin")?;
    output.write_all(&mut codes)?;

    Ok(())
}

pub fn interpret_with_env(
    program: Vec<String>,
    env: &mut env::Environment<e::Value>,
    ty_env: &mut env::Environment<ty::Type>,
    sym_table: &mut SymbolTable,
) -> Result<Vec<(e::Value, ty::Type)>> {
    let tokens = t::tokenize(program)?;
    let program = p::parse_with_env(tokens, sym_table)?;
    let program = m::expand_macros(program, sym_table)?;
    let program = ty::check_and_inference_type(program, &ty_env)?;
    let program = opt::tail_recursion::optimize(program)?;
    e::eval_program(&program, env)
}
