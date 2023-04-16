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

pub mod cli_option;

use object::elf::*;
use object::write::elf::{FileHeader, ProgramHeader, SectionHeader, Sym, Writer};
use object::write::StreamingBuffer;
use object::Endianness;
use std::{fs::File, io::BufWriter, io::Write};

use colored::*;

use anyhow::Result;

use crate::lispi::ast::dump_asts;
use crate::lispi::cli_option::CliOption;
use crate::lispi::{
    environment as env, evaluator as e, macro_expander as m, parser as p, tokenizer as t,
    typer as ty,
};

use self::console::printlnuw;
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

    fn newline(&mut self) {
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

pub fn frontend(
    program: Vec<String>,
    opt: &CliOption,
) -> Result<(Program, Environment<Value>, SymbolTable)> {
    let tokens = t::tokenize(program)?;

    if opt.dump {
        println!("{}", "Tokens:".red());
        for token in &tokens {
            println!("{}", token);
        }
        println!();
    }

    let (program, mut sym_table) = p::parse(tokens)?;

    if opt.dump {
        println!("{}", "Parsed AST:".red());
        dump_asts(&program);
        println!();
    }

    let program = m::expand_macros(program, &mut sym_table)?;

    let mut env = env::Environment::default();
    let mut ty_env = env::Environment::default();

    e::init_env(&mut env, &mut ty_env, &mut sym_table);
    // sym_table.dump();

    let program = ty::check_and_inference_type(program, &ty_env, &mut sym_table)?;
    // for ast in &program {
    //     println!("{}", ast);
    // }

    let program = opt::tail_recursion::optimize(program)?;

    if opt.dump {
        println!("{}", "Optimized AST:".red());
        dump_asts(&program);
        println!();
    }
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
pub fn interpret(program: Vec<String>, opt: &CliOption) -> Result<Vec<(e::Value, ty::Type)>> {
    let (program, mut env, _) = frontend(program, opt)?;
    e::eval_program(&program, &mut env)
}

pub fn compile(program: Vec<String>, opt: &CliOption) -> Result<()> {
    let (program, mut _env, sym_table) = frontend(program, opt)?;

    let mut ir_ctx = ir::IrContext::new();

    let funcs = ir::compiler::compile(program, sym_table, &mut ir_ctx)?;

    if opt.dump {
        printlnuw(&"Raw IR instructions:".red());
        for fun in &funcs {
            fun.dump(&ir_ctx.bb_arena);
        }
        printlnuw("");
    }

    if !opt.without_opts {
        opt::removing_duplicated_assignments::optimize(&funcs, &mut ir_ctx)?;
        if opt.dump {
            printlnuw(&"Remove duplicated assignments:".red());
            for fun in &funcs {
                fun.dump(&ir_ctx.bb_arena);
            }
            printlnuw("");
        }

        opt::constant_folding::optimize(&funcs, &mut ir_ctx, true)?;
        if opt.dump {
            printlnuw(&"Constant folding:".red());
            for fun in &funcs {
                fun.dump(&ir_ctx.bb_arena);
            }
            printlnuw("");
        }
    }

    let func_with_reg_maps =
        ir::register_allocation::create_interference_graph(funcs, &mut ir_ctx)?;

    if opt.dump {
        printlnuw(&"Register allocation:".red());
        for (fun, reg_map) in &func_with_reg_maps {
            printlnuw(&format!("{}:", fun.name));
            for (var, id) in reg_map {
                printlnuw(&format!("  %{} -> {}", var.name, id));
            }
        }
        printlnuw("");
    }

    let codes = riscv::generate_code(func_with_reg_maps, &mut ir_ctx, opt)?;

    let big_endian = true;

    let codes = codes
        .into_iter()
        .flat_map(|code| {
            let mut codes = code.to_be_bytes();
            if big_endian {
                codes.reverse();
            }
            codes
        })
        .collect::<Vec<_>>();

    let mut output = StreamingBuffer::new(BufWriter::new(File::create("out.elf")?));
    let mut writer = Writer::new(Endianness::Little, false, &mut output);
    // References: https://keens.github.io/blog/2020/04/12/saishougennoelf/
    writer.reserve_file_header();
    writer.reserve_program_headers(1);

    let p_offset = writer.reserve(codes.len(), 4) as u64;

    let text_str = writer.add_section_name(".text".as_bytes());
    let main_str = writer.add_string("main".as_bytes());

    writer.reserve_symtab_section_index();
    writer.reserve_symbol_index(None);
    writer.reserve_symtab();

    writer.reserve_strtab_section_index();
    writer.reserve_strtab();

    writer.reserve_shstrtab_section_index();
    writer.reserve_shstrtab();

    writer.reserve_section_index();
    writer.reserve_section_headers();

    writer.write_file_header(&FileHeader {
        os_abi: 0x00,
        abi_version: 0x00,
        e_type: ET_REL,
        e_machine: EM_RISCV,
        e_entry: 0x000000,
        e_flags: 0x00,
    })?;
    // This is needed for rv32emu
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

    writer.write_null_symbol();
    writer.write_symbol(&Sym {
        name: Some(main_str),
        section: None,
        st_info: (STB_GLOBAL << 4) | STT_FUNC,
        st_other: STV_DEFAULT,
        st_shndx: 2, //TODO: Use variable rather than magic number
        st_value: 0,
        st_size: codes.len() as u64,
    });

    writer.write_strtab();

    writer.write_shstrtab();

    writer.write_null_section_header();
    writer.write_symtab_section_header(0);
    writer.write_strtab_section_header();
    writer.write_shstrtab_section_header();
    writer.write_section_header(&SectionHeader {
        name: Some(text_str),
        sh_type: SHT_PROGBITS,
        sh_flags: SHF_EXECINSTR as u64,
        sh_addr: 0x000000,
        sh_offset: p_offset,
        sh_size: codes.len() as u64,
        sh_link: 0,
        sh_info: 0,
        sh_addralign: 0x4,
        sh_entsize: 0,
    });

    let mut output = File::create("out.bin")?;
    output.write_all(&codes)?;

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
    let program = ty::check_and_inference_type(program, ty_env, sym_table)?;
    let program = opt::tail_recursion::optimize(program)?;
    e::eval_program(&program, env)
}
