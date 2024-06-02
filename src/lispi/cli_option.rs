use std::collections::HashSet;

use clap::{Parser, ValueEnum};
use strum::IntoEnumIterator;
use strum_macros::EnumIter;

#[derive(Parser)]
#[clap(author, version, about, long_about=None)]
/// An interpreter of Scheme (subset)
pub struct CliOption {
    /// Path of the script. If this option is not specified, it will run in REPL mode.
    #[clap(value_parser)]
    pub filename: Option<String>,

    #[clap(short, long, action = clap::ArgAction::SetTrue)]
    pub compile: bool,

    #[clap(short, long, value_enum)]
    pub dump: Vec<DumpOptions>,

    #[clap(short = 'i', long, value_enum)]
    /// This command is not used. It is intended to switching from `-d`.
    pub ignored_dump: Vec<DumpOptions>,

    #[clap(long, action = clap::ArgAction::SetTrue)]
    pub dump_files: bool,

    #[clap(long, action = clap::ArgAction::SetTrue)]
    pub dump_register_allocation: bool,

    #[clap(long, action = clap::ArgAction::SetTrue)]
    pub without_opts: bool,
}

impl CliOption {
    pub fn dump_opts(&self) -> HashSet<DumpOptions> {
        if self.dump.contains(&DumpOptions::All) {
            HashSet::from_iter(DumpOptions::iter())
        } else {
            HashSet::from_iter(self.dump.clone())
        }
    }
}

impl Default for CliOption {
    fn default() -> Self {
        CliOption {
            filename: None,
            compile: false,
            dump: Vec::new(),
            ignored_dump: Vec::new(),
            dump_files: false,
            dump_register_allocation: false,
            without_opts: false,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, ValueEnum, EnumIter)]
pub enum DumpOptions {
    All,
    Tokens,
    AST,
    PreprocessedAST,
    Type,
    OptimizedAST,
    RawIR,
    TranslateCmp,
    RemoveRefAndDeref,
    PlaceOnMemory,
    RemoveRedundantAssignments,
    ConstantFolding,
    ImmediateUnfolding,
    RemoveUncalledFunctions,
    RemovePhiNodes,
    RegisterAllocation,
    MachineInstructions,
}
