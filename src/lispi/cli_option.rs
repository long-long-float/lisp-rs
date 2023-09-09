use clap::Parser;

#[derive(Parser)]
#[clap(author, version, about, long_about=None)]
/// An interpreter of Scheme (subset)
pub struct CliOption {
    /// Path of the script. If this option is not specified, it will run in REPL mode.
    #[clap(value_parser)]
    pub filename: Option<String>,

    #[clap(short, long, action = clap::ArgAction::SetTrue)]
    pub compile: bool,

    #[clap(short, long, action = clap::ArgAction::SetTrue)]
    pub dump: bool,

    #[clap(long, action = clap::ArgAction::SetTrue)]
    pub dump_register_allocation: bool,

    #[clap(long, action = clap::ArgAction::SetTrue)]
    pub without_opts: bool,
}
