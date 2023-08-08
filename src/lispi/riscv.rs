pub mod cmp_translator;
pub mod code_generator;
pub mod instruction;
pub mod stack_frame;

#[derive(Eq, PartialEq, Hash)]
pub enum Spec {
    /// Base Integer Instruction Set, Version 2.1
    Integer32,
    /// Standard Extension for Integer Multiplication and Division, Version 2.0
    Multiplication,
}
