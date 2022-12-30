pub mod basic_block;
pub mod compiler;
pub mod instruction;

use typed_arena::Arena;

use self::basic_block::BasicBlock;

pub struct IrContext {
    bb_arena: Arena<BasicBlock>,
}

impl IrContext {
    pub fn new() -> Self {
        Self {
            bb_arena: Arena::new(),
        }
    }
}
