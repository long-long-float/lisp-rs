//!
//! Removing reference and dereference instructions for the same variable.
//!
//! For example, following instructions:
//! ```
//! %var1 = ref %var0
//! ; some instructions...
//! %var2 = deref %var1
//! ````
//!
//! Are converted into:
//!
//! ```
//! ; some instructions...
//! %var2 = %var0
//! ```
//!

use anyhow::Result;

use crate::lispi::ir::{
    basic_block::{Function, IrProgram},
    IrContext,
};

pub fn remove_ref_and_deref(fun: &Function, ir_ctx: &mut IrContext) -> Result<()> {
    Ok(())
}

pub fn optimize(program: &IrProgram, ir_ctx: &mut IrContext) -> Result<()> {
    for fun in &program.funcs {
        remove_ref_and_deref(fun, ir_ctx)?;
    }

    Ok(())
}
