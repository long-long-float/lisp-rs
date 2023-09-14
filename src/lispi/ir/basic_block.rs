use anyhow::Result;
use colored::Colorize;
use itertools::Itertools;
use std::{collections::VecDeque, fmt::Display, fs::File, io::Write, path::Path, slice::Iter};

use id_arena::{Arena, Id};
use rustc_hash::{FxHashMap, FxHashSet};

use super::instruction::{self as i, AnnotatedInstr};
use crate::lispi::{
    ty::{StructDefinition, StructDefinitions, Type},
    SymbolValue,
};

#[derive(Clone, PartialEq, Debug)]
pub struct BasicBlock {
    pub label: String,
    pub insts: Vec<i::AnnotatedInstr>,

    /// Basic blocks where the control flow goes to
    pub destination_bbs: FxHashSet<Id<BasicBlock>>,

    /// Basic blocks where the control flow comes from
    pub source_bbs: FxHashSet<Id<BasicBlock>>,

    pub preceding_bb: Option<Id<BasicBlock>>,
}

impl BasicBlock {
    pub fn new(label: String, preceding_bb: Option<Id<BasicBlock>>) -> Self {
        Self {
            label,
            insts: Vec::new(),
            destination_bbs: FxHashSet::default(),
            source_bbs: FxHashSet::default(),
            preceding_bb,
        }
    }

    pub fn push_inst(&mut self, inst: i::AnnotatedInstr) {
        self.insts.push(inst);
    }
}

pub trait BasicBlockIdExtension {
    /// Find BasicBlock by BFS
    fn find_forward<'a, F>(&self, arena: &'a Arena<BasicBlock>, pred: F) -> Option<&'a BasicBlock>
    where
        F: FnMut(&'a BasicBlock) -> bool;
}

impl BasicBlockIdExtension for Id<BasicBlock> {
    fn find_forward<'a, F>(
        &self,
        arena: &'a Arena<BasicBlock>,
        mut pred: F,
    ) -> Option<&'a BasicBlock>
    where
        F: FnMut(&'a BasicBlock) -> bool,
    {
        let mut que = VecDeque::new();

        que.push_back(self);

        let mut visited_bbs = FxHashSet::default();

        while let Some(bb) = que.pop_back() {
            if visited_bbs.contains(bb) {
                continue;
            }
            visited_bbs.insert(bb);

            let bb = arena.get(*bb).unwrap();

            if pred(bb) {
                return Some(bb);
            }

            for dbb in &bb.destination_bbs {
                que.push_back(dbb);
            }
        }

        None
    }
}

pub type BasicBlocks = Vec<Id<BasicBlock>>;

#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub args: Vec<(String, Type)>,
    pub free_vars: Vec<SymbolValue>,
    pub ty: Type,
    pub is_lambda: bool,

    pub basic_blocks: BasicBlocks,
}

impl Function {
    pub fn new(
        name: String,
        args: Vec<(String, Type)>,
        free_vars: Vec<SymbolValue>,
        ty: Type,
        is_lambda: bool,
        basic_blocks: BasicBlocks,
    ) -> Self {
        Self {
            name,
            args,
            free_vars,
            ty,
            is_lambda,
            basic_blocks,
        }
    }

    pub fn walk_instructions<'a>(
        &'a self,
        arena: &'a Arena<BasicBlock>,
    ) -> WalkingInstructionIterator<'a> {
        let cur_bb = self.basic_blocks.iter();
        WalkingInstructionIterator::new(arena, cur_bb)
    }

    pub fn dump(&self, arena: &Arena<BasicBlock>) {
        print!("{}", self.display(true, arena));
    }

    pub fn display<'a>(&'a self, colored: bool, arena: &'a Arena<BasicBlock>) -> FunctionDisplay {
        FunctionDisplay {
            func: self,
            colored,
            arena,
        }
    }
}

pub struct WalkingInstructionIterator<'a> {
    arena: &'a Arena<BasicBlock>,
    cur_bb: Iter<'a, Id<BasicBlock>>,
    cur_inst: Option<Iter<'a, AnnotatedInstr>>,

    finished: bool,
}

impl<'a> WalkingInstructionIterator<'a> {
    fn new(arena: &'a Arena<BasicBlock>, cur_bb: Iter<'a, Id<BasicBlock>>) -> Self {
        Self {
            arena,
            cur_bb,
            cur_inst: None,
            finished: false,
        }
    }

    fn load_next_bb(&mut self) {
        let next_bb = self.cur_bb.next();
        match next_bb {
            Some(next_bb) => {
                let next_bb = self.arena.get(*next_bb).unwrap();
                self.cur_inst = Some(next_bb.insts.iter());
            }
            None => {
                self.finished = true;
            }
        }
    }
}

impl<'a> Iterator for WalkingInstructionIterator<'a> {
    type Item = &'a AnnotatedInstr;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            None
        } else {
            match self.cur_inst.as_mut() {
                None => {
                    self.load_next_bb();
                    self.next()
                }
                Some(iter) => {
                    let ret = iter.next();
                    match ret {
                        Some(_) => ret,
                        None => {
                            self.load_next_bb();
                            self.next()
                        }
                    }
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct FunctionDisplay<'a> {
    func: &'a Function,
    colored: bool,
    arena: &'a Arena<BasicBlock>,
}

impl Display for FunctionDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "function {} (", self.func.name)?;
        for (id, ty) in &self.func.args {
            write!(f, "%{}: {}, ", id, ty)?;
        }
        write!(f, ") (")?;
        for id in &self.func.free_vars {
            write!(f, "%{}, ", id)?;
        }
        writeln!(
            f,
            "): {} {{ // {}",
            self.func.ty,
            if self.func.is_lambda { "lambda" } else { "" }
        )?;

        for bb in &self.func.basic_blocks {
            let bb = self.arena.get(*bb).unwrap();
            if self.colored {
                writeln!(f, "  {}:", bb.label.cyan())?;
            } else {
                writeln!(f, "  {}:", bb.label)?;
            }
            for inst in &bb.insts {
                writeln!(f, "  {}", inst.display(self.colored))?;
            }
        }

        writeln!(f, "}}")?;

        Ok(())
    }
}

pub struct IrProgram {
    pub funcs: Vec<Function>,
    pub structs: StructDefinitions,
}

impl IrProgram {
    pub fn map_fun<F>(self, fun: F) -> Result<Self>
    where
        F: FnMut(Function) -> Result<Function>,
    {
        let IrProgram { funcs, structs } = self;
        Ok(IrProgram {
            funcs: funcs.into_iter().map(fun).collect::<Result<Vec<_>>>()?,
            structs,
        })
    }
}

fn connect_bbs(
    arena: &mut Arena<BasicBlock>,
    source_id: &Id<BasicBlock>,
    dest_id: &Id<BasicBlock>,
) {
    let source = arena.get_mut(*source_id).unwrap();
    source.destination_bbs.insert(*dest_id);

    let dest = arena.get_mut(*dest_id).unwrap();
    dest.source_bbs.insert(*source_id);
}

pub fn build_connections_between_bbs(arena: &mut Arena<BasicBlock>, funcs: &[Function]) {
    for func in funcs {
        // Connect consecutive basic blocks
        for (forward_id, back_id) in func.basic_blocks.iter().tuple_windows() {
            let forward_bb = arena.get(*forward_id).unwrap();
            let is_terminal = forward_bb
                .insts
                .last()
                .map_or(false, |inst| inst.inst.is_terminal());

            if !is_terminal {
                connect_bbs(arena, forward_id, back_id);
            }
        }

        // Connect non-consecutive (e.g. jump) basic blocks
        for curr_id in &func.basic_blocks {
            let curr_bb = arena.get(*curr_id).unwrap();

            let insts = curr_bb.insts.clone();
            for inst in insts {
                match &inst.inst {
                    i::Instruction::Branch {
                        then_bb: then_id,
                        else_bb: else_id,
                        ..
                    } => {
                        connect_bbs(arena, curr_id, then_id);
                        connect_bbs(arena, curr_id, else_id);
                    }
                    i::Instruction::Jump(_, dest_id) => connect_bbs(arena, curr_id, dest_id),
                    _ => {}
                }
            }
        }
    }
}

pub fn dump_functions<P>(arena: &mut Arena<BasicBlock>, funcs: &[Function], path: P) -> Result<()>
where
    P: AsRef<Path>,
{
    let mut out = File::create(path)?;

    for func in funcs {
        writeln!(out, "# {}", func.name)?;

        let contents = func.display(false, arena).to_string();
        writeln!(out, "{}", contents)?;
    }

    Ok(())
}

pub fn dump_functions_as_dot<P>(
    arena: &mut Arena<BasicBlock>,
    funcs: &[Function],
    path: P,
) -> Result<()>
where
    P: AsRef<Path>,
{
    let mut out = File::create(path)?;

    writeln!(
        out,
        "digraph cfg {{
    node [shape=box, nojustify=true]"
    )?;

    for func in funcs {
        let mut que = VecDeque::new();

        for bb_id in &func.basic_blocks {
            let bb = arena.get(*bb_id).unwrap();
            let insts = bb
                .insts
                .iter()
                .map(|inst| inst.display(false).to_string())
                .join("\\l");
            writeln!(
                out,
                "    {} [label=\"{}:\\l{}\\l\"]",
                bb.label, bb.label, insts
            )?;
        }

        if let Some(bb) = func.basic_blocks.first() {
            que.push_back(bb);
        }

        let mut visited_bbs = FxHashSet::default();

        while let Some(bb) = que.pop_back() {
            if visited_bbs.contains(bb) {
                continue;
            }
            visited_bbs.insert(bb);

            let bb = arena.get(*bb).unwrap();

            for dbb in &bb.destination_bbs {
                que.push_back(dbb);

                let dbb = arena.get(*dbb).unwrap();

                writeln!(out, "    {} -> {};", bb.label, dbb.label)?;
            }
        }
    }

    writeln!(out, "}}")?;

    Ok(())
}
