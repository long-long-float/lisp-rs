use std::fmt::Display;

use anyhow::Result;
use id_arena::Id;
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    bug,
    lispi::{
        cli_option::CliOption,
        error::Error,
        ir::{
            basic_block::{BasicBlock, Function, IrProgram},
            instruction::{AnnotatedInstr, Instruction, Variable},
            IrContext,
        },
        ty,
        unique_generator::UniqueGenerator,
    },
};

use super::tag::Tag;

pub type RegisterMap = FxHashMap<Variable, usize>;

/// ID in Interference Graph
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
struct Igid(usize);

impl Igid {
    fn value(&self) -> usize {
        self.0
    }
}

impl From<usize> for Igid {
    fn from(value: usize) -> Self {
        Igid(value)
    }
}

#[derive(Default)]
/// Undirected graph for interference analyzation.
struct InterferenceGraph {
    vars: FxHashMap<Variable, Igid>,

    /// Adjacency list
    nodes: Vec<FxHashSet<Igid>>,
}

impl InterferenceGraph {
    fn add_node(&mut self, var: &Variable) -> Igid {
        if let Some(id) = self.vars.get(var) {
            *id
        } else {
            let id = self.nodes.len().into();
            self.vars.insert(var.to_owned(), id);

            self.nodes.push(FxHashSet::default());

            id
        }
    }

    /// Add an edge between node1 and node2.
    /// If node1 or node2 don't exist, they will be created.
    fn connect(&mut self, node1: &Variable, node2: &Variable) {
        let node1 = self.get_id_or_add_node(node1);
        let node2 = self.get_id_or_add_node(node2);

        if node1 == node2 {
            return;
        }

        self.nodes[node1.value()].insert(node2);
        self.nodes[node2.value()].insert(node1);
    }

    /// Remove var node and edges from/to var.
    fn remove(&mut self, var: &Variable) {
        if let Some(&id) = self.get_id(var) {
            self.nodes[id.value()].clear();
            for node in &mut self.nodes {
                node.remove(&id);
            }

            self.vars.remove(var);
        }
    }

    fn get_id_or_add_node(&mut self, var: &Variable) -> Igid {
        if let Some(id) = self.get_id(var) {
            *id
        } else {
            self.add_node(var)
        }
    }

    fn get_id(&self, var: &Variable) -> Option<&Igid> {
        self.vars.get(var)
    }

    fn get_var(&self, id: Igid) -> Option<&Variable> {
        self.vars
            .iter()
            .find_map(|(var, iid)| if *iid == id { Some(var) } else { None })
    }

    fn get_connected_vars(&self, var: &Variable) -> Vec<Igid> {
        if let Some(&id) = self.get_id(var) {
            self.nodes[id.value()]
                .iter()
                .map(|id| id.to_owned())
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        }
    }

    #[allow(dead_code)]
    fn exists(&self, var: &Variable) -> bool {
        self.vars.contains_key(var)
    }

    #[allow(dead_code)]
    fn is_connected_to(&self, src: &Variable, dest: &Variable) -> bool {
        if let (Some(&src), Some(dest)) = (self.get_id(src), self.get_id(dest)) {
            self.nodes[src.value()].contains(dest)
        } else {
            false
        }
    }
}

impl Display for InterferenceGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (id, connected) in self.nodes.iter().enumerate() {
            let var = self.get_var(id.into()).unwrap();
            write!(f, "{} -> ", var.name)?;

            let connected = connected
                .iter()
                .map(|id| {
                    let other = self.get_var(*id).unwrap();
                    other.name.clone()
                })
                .join(", ");
            writeln!(f, "{}", connected)?;
        }

        Ok(())
    }
}

type VariableSet<'a> = FxHashSet<&'a Variable>;
type AllInOuts<'a> = FxHashMap<Id<BasicBlock>, Vec<(VariableSet<'a>, VariableSet<'a>)>>;

fn print_var_set(var_set: &FxHashSet<&Variable>) {
    print!("  {{");
    for v in var_set {
        print!("{}, ", v);
    }
    println!("}}, ");
}

fn calculate_lifetime<'a>(func: &Function, ir_ctx: &'a IrContext) -> AllInOuts<'a> {
    let mut def_uses = FxHashMap::default();

    let mut exclude_vars = Vec::new();

    // Scan DontAllocateRegister
    for bb_id in &func.basic_blocks {
        let bb = ir_ctx.bb_arena.get(*bb_id).unwrap();

        for annot_inst in &bb.insts {
            if annot_inst.has_tag(Tag::DontAllocateRegister) {
                exclude_vars.push(&annot_inst.result);
            }
        }
    }

    for bb_id in &func.basic_blocks {
        let bb = ir_ctx.bb_arena.get(*bb_id).unwrap();

        let mut def_uses_bb = Vec::new();

        for annot_inst in &bb.insts {
            let used_vars = annot_inst.inst.collect_vars();
            // get_vars(&annot_inst.inst, &mut used_vars);
            let used_vars = used_vars
                .into_iter()
                .filter(|uv| !exclude_vars.iter().any(|v| v == uv))
                .collect_vec();

            let mut def_vars = FxHashSet::default();
            // if !annot_inst.inst.is_terminal() {
            if annot_inst.has_result() {
                def_vars.insert(&annot_inst.result);
            };

            println!("{}", annot_inst.display(true));
            print_var_set(&def_vars);
            println!();

            def_uses_bb.push((def_vars, FxHashSet::from_iter(used_vars.into_iter())));
        }

        def_uses.insert(*bb_id, def_uses_bb);
    }

    // To make this immutable
    let def_uses = def_uses;

    let mut prev_all_in_outs = FxHashMap::default();
    let mut all_in_outs_result = FxHashMap::default();

    let mut all_in_outs: FxHashMap<Id<BasicBlock>, Vec<_>> = FxHashMap::default();

    let mut prev_in_vars = FxHashSet::default();

    for _ in 0..10 {
        let mut def_uses = def_uses.clone();

        for bb_id in func.basic_blocks.iter().rev() {
            let bb = ir_ctx.bb_arena.get(*bb_id).unwrap();

            let mut def_uses_bb = def_uses.remove(bb_id).unwrap();

            let mut in_outs = Vec::new();

            for i in 0..bb.insts.len() {
                let (defs, uses) = def_uses_bb.pop().unwrap();

                let is_last_inst = i == 0;
                let mut out_vars = FxHashSet::default();
                if is_last_inst {
                    for dest_bb in &bb.destination_bbs {
                        if let Some(in_outs) = all_in_outs.get(dest_bb) {
                            if let Some((inn, _)) = in_outs.first() {
                                for v in inn {
                                    let v: &&Variable = v;
                                    out_vars.insert(*v);
                                }
                            }
                        }
                    }
                } else {
                    out_vars = FxHashSet::from_iter(prev_in_vars.drain());
                }

                let uses = FxHashSet::from_iter(uses.into_iter());
                let diff = FxHashSet::from_iter(out_vars.difference(&defs).copied());
                let in_vars = FxHashSet::from_iter(uses.union(&diff).copied());

                prev_in_vars = in_vars.clone();

                println!("{}", bb.insts[bb.insts.len() - 1 - i].display(true));
                print_var_set(&in_vars);
                print_var_set(&out_vars);
                print_var_set(&defs);
                print_var_set(&uses);
                println!();

                in_outs.push((in_vars, out_vars));
            }

            in_outs.reverse();
            all_in_outs.insert(*bb_id, in_outs);
        }

        if all_in_outs == prev_all_in_outs {
            all_in_outs_result = all_in_outs;
            break;
        }

        prev_all_in_outs = FxHashMap::from_iter(all_in_outs.clone());
    }

    all_in_outs_result
}

fn build_inference_graph(
    func: &Function,
    all_in_outs: &AllInOuts,
    ir_ctx: &IrContext,
) -> InterferenceGraph {
    let mut inter_graph = InterferenceGraph::default();

    for bb_id in &func.basic_blocks {
        let bb = ir_ctx.bb_arena.get(*bb_id).unwrap();

        for curr_inst_idx in 0..bb.insts.len() {
            if curr_inst_idx < bb.insts.len() - 1 {
                // In this case, "out" of curr-inst and "in" of next-inst are self-evidently equal.
                let in_outs = all_in_outs.get(bb_id).unwrap();
                let (ins, outs) = &in_outs[curr_inst_idx];

                fn in_args(func: &Function, var: &Variable) -> bool {
                    func.args.iter().any(|(name, _)| &var.name == name)
                }

                for v in ins {
                    if in_args(func, v) {
                        continue;
                    }
                    inter_graph.add_node(v);
                }

                for v in outs {
                    if in_args(func, v) {
                        continue;
                    }
                    inter_graph.add_node(v);
                }

                for (a, b) in ins.iter().tuple_combinations() {
                    if in_args(func, a) || in_args(func, b) {
                        continue;
                    }
                    inter_graph.connect(a, b);
                }

                for (a, b) in outs.iter().tuple_combinations() {
                    if in_args(func, a) || in_args(func, b) {
                        continue;
                    }
                    inter_graph.connect(a, b);
                }
            } else {
                // Take from next bb
                for dest_bb in &bb.destination_bbs {
                    let _dest_bb = ir_ctx.bb_arena.get(*dest_bb).unwrap();
                }
            }
        }
    }

    inter_graph
}

fn spill_variable(spilled_var: &Variable, fun: &Function, ir_ctx: &mut IrContext) {
    let ptr_var = Variable {
        name: format!("{}-ptr", spilled_var.name),
    };
    let mut gen = UniqueGenerator::default();

    let mut already_spilled = false;

    for bb in fun.basic_blocks.iter() {
        let mut result = Vec::new();

        let bb = ir_ctx.bb_arena.get_mut(*bb).unwrap();

        for AnnotatedInstr {
            result: var,
            inst,
            ty,
            tags,
        } in bb.insts.clone().into_iter()
        {
            let mut replace_var_map = FxHashMap::default();
            // TODO: Allocate the globally unique name.
            let new_var = Variable {
                name: format!("{}-{}", spilled_var.name, gen.gen()),
            };
            replace_var_map.insert(spilled_var.clone(), new_var.clone());
            let replaced_inst = inst.clone().replace_var(&replace_var_map);
            if replaced_inst != inst {
                result.push(AnnotatedInstr::new(
                    new_var,
                    Instruction::LoadElement {
                        addr: ptr_var.clone().into(),
                        // TODO: Adjust type
                        ty: ty::Type::Int,
                        index: 0.into(),
                    },
                    ty::Type::Int,
                ));
            }
            result.push(AnnotatedInstr::new(var.clone(), replaced_inst, ty).with_tags(tags));

            if &var == spilled_var {
                if !already_spilled {
                    result.push(
                        AnnotatedInstr::new(
                            ptr_var.clone(),
                            Instruction::Alloca {
                                // TODO: Adjust type
                                ty: ty::Type::Int,
                                count: 4.into(),
                            },
                            ty::Type::Reference(Box::new(ty::Type::Int)),
                        )
                        .with_tags(vec![Tag::DontAllocateRegister]),
                    );

                    already_spilled = true;
                }

                result.push(AnnotatedInstr::new(
                    Variable::empty(),
                    Instruction::StoreElement {
                        addr: ptr_var.clone().into(),
                        // TODO: Adjust type
                        ty: ty::Type::Int,
                        index: 0.into(),
                        value: spilled_var.clone().into(),
                    },
                    ty::Type::Void,
                ));
            }
        }

        bb.insts = result;
    }
}

/// Order is the second vector of the result is the same as `InProgram.funcs`.
pub fn create_interference_graph(
    program: IrProgram,
    ir_ctx: &mut IrContext,
    _opt: &CliOption,
) -> Result<(IrProgram, Vec<RegisterMap>)> {
    // TODO: Take the number from outside
    let num_of_registers = 7;

    let mut register_maps = Vec::new();

    let program = program.map_fun(|func| {
        for _ in 0..3 {
            let all_in_outs = calculate_lifetime(&func, ir_ctx);

            let mut inter_graph = build_inference_graph(&func, &all_in_outs, ir_ctx);

            println!("{}", inter_graph);

            let vars = inter_graph.vars.clone();

            // A vector of (IGID, connected IGIDs).
            let mut removed_vars = Vec::new();
            let mut spill_list = Vec::new();

            for (var, id) in &vars {
                let connected_var = inter_graph.get_connected_vars(var);

                let register_pressure = connected_var.len();
                if register_pressure < num_of_registers {
                    removed_vars.push((id, connected_var));
                } else {
                    spill_list.push(var);
                }
                inter_graph.remove(var);
            }

            if spill_list.is_empty() {
                // A mapping for IGID and register ID.
                let mut allocation_map = FxHashMap::default();

                for (&var, others) in removed_vars.iter().rev() {
                    let mut allocated = [false].repeat(num_of_registers);
                    for other in others {
                        if let Some(&reg_id) = allocation_map.get(other) {
                            allocated[reg_id] = true;
                        }
                    }

                    let reg_id = allocated
                        .iter()
                        .enumerate()
                        .find(|(_, &alloc)| !alloc)
                        .map(|(id, _)| id);

                    if let Some(reg_id) = reg_id {
                        allocation_map.insert(var, reg_id);
                    } else {
                        return Err(bug!("Register cannot be allocated!"));
                    }
                }

                let mut result = FxHashMap::default();

                for (var, reg) in allocation_map {
                    let (var, _) = vars.iter().find(|(_, &id)| id == var).unwrap();
                    result.insert(var.to_owned(), reg);
                }

                register_maps.push(result);

                return Ok(func);
            } else {
                println!("{:#?}", spill_list);
                for sv in spill_list {
                    spill_variable(sv, &func, ir_ctx);
                }
                func.dump(&ir_ctx.bb_arena);
                println!();
            }
        }

        Err(Error::CompileError("Cannot allocate registers".to_string()).into())
    })?;

    Ok((program, register_maps))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interference_graph() {
        let mut graph = InterferenceGraph::default();
        let vars = (0..5)
            .map(|i| Variable {
                name: format!("var{}", i),
            })
            .collect::<Vec<_>>();

        graph.connect(&vars[0], &vars[1]);
        assert!(!graph.is_connected_to(&vars[0], &vars[0]));
        assert!(graph.is_connected_to(&vars[0], &vars[1]));
        assert!(graph.is_connected_to(&vars[1], &vars[0]));
        assert!(!graph.is_connected_to(&vars[0], &vars[2]));
        assert_eq!(2, graph.vars.len());

        graph.remove(&vars[0]);
        assert!(!graph.is_connected_to(&vars[0], &vars[1]));
        assert!(!graph.is_connected_to(&vars[1], &vars[0]));
        assert!(!graph.exists(&vars[0]));
        assert!(graph.exists(&vars[1]));
        assert_eq!(1, graph.vars.len());

        graph.connect(&vars[0], &vars[1]);
        graph.connect(&vars[1], &vars[2]);
        graph.connect(&vars[2], &vars[0]);
        assert_eq!(3, graph.vars.len());
        graph.remove(&vars[0]);
        assert!(!graph.is_connected_to(&vars[1], &vars[0]));
        assert!(!graph.is_connected_to(&vars[2], &vars[0]));
        assert_eq!(2, graph.vars.len());
    }
}
