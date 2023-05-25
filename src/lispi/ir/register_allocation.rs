use anyhow::Result;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{bug, lispi::ir::instruction::Operand};

use super::{
    super::error::Error,
    instruction::{Function, Functions, Instruction, Variable},
    IrContext,
};

pub type RegisterMap = FxHashMap<Variable, usize>;

/// ID in Interference Graph
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
struct IGID {
    value: usize,
}

impl IGID {
    fn new(value: usize) -> Self {
        IGID { value }
    }
}

impl From<usize> for IGID {
    fn from(value: usize) -> Self {
        IGID::new(value)
    }
}

#[derive(Default)]
/// Undirected graph for interference analyzation.
struct InterferenceGraph {
    vars: FxHashMap<Variable, IGID>,

    /// Adjacency list
    nodes: Vec<FxHashSet<IGID>>,
}

impl InterferenceGraph {
    fn add_node(&mut self, var: &Variable) -> IGID {
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
    fn connect(&mut self, node1: &Variable, node2: &Variable) {
        let node1 = self.get_id_or_add_node(node1);
        let node2 = self.get_id_or_add_node(node2);

        if node1 == node2 {
            return;
        }

        self.nodes[node1.value].insert(node2);
        self.nodes[node2.value].insert(node1);
    }

    /// Remove var node and edges from/to var.
    fn remove(&mut self, var: &Variable) {
        if let Some(&id) = self.get_id(var) {
            self.nodes[id.value].clear();
            for node in &mut self.nodes {
                node.remove(&id);
            }

            self.vars.remove(var);
        }
    }

    fn get_id_or_add_node(&mut self, var: &Variable) -> IGID {
        if let Some(id) = self.get_id(var) {
            *id
        } else {
            self.add_node(var)
        }
    }

    fn get_id(&self, var: &Variable) -> Option<&IGID> {
        self.vars.get(var)
    }

    fn get_connected_vars(&self, var: &Variable) -> Vec<IGID> {
        if let Some(&id) = self.get_id(var) {
            self.nodes[id.value]
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
            self.nodes[src.value].contains(dest)
        } else {
            false
        }
    }
}

fn get_vars<'a>(inst: &'a Instruction, vars: &mut Vec<&'a Variable>) {
    fn add_only_var<'a>(op: &'a Operand, vars: &mut Vec<&'a Variable>) {
        if let Operand::Variable(var) = op {
            vars.push(var);
        }
    }

    match inst {
        Instruction::Branch { cond, .. } => {
            add_only_var(cond, vars);
        }
        Instruction::Jump(_, _) => {}
        Instruction::Ret(op) => add_only_var(op, vars),
        Instruction::Add(left, right) => {
            add_only_var(left, vars);
            add_only_var(right, vars);
        }
        Instruction::Sub(left, right) => {
            add_only_var(left, vars);
            add_only_var(right, vars);
        }
        Instruction::Mul(left, right) => {
            add_only_var(left, vars);
            add_only_var(right, vars);
        }
        Instruction::Or(left, right) => {
            add_only_var(left, vars);
            add_only_var(right, vars);
        }
        Instruction::Not(op) => {
            add_only_var(op, vars);
        }
        Instruction::Shift(_, left, right) => {
            add_only_var(left, vars);
            add_only_var(right, vars);
        }
        Instruction::Store(addr, value) => {
            add_only_var(addr, vars);
            add_only_var(value, vars);
        }
        Instruction::Cmp(_, left, right) => {
            add_only_var(left, vars);
            add_only_var(right, vars);
        }
        Instruction::Call { fun, args } => {
            add_only_var(fun, vars);
            for arg in args {
                add_only_var(arg, vars);
            }
        }
        Instruction::Phi(nodes) => {
            for (op, _) in nodes {
                add_only_var(op, vars);
            }
        }
        Instruction::Operand(op) => add_only_var(op, vars),
        Instruction::Label(_) => {}
        Instruction::Nop => {}
    }
}

pub fn create_interference_graph(
    funcs: Functions,
    ir_ctx: &mut IrContext,
) -> Result<Vec<(Function, RegisterMap)>> {
    // TODO: Take the number from outside
    let num_of_registers = 7;

    funcs
        .into_iter()
        .map(|func| {
            // Calculate lifetime
            {
                let mut def_uses = FxHashMap::default();

                for bb_id in &func.basic_blocks {
                    let bb = ir_ctx.bb_arena.get(*bb_id).unwrap();

                    let mut def_uses_bb = Vec::new();

                    for annot_inst in &bb.insts {
                        let mut used_vars = Vec::new();
                        get_vars(&annot_inst.inst, &mut used_vars);

                        let mut def_vars = FxHashSet::default();
                        if !annot_inst.inst.is_terminal() {
                            def_vars.insert(&annot_inst.result);
                        };

                        def_uses_bb.push((def_vars, FxHashSet::from_iter(used_vars.into_iter())));
                    }

                    def_uses.insert(*bb_id, def_uses_bb);
                }

                // To make this immutable
                let def_uses = def_uses;

                let mut prev_all_in_outs = FxHashMap::default();
                let mut all_in_outs_result = FxHashMap::default();

                let mut all_in_outs = FxHashMap::default();

                for _ in 0..10 {
                    let mut def_uses = def_uses.clone();

                    for bb_id in func.basic_blocks.iter().rev() {
                        let bb = ir_ctx.bb_arena.get(*bb_id).unwrap();

                        let mut def_uses_bb = def_uses.remove(bb_id).unwrap();

                        for _ in 0..bb.insts.len() {
                            let (defs, uses) = def_uses_bb.pop().unwrap();

                            let mut out_vars = FxHashSet::default();
                            for dest_bb in &bb.destination_bbs {
                                if let Some((inn, _)) = all_in_outs.get(dest_bb) {
                                    for v in inn {
                                        let v: &&Variable = v;
                                        out_vars.insert(*v);
                                    }
                                }
                            }

                            let uses = FxHashSet::from_iter(uses.into_iter());
                            let diff = FxHashSet::from_iter(out_vars.difference(&defs).map(|v| *v));
                            let in_vars =
                                FxHashSet::from_iter(uses.union(&diff).into_iter().map(|v| *v));

                            all_in_outs.insert(bb_id, (in_vars, out_vars));
                        }
                    }

                    if all_in_outs == prev_all_in_outs {
                        all_in_outs_result = all_in_outs;
                        break;
                    }

                    prev_all_in_outs = FxHashMap::from_iter(all_in_outs.clone());
                }

                println!("{:#?}", all_in_outs_result);
            }

            let mut living_vars = FxHashSet::default();

            let mut inter_graph = InterferenceGraph::default();

            for bb in func.basic_blocks.iter().rev() {
                let bb = ir_ctx.bb_arena.get(*bb).unwrap();

                for annot_inst in bb.insts.iter().rev() {
                    let mut used_vars = Vec::new();
                    get_vars(&annot_inst.inst, &mut used_vars);

                    for var in used_vars {
                        let in_args = func.args.iter().any(|(name, _)| &var.name == name);
                        if in_args {
                            continue;
                        }

                        living_vars.insert(var);
                    }

                    for lvar1 in &living_vars {
                        for lvar2 in &living_vars {
                            inter_graph.connect(lvar1, lvar2);
                        }
                    }

                    let result_var = &annot_inst.result;
                    living_vars.remove(result_var);
                }
            }

            // A vector of (IGID, connected IGIDs).
            let mut removed_vars = Vec::new();

            let vars = inter_graph.vars.clone();

            for (var, id) in &vars {
                let connected_var = inter_graph.get_connected_vars(var);

                let register_pressure = connected_var.len();
                if register_pressure > num_of_registers {
                    return Err(bug!("Register spill is not implemented!"));
                }

                inter_graph.remove(var);

                removed_vars.push((id, connected_var));
            }

            // A mapping for IGID and register ID.
            let mut allocation_map = FxHashMap::default();

            for (&var, others) in removed_vars.iter().rev() {
                let mut allocated = vec![false].repeat(num_of_registers);
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

            Ok((func, result))
        })
        .collect::<Result<Vec<_>>>()
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
