use std::sync::Arc;

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

    fn exists(&self, var: &Variable) -> bool {
        self.vars.contains_key(var)
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