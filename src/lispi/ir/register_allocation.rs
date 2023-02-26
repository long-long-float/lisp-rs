use rustc_hash::{FxHashMap, FxHashSet};

use crate::lispi::ir::instruction::Operand;

use super::{
    instruction::{Functions, Instruction, Variable},
    IrContext,
};

type IGID = usize;

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
            let id = self.nodes.len();
            self.vars.insert(var.to_owned(), id);

            self.nodes.push(FxHashSet::default());

            id
        }
    }

    /// Add an edge between node1 and node2.
    fn connect(&mut self, node1: &Variable, node2: &Variable) {
        let node1 = self.get_id_or_add_node(node1);
        let node2 = self.get_id_or_add_node(node2);

        self.nodes[node1].insert(node2);
        self.nodes[node2].insert(node1);
    }

    /// Remove edges from/to var. This doesn't remove node itself.
    fn remove(&mut self, var: &Variable) {
        if let Some(&id) = self.get_id(var) {
            self.nodes[id].clear();
            for node in &mut self.nodes {
                node.remove(&id);
            }
        }
    }

    fn get_id_or_add_node(&mut self, var: &Variable) -> IGID {
        if let Some(id) = self.get_id(var) {
            *id
        } else {
            self.add_node(var)
        }
    }

    fn get_id(&mut self, var: &Variable) -> Option<&IGID> {
        self.vars.get(var)
    }

    fn is_connected_to(&mut self, src: &Variable, dest: &Variable) -> bool {
        let src = self.get_id_or_add_node(src);
        let dest = self.get_id_or_add_node(dest);

        self.nodes[src].contains(&dest)
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

pub fn create_interference_graph(funcs: &Functions, ir_ctx: &mut IrContext) {
    for func in funcs {
        let mut living_vars = FxHashSet::default();

        let mut inter_graph = InterferenceGraph::default();

        for bb in func.basic_blocks.iter().rev() {
            let bb = ir_ctx.bb_arena.get(*bb).unwrap();

            for annot_inst in bb.insts.iter().rev() {
                let mut used_vars = Vec::new();
                get_vars(&annot_inst.inst, &mut used_vars);

                for var in used_vars {
                    living_vars.insert(var);

                    inter_graph.add_node(var);
                }

                for lvar1 in &living_vars {
                    for lvar2 in &living_vars {
                        inter_graph.connect(lvar1, lvar2);
                    }
                }

                let result_var = &annot_inst.result;
                living_vars.remove(result_var);
                inter_graph.remove(result_var);
            }
        }
    }
}

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

        for v in &vars {
            graph.add_node(v);
        }

        graph.connect(&vars[0], &vars[1]);
        assert!(!graph.is_connected_to(&vars[0], &vars[0]));
        assert!(graph.is_connected_to(&vars[0], &vars[1]));
        assert!(graph.is_connected_to(&vars[1], &vars[0]));
        assert!(!graph.is_connected_to(&vars[0], &vars[2]));

        graph.remove(&vars[0]);
        assert!(!graph.is_connected_to(&vars[0], &vars[1]));
        assert!(!graph.is_connected_to(&vars[1], &vars[0]));

        graph.connect(&vars[0], &vars[1]);
        graph.connect(&vars[1], &vars[2]);
        graph.connect(&vars[2], &vars[0]);
        graph.remove(&vars[0]);
        assert!(!graph.is_connected_to(&vars[1], &vars[0]));
        assert!(!graph.is_connected_to(&vars[2], &vars[0]));
    }
}
