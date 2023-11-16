use std::fmt::Display;

use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::lispi::ir::instruction::Variable;

/// ID in Interference Graph
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Igid(usize);

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
pub struct InterferenceGraph {
    pub vars: FxHashMap<Variable, Igid>,

    /// Adjacency list
    nodes: Vec<FxHashSet<Igid>>,
}

impl InterferenceGraph {
    pub fn add_node(&mut self, var: &Variable) -> Igid {
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
    pub fn connect(&mut self, node1: &Variable, node2: &Variable) {
        let node1 = self.get_id_or_add_node(node1);
        let node2 = self.get_id_or_add_node(node2);

        if node1 == node2 {
            return;
        }

        self.nodes[node1.value()].insert(node2);
        self.nodes[node2.value()].insert(node1);
    }

    /// Remove var node and edges from/to var.
    pub fn remove(&mut self, var: &Variable) {
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

    pub fn get_connected_vars(&self, var: &Variable) -> Vec<Igid> {
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
