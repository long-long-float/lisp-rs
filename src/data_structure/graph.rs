use std::fmt::Display;

use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};

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

pub struct DirectedGraph<T> {
    pub vars: FxHashMap<T, Igid>,

    /// Adjacency list
    nodes: Vec<FxHashSet<Igid>>,
}

impl<T> DirectedGraph<T>
where
    T: Eq + PartialEq + Clone + std::hash::Hash,
{
    pub fn add_node(&mut self, var: &T) -> Igid {
        if let Some(id) = self.vars.get(var) {
            *id
        } else {
            let id = self.nodes.len().into();
            self.vars.insert(var.clone(), id);

            self.nodes.push(FxHashSet::default());

            id
        }
    }

    /// Add an edge from src to dest.
    /// If src or dest don't exist, they will be created.
    pub fn connect(&mut self, src: &T, dest: &T) {
        let src = self.get_id_or_add_node(src);
        let dest = self.get_id_or_add_node(dest);

        if src == dest {
            return;
        }

        self.nodes[src.value()].insert(dest);
    }

    /// Remove var node and edges from/to var.
    pub fn remove(&mut self, var: &T) {
        if let Some(&id) = self.get_id(var) {
            self.nodes[id.value()].clear();
            for node in &mut self.nodes {
                node.remove(&id);
            }

            self.vars.remove(var);
        }
    }

    pub fn values(&self) -> FxHashMap<T, Igid> {
        self.vars.clone()
    }

    fn get_id_or_add_node(&mut self, var: &T) -> Igid {
        if let Some(id) = self.get_id(var) {
            *id
        } else {
            self.add_node(var)
        }
    }

    fn get_id(&self, var: &T) -> Option<&Igid> {
        self.vars.get(var)
    }

    fn get_var(&self, id: Igid) -> Option<&T> {
        self.vars
            .iter()
            .find_map(|(var, iid)| if *iid == id { Some(var) } else { None })
    }

    pub fn get_connected_vars(&self, var: &T) -> Vec<Igid> {
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
    fn exists(&self, var: &T) -> bool {
        self.vars.contains_key(var)
    }

    #[allow(dead_code)]
    fn is_connected_to(&self, src: &T, dest: &T) -> bool {
        if let (Some(&src), Some(dest)) = (self.get_id(src), self.get_id(dest)) {
            self.nodes[src.value()].contains(dest)
        } else {
            false
        }
    }
}

impl<T> Default for DirectedGraph<T> {
    fn default() -> Self {
        Self {
            vars: FxHashMap::default(),
            nodes: Vec::default(),
        }
    }
}

impl<T> Display for DirectedGraph<T>
where
    T: Eq + PartialEq + Display + Clone + std::hash::Hash,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (id, connected) in self.nodes.iter().enumerate() {
            let var = self.get_var(id.into()).unwrap();
            write!(f, "{} -> ", var)?;

            let connected = connected
                .iter()
                .map(|id| self.get_var(*id).unwrap().to_string())
                .join(", ");
            writeln!(f, "{}", connected)?;
        }

        Ok(())
    }
}

pub struct UndirectedGraph<T> {
    directed_graph: DirectedGraph<T>,
}

impl<T> UndirectedGraph<T>
where
    T: Eq + PartialEq + Clone + std::hash::Hash,
{
    pub fn add_node(&mut self, var: &T) -> Igid {
        self.directed_graph.add_node(var)
    }

    /// Add an edge between node1 and node2.
    /// If node1 or node2 don't exist, they will be created.
    pub fn connect(&mut self, node1: &T, node2: &T) {
        self.directed_graph.connect(node1, node2);
        self.directed_graph.connect(node2, node1);
    }

    /// Remove var node and edges from/to var.
    pub fn remove(&mut self, var: &T) {
        self.directed_graph.remove(var)
    }

    pub fn values(&self) -> FxHashMap<T, Igid> {
        self.directed_graph.values()
    }

    pub fn get_connected_vars(&self, var: &T) -> Vec<Igid> {
        self.directed_graph.get_connected_vars(var)
    }

    #[allow(dead_code)]
    fn exists(&self, var: &T) -> bool {
        self.directed_graph.exists(var)
    }

    #[allow(dead_code)]
    fn is_connected_to(&self, src: &T, dest: &T) -> bool {
        self.directed_graph.is_connected_to(src, dest)
    }
}

impl<T> Default for UndirectedGraph<T> {
    fn default() -> Self {
        Self {
            directed_graph: DirectedGraph::default(),
        }
    }
}

impl<T> Display for UndirectedGraph<T>
where
    T: Eq + PartialEq + Display + Clone + std::hash::Hash,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.directed_graph.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use crate::lispi::ir::instruction::Variable;

    use super::*;

    #[test]
    fn directed_graph_test() {
        let mut graph = DirectedGraph::default();
        let vars = (0..5)
            .map(|i| Variable {
                name: format!("var{}", i),
            })
            .collect::<Vec<_>>();

        graph.connect(&vars[0], &vars[1]);
        assert!(!graph.is_connected_to(&vars[0], &vars[0]));
        assert!(graph.is_connected_to(&vars[0], &vars[1]));
        assert!(!graph.is_connected_to(&vars[1], &vars[0]));
        assert!(!graph.is_connected_to(&vars[0], &vars[2]));
        assert_eq!(2, graph.values().len());

        graph.remove(&vars[0]);
        assert!(!graph.is_connected_to(&vars[0], &vars[1]));
        assert!(!graph.is_connected_to(&vars[1], &vars[0]));
        assert!(!graph.exists(&vars[0]));
        assert!(graph.exists(&vars[1]));
        assert_eq!(1, graph.values().len());

        graph.connect(&vars[0], &vars[1]);
        graph.connect(&vars[1], &vars[2]);
        graph.connect(&vars[2], &vars[0]);
        assert_eq!(3, graph.values().len());
        graph.remove(&vars[0]);
        assert!(!graph.is_connected_to(&vars[1], &vars[0]));
        assert!(!graph.is_connected_to(&vars[2], &vars[0]));
        assert_eq!(2, graph.values().len());
    }

    #[test]
    fn undirected_graph_test() {
        let mut graph = UndirectedGraph::default();
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
        assert_eq!(2, graph.values().len());

        graph.remove(&vars[0]);
        assert!(!graph.is_connected_to(&vars[0], &vars[1]));
        assert!(!graph.is_connected_to(&vars[1], &vars[0]));
        assert!(!graph.exists(&vars[0]));
        assert!(graph.exists(&vars[1]));
        assert_eq!(1, graph.values().len());

        graph.connect(&vars[0], &vars[1]);
        graph.connect(&vars[1], &vars[2]);
        graph.connect(&vars[2], &vars[0]);
        assert_eq!(3, graph.values().len());
        graph.remove(&vars[0]);
        assert!(!graph.is_connected_to(&vars[1], &vars[0]));
        assert!(!graph.is_connected_to(&vars[2], &vars[0]));
        assert_eq!(2, graph.values().len());
    }
}
