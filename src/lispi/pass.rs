use std::collections::HashSet;

pub mod constant_folding;
pub mod context_folding;
pub mod immediate_unfolding;
pub mod placing_on_memory;
pub mod removing_duplicated_assignments;
pub mod removing_redundant_assignments;
pub mod removing_ref_and_deref;
pub mod removing_uncalled_functions;
pub mod tail_recursion;

#[derive(Eq, PartialEq, Hash)]
pub enum Optimize {
    ConstantFolding,
    ImmediateUnfolding,
    RemovingRedundantAssignments,
    TailRecursion,
}

impl Optimize {
    pub fn all() -> HashSet<Optimize> {
        use Optimize::*;
        HashSet::from([
            ConstantFolding,
            ImmediateUnfolding,
            RemovingRedundantAssignments,
            TailRecursion,
        ])
    }

    pub fn minimum() -> HashSet<Optimize> {
        use Optimize::*;
        HashSet::from([ImmediateUnfolding, TailRecursion])
    }
}
