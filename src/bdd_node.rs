use crate::bdd_pointer::BddPointer;
use crate::BddVariable;

/// BDD nodes represent individual vertices of the BDD directed acyclic graph.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct BddNode {
    pub var: BddVariable,
    pub low_link: BddPointer,
    pub high_link: BddPointer,
}

impl BddNode {
    /// Make a new terminal `zero` node.
    pub fn mk_zero(num_vars: u16) -> BddNode {
        return BddNode {
            var: BddVariable(num_vars),
            low_link: BddPointer::zero(),
            high_link: BddPointer::zero(),
        };
    }

    /// Make a new terminal `one` node.
    pub fn mk_one(num_vars: u16) -> BddNode {
        return BddNode {
            var: BddVariable(num_vars),
            low_link: BddPointer::one(),
            high_link: BddPointer::one(),
        };
    }

    /// Make a new general node.
    ///
    /// *Assumptions:*
    ///  - `low` and `high` are pointers in the same BDD array.
    ///  - Returned node is added to the same BDD where `low` and `high` are pointers.
    pub fn mk_node(var: BddVariable, low_link: BddPointer, high_link: BddPointer) -> BddNode {
        return BddNode {
            var,
            low_link,
            high_link,
        };
    }
}
