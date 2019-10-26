//! **(internal)** BDD nodes represent individual vertices of the BDD directed acyclic graph.
//!
//! A BDD node can be a terminal, in which case it is either `0` or `1`, or a decision node,
//! in which case it contains a variable $v_i$ which it conditions upon and two pointers
//! (`low` and `high`) to other nodes in the same BDD:
//!
//! ```mermaid
//! graph LR
//!     id1($v_i$)
//!     id2($v_j$)
//!     id3($v_k$)
//!     id1 -->|low| id2
//!     id1 -->|high| id3
//! ```
//!
//! Internally, we represent terminal nodes using the same structure, giving them cyclic
//! pointers. Instead of variable id, we use the number of variables in the BDD universe.
//! This is consistent with the fact that we first condition on smallest variable ids.
//! It can be also used for consistency checks inside the library.

use crate::BddVariable;
use crate::bdd_pointer::BddPointer;

/// BDD nodes represent individual vertices of the BDD directed acyclic graph.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct BddNode {
    pub var: BddVariable,
    pub low_link: BddPointer,
    pub high_link: BddPointer
}

impl BddNode {


    /// Make a new terminal `zero` node.
    pub fn mk_zero(num_vars: u16) -> BddNode {
        return BddNode {
            var: BddVariable(num_vars),
            low_link: BddPointer::zero(),
            high_link: BddPointer::zero()
        }
    }

    /// Make a new terminal `one` node.
    pub fn mk_one(num_vars: u16) -> BddNode {
        return BddNode {
            var: BddVariable(num_vars),
            low_link: BddPointer::one(),
            high_link: BddPointer::one()
        }
    }

    /// Make a new general node.
    ///
    /// *Assumptions:*
    ///  - `low` and `high` are pointers in the same BDD array.
    ///  - Returned node is added to the same BDD where `low` and `high` are pointers.
    pub fn mk_node(var: BddVariable, low_link: BddPointer, high_link: BddPointer) -> BddNode {
        return BddNode { var, low_link, high_link }
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    /// Some basic methods used for testing.
    impl BddNode {

        /// Check whether this node is *effectively* terminal.
        ///
        /// *Warning:* This does not mean the node is necessarily terminal, it might also just
        /// point to a terminal node, effectively gaining its value. However, this should not
        /// happen in minimized BDDs.
        pub fn is_terminal(&self) -> bool {
            return self.low_link == self.high_link && (self.low_link.is_one() || self.low_link.is_zero())
        }

        /// Check whether this node is *effectively* one.
        pub fn is_one(&self) -> bool {
            return self.is_terminal() && self.low_link.is_one()
        }

        /// Check whether this node is *effectively* zero.
        pub fn is_zero(&self) -> bool {
            return self.is_terminal() && self.low_link.is_zero()
        }

    }

    #[test]
    fn bdd_node_one() {
        let one = BddNode::mk_one(2);
        assert!(one.is_terminal());
        assert!(one.is_one());
        assert!(!one.is_zero());
        assert_eq!(BddVariable(2), one.var);
    }

    #[test]
    fn bdd_node_zero() {
        let zero = BddNode::mk_zero(2);
        assert!(zero.is_terminal());
        assert!(zero.is_zero());
        assert!(!zero.is_one());
        assert_eq!(BddVariable(2), zero.var);
    }

    #[test]
    fn bdd_node_create() {
        let node = BddNode::mk_node(
            BddVariable(4),
            BddPointer(16), BddPointer::zero()
        );
        assert_eq!(BddPointer(16), node.low_link);
        assert_eq!(BddPointer::zero(), node.high_link);
        assert_eq!(BddVariable(4), node.var);
        assert!(!node.is_terminal());
        assert!(!node.is_one());
        assert!(!node.is_zero());
    }

}