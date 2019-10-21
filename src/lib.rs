//! TODO: Add crate documentation with description of BDDs
//! Define: Boolean variables, BDD universe.
//!
//! Describe BDD encoding inside an array.
//!
//! BDD variables are used instead of their respective indices to provide enhanced type
//! safety. They are also intentionally very opaque because we might need to change their internal
//! structure in the future. The same goes for BDD pointers - extra safety plus we can
//! swap implementations. Except you probably shouldn't use BDD pointers explicitly anyway.

use crate::bdd_node::BddNode;
use crate::bdd_pointer::BddPointer;

mod bdd_node;
mod bdd_pointer;

/// BDD variable identifies one of the variables in the associated BDD universe.
///
/// Usage example: TODO.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BddVariable(u16);

/// BDD object is an array-based encoding of the binary decision diagram.
///
/// Usage example: TODO.
pub struct Bdd(Vec<BddNode>);

impl Bdd {

    /// The number of nodes in this BDD. (Do not confuse with cardinality!)
    pub fn size(&self) -> usize {
        return self.0.len();
    }

    /// Pointer to the root of the decision diagram.
    pub fn root_pointer(&self) -> BddPointer {
        return BddPointer((self.0.len() - 1) as u32)
    }

    /// Number of variables in the corresponding BDD universe.
    pub fn num_vars(&self) -> u16 {
        return self.0[0].var.0;
    }

    /// Get low link of the node at a specified location.
    pub fn low_link_of(&self, node: &BddPointer) -> BddPointer {
        return self.0[node.0 as usize].low_link;
    }

    /// Get high link of the node at a specified location.
    pub fn high_link_of(&self, node: &BddPointer) -> BddPointer {
        return self.0[node.0 as usize].high_link;
    }

    /// **(internal)** Create a new BDD for the `false` formula.
    fn mk_false(num_vars: u16) -> Bdd {
        return Bdd(vec![BddNode::mk_zero(num_vars)]);
    }

    /// **(internal)** Create a new BDD for the `true` formula.
    fn mk_true(num_vars: u16) -> Bdd {
        return Bdd(vec![BddNode::mk_zero(num_vars), BddNode::mk_one(num_vars)]);
    }

    /// **(internal)** Add a new node to an existing BDD, making the new node the root of the BDD.
    fn push_node(&mut self, node: BddNode) {
        self.0.push(node);
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    /// A small BDD over variables x_0, x_1, x_2, x_3, x_4 corresponding to the formula $(x_4 \land \neg x_3)$
    fn mk_small_test_bdd() -> Bdd {
        let mut bdd = Bdd::mk_true(5);
        bdd.push_node(BddNode::mk_node(BddVariable(3),
            BddPointer::one(), BddPointer::zero()
        ));
        bdd.push_node(BddNode::mk_node(BddVariable(4),
                BddPointer::zero(), bdd.root_pointer()
        ));
        return bdd;
    }

    #[test]
    fn bdd_impl() {
        let bdd = mk_small_test_bdd();

        assert_eq!(4, bdd.size());
        assert_eq!(BddPointer(3), bdd.root_pointer());
        assert_eq!(BddPointer::one(), bdd.low_link_of(&BddPointer(2)));
        assert_eq!(BddPointer::zero(), bdd.high_link_of(&BddPointer(2)));
        assert_eq!(BddPointer::zero(), bdd.low_link_of(&BddPointer(3)));
        assert_eq!(BddPointer(2), bdd.high_link_of(&BddPointer(3)));
    }

}
