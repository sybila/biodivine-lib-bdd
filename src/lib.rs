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
use std::ops::Range;
use std::iter::Map;

mod bdd_node;
mod bdd_pointer;
mod bdd_dot_printer;
mod bdd_universe_impl;
mod bdd_valuation;

pub use bdd_universe_impl::BddUniverse;
pub use bdd_universe_impl::BddUniverseBuilder;
pub use bdd_valuation::BddValuation;
pub use bdd_valuation::BddValuationIterator;

/// BDD variable identifies one of the variables in the associated BDD universe.
///
/// Usage example: TODO.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BddVariable(u16);

/// BDD object is an array-based encoding of the binary decision diagram.
///
/// Usage example: TODO.
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Bdd(Vec<BddNode>);

impl Bdd {

    /// The number of nodes in this BDD. (Do not confuse with cardinality!)
    pub fn size(&self) -> usize {
        return self.0.len();
    }

    /// Number of variables in the corresponding BDD universe.
    pub fn num_vars(&self) -> u16 {
        // Assert: every BDD is not empty - it has at least the terminal zero node.
        return self.0[0].var.0;
    }

    /// **(internal)** Pointer to the root of the decision diagram.
    fn root_pointer(&self) -> BddPointer {
        return BddPointer((self.0.len() - 1) as u32)
    }

    /// **(internal)** Get the low link of the node at a specified location.
    fn low_link_of(&self, node: &BddPointer) -> BddPointer {
        return self.0[node.0 as usize].low_link;
    }

    /// **(internal)** Get the high link of the node at a specified location.
    fn high_link_of(&self, node: &BddPointer) -> BddPointer {
        return self.0[node.0 as usize].high_link;
    }

    /// **(internal)** Get the conditioning variable of the node at a specified location.
    ///
    /// *Pre:* `node` is not a terminal node.
    fn var_of(&self, node: &BddPointer) -> BddVariable {
        if cfg!(shields_up) && (node.is_one() || node.is_zero()) {
            panic!("Terminal nodes don't have a conditioning variable!");
        }
        return self.0[node.0 as usize].var;
    }

    /// **(internal)** Create a new BDD for the `false` formula.
    fn mk_false(num_vars: u16) -> Bdd {
        return Bdd(vec![BddNode::mk_zero(num_vars)]);
    }

    /// **(internal)** Create a new BDD for the `true` formula.
    fn mk_true(num_vars: u16) -> Bdd {
        return Bdd(vec![BddNode::mk_zero(num_vars), BddNode::mk_one(num_vars)]);
    }

    /// **(internal)** True if this BDD is exactly the `true` formula.
    fn is_true(&self) -> bool {
        return self.0.len() == 2;
    }

    /// **(internal)** True if this BDD is exactly the `false` formula.
    fn is_false(&self) -> bool {
        return self.0.len() == 1;
    }

    /// **(internal)** Add a new node to an existing BDD, making the new node the root of the BDD.
    fn push_node(&mut self, node: BddNode) {
        self.0.push(node);
    }

    /// **(internal)** Create an iterator over all pointers of the BDD (including terminals!).
    ///
    /// The iteration order is the same as the underlying representation, so you can expect
    /// terminals to be the first two nodes.
    fn pointers(&self) -> Map<Range<usize>, fn(usize) -> BddPointer> {
        return (0..self.size()).map(|index| BddPointer(index as u32))
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    /// A small BDD over variables $v_1, v_2, v_3, v_4, v_5$ corresponding to the formula $(v_3 \land \neg v_4)$
    pub fn mk_small_test_bdd() -> Bdd {
        let mut bdd = Bdd::mk_true(5);
        bdd.push_node(BddNode::mk_node(BddVariable(3),  // !v4
           BddPointer::one(), BddPointer::zero()
        ));
        bdd.push_node(BddNode::mk_node(BddVariable(2),  // v3
           BddPointer::zero(), bdd.root_pointer()
        ));
        return bdd;
    }

    #[test]
    fn bdd_impl() {
        let bdd = mk_small_test_bdd();

        assert_eq!(4, bdd.size());
        assert_eq!(5, bdd.num_vars());
        assert_eq!(BddPointer(3), bdd.root_pointer());
        assert_eq!(BddPointer::one(), bdd.low_link_of(&BddPointer(2)));
        assert_eq!(BddPointer::zero(), bdd.high_link_of(&BddPointer(2)));
        assert_eq!(BddVariable(3), bdd.var_of(&BddPointer(2)));
        assert_eq!(BddPointer::zero(), bdd.low_link_of(&BddPointer(3)));
        assert_eq!(BddPointer(2), bdd.high_link_of(&BddPointer(3)));
        assert_eq!(BddVariable(2), bdd.var_of(&BddPointer(3)));
    }

}
