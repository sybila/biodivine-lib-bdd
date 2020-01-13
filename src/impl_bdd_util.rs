//! **(internal)** Implementation of some basic internal utility methods for `Bdd`s.

use super::*;
use std::iter::Map;
use std::ops::Range;
use std::slice::Iter;

/// Several useful (mostly internal) low-level utility methods for `Bdd`s.
impl Bdd {
    /// The number of nodes in this `Bdd`. (Do not confuse with cardinality)
    pub fn size(&self) -> usize {
        return self.0.len();
    }

    /// Number of variables in the corresponding `BddVariableSet`.
    pub fn num_vars(&self) -> u16 {
        // Assert: every BDD is not empty - it has at least the terminal zero node.
        return self.0[0].var.0;
    }

    /// True if this `Bdd` is exactly the `true` formula.
    pub fn is_true(&self) -> bool {
        return self.0.len() == 2;
    }

    /// True if this `Bdd` is exactly the `false` formula.
    pub fn is_false(&self) -> bool {
        return self.0.len() == 1;
    }

    /// **(internal)** Pointer to the root of the decision diagram.
    pub(super) fn root_pointer(&self) -> BddPointer {
        return BddPointer::from_index(self.0.len() - 1);
    }

    /// **(internal)** Get the low link of the node at a specified location.
    pub(super) fn low_link_of(&self, node: BddPointer) -> BddPointer {
        return self.0[node.to_index()].low_link;
    }

    /// **(internal)** Get the high link of the node at a specified location.
    pub(super) fn high_link_of(&self, node: BddPointer) -> BddPointer {
        return self.0[node.to_index()].high_link;
    }

    /// **(internal)** Get the conditioning variable of the node at a specified location.
    ///
    /// *Panics:* `node` must not be a terminal.
    pub(super) fn var_of(&self, node: BddPointer) -> BddVariable {
        if cfg!(shields_up) && (node.is_one() || node.is_zero()) {
            panic!("Terminal nodes don't have a conditioning variable!");
        }
        return self.0[node.to_index()].var;
    }

    /// **(internal)** Create a new `Bdd` for the `false` formula.
    pub(super) fn mk_false(num_vars: u16) -> Bdd {
        return Bdd(vec![BddNode::mk_zero(num_vars)]);
    }

    /// **(internal)** Create a new `Bdd` for the `true` formula.
    pub(super) fn mk_true(num_vars: u16) -> Bdd {
        return Bdd(vec![BddNode::mk_zero(num_vars), BddNode::mk_one(num_vars)]);
    }

    /// **(internal)** Add a new node to an existing `Bdd`, making the new node the root of the `Bdd`.
    pub(super) fn push_node(&mut self, node: BddNode) {
        self.0.push(node);
    }

    /// **(internal)** Create an iterator over all pointers of the `Bdd` (including terminals!).
    ///
    /// The iteration order is the same as the underlying representation, so you can expect
    /// terminals to be the first two nodes.
    pub(super) fn pointers(&self) -> Map<Range<usize>, fn(usize) -> BddPointer> {
        return (0..self.size()).map(BddPointer::from_index);
    }

    /// **(internal)** Create an iterator over all nodes of the `Bdd` (including terminals).
    pub(super) fn nodes(&self) -> Iter<BddNode> {
        return self.0.iter();
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_util::mk_small_test_bdd;
    use super::*;

    //TODO: Add tests on DFS postorder of created BDDs

    #[test]
    fn bdd_impl() {
        let bdd = mk_small_test_bdd();

        assert_eq!(4, bdd.size());
        assert_eq!(5, bdd.num_vars());
        assert_eq!(BddPointer::from_index(3), bdd.root_pointer());
        assert_eq!(
            BddPointer::one(),
            bdd.low_link_of(BddPointer::from_index(2))
        );
        assert_eq!(
            BddPointer::zero(),
            bdd.high_link_of(BddPointer::from_index(2))
        );
        assert_eq!(BddVariable(3), bdd.var_of(BddPointer::from_index(2)));
        assert_eq!(
            BddPointer::zero(),
            bdd.low_link_of(BddPointer::from_index(3))
        );
        assert_eq!(
            BddPointer::from_index(2),
            bdd.high_link_of(BddPointer::from_index(3))
        );
        assert_eq!(BddVariable(2), bdd.var_of(BddPointer::from_index(3)));
    }
}
