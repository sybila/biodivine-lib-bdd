//! **What is this?** This crate provides basic implementation of **Binary Decision Diagrams**
//! (BDD), or more specifically, Reduced Ordered Binary Decision Diagrams (ROBDD). Using
//! `biodivine-lib-bdd`, you can safely create, manipulate and serialize BDDs, even in
//! multi-threaded environment. BDDs can be used to represent Boolean functions (or formulas)
//! as well as Boolean relations or general sets of Boolean vectors.
//!
//! **Why is this useful?** Compared to other similar libraries, our BDDs do not share nodes in
//! one large graph, but each BDD has its own separate memory. While this prevents some
//! optimizations (and in the worst case it can increase memory usage significantly), it also
//! allows us to work with individual BDDs in a multi-threaded context easily and to avoid the
//! need for garbage collection or reference counting inside the BDDs. Serialisation is also
//! trivial. In terms of performance, this approach cannot outperform state of the art (thread
//! unsafe, garbage collected) implementations, at least not in ideal conditions (large enough
//! cache, low pressure on GC), but even in the ideal conditions we seem to be at most 2-3x slower.
//! In more favourable instances, we can even match or outperform such implementations.
//!
//! To quickly learn about what are BDDs and how to use this crate, check out the
//! [tutorial](./tutorial/index.html) module. It contains a wide range of examples.

use crate::bdd_node::BddNode;
use crate::bdd_pointer::BddPointer;
use std::iter::Map;
use std::ops::Range;

mod bdd_dot_printer;
mod bdd_expression_parser;
mod bdd_macro;
mod bdd_node;
mod bdd_pointer;
mod bdd_serialisation;
mod bdd_universe_impl;
mod bdd_valuation_impl;

pub mod tutorial;
pub use bdd_expression_parser::parse_boolean_formula;
pub use bdd_expression_parser::BooleanFormula;
pub use bdd_universe_impl::BddUniverse;
pub use bdd_universe_impl::BddUniverseBuilder;
pub use bdd_valuation_impl::BddValuation;
pub use bdd_valuation_impl::BddValuationIterator;
use std::fmt::{Display, Error, Formatter};
use std::slice::Iter;

/// BDD variable identifies one of the variables in the associated BDD universe.
///
/// Usage example: TODO.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BddVariable(u16);

impl Display for BddVariable {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        f.write_fmt(format_args!("{}", self.0))
    }
}

impl BddVariable {
    // Convert to little endian bytes
    pub fn to_le_bytes(&self) -> [u8; 2] {
        return self.0.to_le_bytes();
    }

    // Read from little endian byte representation
    pub fn from_le_bytes(bytes: [u8; 2]) -> BddVariable {
        return BddVariable(u16::from_le_bytes(bytes));
    }
}

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
        return BddPointer::from_index(self.0.len() - 1);
    }

    /// **(internal)** Get the low link of the node at a specified location.
    fn low_link_of(&self, node: BddPointer) -> BddPointer {
        return self.0[node.to_index()].low_link;
    }

    /// **(internal)** Get the high link of the node at a specified location.
    fn high_link_of(&self, node: BddPointer) -> BddPointer {
        return self.0[node.to_index()].high_link;
    }

    /// **(internal)** Get the conditioning variable of the node at a specified location.
    ///
    /// *Pre:* `node` is not a terminal node.
    fn var_of(&self, node: BddPointer) -> BddVariable {
        if cfg!(shields_up) && (node.is_one() || node.is_zero()) {
            panic!("Terminal nodes don't have a conditioning variable!");
        }
        return self.0[node.to_index()].var;
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
        return (0..self.size()).map(BddPointer::from_index);
    }

    /// **(internal)** Create an iterator over all nodes of the BDD (including terminals).
    fn nodes(&self) -> Iter<BddNode> {
        return self.0.iter();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    //TODO: Add tests on DFS postorder of created BDDs

    /// A small BDD over variables $v_1, v_2, v_3, v_4, v_5$ corresponding to the formula $(v_3 \land \neg v_4)$
    pub fn mk_small_test_bdd() -> Bdd {
        let mut bdd = Bdd::mk_true(5);
        bdd.push_node(BddNode::mk_node(
            BddVariable(3), // !v4
            BddPointer::one(),
            BddPointer::zero(),
        ));
        bdd.push_node(BddNode::mk_node(
            BddVariable(2), // v3
            BddPointer::zero(),
            bdd.root_pointer(),
        ));
        return bdd;
    }

    pub fn load_expected_results(test_name: &str) -> String {
        return std::fs::read_to_string(format!("test_results/{}", test_name))
            .expect("Cannot open result file.");
    }

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
