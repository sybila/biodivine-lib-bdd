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
//!
//! Here, we provide a quick overview of BDDs and how they are implemented in this library. If
//! you are interested in usage examples and API documentation, feel free to skip ahead :)
//!
//! ## What is a BDD?
//!
//! BDD is a *directed acyclic graph* (DAG) with two types of vertices (or nodes). There are two
//! terminal vertices called `1` and `0` which have no outgoing edges. The rest of the vertices
//! are decision vertices. Each decision vertex has an associated Boolean variable $v$ and two
//! outgoing edges $low$ and $high$. In diagrams, $low$ edges are typically drawn as dashed and
//! $high$ edges as solid. The graph has always one root vertex (with no predecessors).
//!
//! Semantically, for a given valuation (assignment) of Boolean variables $Val(v) \to \\{ 0, 1 \\}$,
//! we can "evaluate" the graph by starting in the root vertex and choosing the following vertex
//! based on the value of the current decision variable in the given valuation. Once we reach
//! a terminal vertex, we obtain a final Boolean value. For example, consider the formula
//! $a \land \neg b$. The corresponding BDD is the following:
//!
//! ```mermaid
//! graph LR
//!     a($a$)
//!     b($b$)
//!     zero($0$)
//!     one($1$)
//!     a -.-> zero
//!     a --> b
//!     b -.-> one
//!     b --> zero
//! ```
//!
//! We can see that there is only one path from the root ($a$) to `1` and this path corresponds
//! to the only valuation which satisfies the Boolean formula (i.e. $a = 1; b = 0$).
//!
//! Typically, BDDs assume some **fixed ordering of variables** such that every path from root to
//! terminal follows this ordering (thus *ordered*). Furthermore, in every BDD, all **redundant
//! vertices are removed** (thus *reduced*). The vertex is redundant if both $low$ and $high$
//! point to the same vertex (there is no decision) or if there is another vertex with the same
//! values of $v$, $low$ and $high$ somewhere else in the graph (we can reuse this vertex).
//!
//! When the BDD is ordered and reduced, it is **canonical**, i.e. every equivalent Boolean formula
//! has the same BDD (equality can be thus checked syntactically on the structure of the graph).
//!
//! ## Encoding BDD in an array
//!
//! While BDD is a graph, it would be wasteful to store each node of the BDD as a separate memory
//! object requiring allocations and book keeping. Instead, we sort nodes in each BDD in the
//! DFS post-order (taking low edge first and high edge second, although this decision is arbitrary)
//! of the graph and this way, we can easily save them as a sequence in an array. The only
//! exception are the two terminal nodes which we always place on positions 0 and 1
//! (empty BDD only has the 0 node).
//!
//! Because DFS post-order is unique, we can still check formula equivalence by comparing the two
//! arrays element-wise. Also notice that the root of the BDD is always the last element of the
//! array and children of any node always have smaller indices than the parent.
//!
//! The BDD from the previous section translates to the following array:
//!
//! ```c
//! [0, 1, (b, low = 1, high = 0), (a, low = 0, high = 2)]
//! ```
//!
//! Notice that the edge pointers are now indices into the array itself instead of memory
//! references. This also allows certain memory optimisations (for "small" BDDs, the pointers
//! only need to be 32 bits even on 64 bit platforms, etc.). Also, such representation is trivial
//! to serialize, deserialize or share, since we can just clone the whole array if needed.
//!
//! ## BDD Usage
//!
//! In order to create and manipulate BDDs, you have to first create a **BDD universe**.
//! The universe maintains knowledge about individual Boolean variables and their ordering.
//! Once the universe is created, the set of variables is immutable.
//!
//! There are two ways to create a BDD universe. First is to initialize the universe with explicit
//! named variables:
//! ```rust
//!   use biodivine_lib_bdd::BddUniverseBuilder;
//!
//!   let mut universe = BddUniverseBuilder::new();
//!   let v1 = universe.make_variable("v1");   // a new individual variable
//!   let vars = universe.make_variables(vec!["v2", "v3"]);    // new batch of variables
//!   let universe = universe.build();
//!
//!   assert_eq!(Some(v1), universe.var_by_name("v1"));
//!   assert_eq!(None, universe.var_by_name("unknown"));
//! ```
//!
//! Here, each BDD variable object (`v1` and elements of `vars`) can be later used to create
//! BDDs conditioning on these variables. The purpose of the universe builder is to check for
//! duplicate or invalid variable names (some special characters are not allowed because
//! it would break export to .dot). Once the universe is created, you can use `var_by_name` to
//! obtain a specific variable based on the name you used.
//!
//! Another option is to create an anonymous universe where the variables have default names:
//!
//! ```rust
//!   use biodivine_lib_bdd::BddUniverse;
//!
//!   let universe = BddUniverse::new_anonymous(4);   // new universe with 4 variables
//!   assert_eq!(4, universe.num_vars());
//!
//!   let vars = universe.variables();
//!   assert_eq!("x_3", universe.name_of(vars[3]));   // default name is always x_{var index}
//! ```
//!
//! By default, anonymous variables are named `x_{index}`, but you can use `name_of` to
//! obtain the name of any variable at runtime. You can also use the `variables` function to get
//! a vector of all available variables.
//!
//!
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
use std::iter::Map;
use std::ops::Range;

mod bdd_dot_printer;
mod bdd_expression_parser;
mod bdd_node;
mod bdd_pointer;
mod bdd_universe_impl;
mod bdd_valuation_impl;

pub mod bdd_macro;
pub use bdd_expression_parser::parse_boolean_formula;
pub use bdd_expression_parser::BooleanFormula;
pub use bdd_universe_impl::BddUniverse;
pub use bdd_universe_impl::BddUniverseBuilder;
pub use bdd_valuation_impl::BddValuation;
pub use bdd_valuation_impl::BddValuationIterator;

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
        return BddPointer((self.0.len() - 1) as u32);
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
        return (0..self.size()).map(|index| BddPointer(index as u32));
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
