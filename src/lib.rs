//! # Biodivine/LibBDD
//!
//! This crate provides a basic implementation of [binary decision diagrams](https://en.wikipedia.org/wiki/Binary_decision_diagram) (BDDs) — a symbolic data
//! structure for representing Boolean functions or other equivalent objects (such as bit-vector
//! sets).
//!
//! Compared to other popular implementations, every BDD owns its memory. It is thus trivial to
//! serialise, but also to share between threads. This makes it useful for applications that
//! process high number of BDDs concurrently, but is also generally more idiomatic in Rust.
//!
//! At the moment, we support many standard operations on BDDs:
//!
//!  - Any binary logical operation (`and`, `or`, `iff`, ...), and of course negation.
//!  - Evaluation of Boolean expressions parsed from a string.
//!  - A `bdd!` macro for a more idiomatic specification of operation chains.
//!  - Simplified methods for CNF/DNF formula construction.
//!  - Binary and text serialization/deserialization.
//!  - Valuation/path iterators and other `Bdd` introspection methods (`random_valuation`, `most_fixed_clause`, ...).
//!  - Export of `Bdd` back into a Boolean expression.
//!  - "Relational" operations: projection (existential quantification), selection (restriction) and unique subset picking (see tutorials for more info).
//!  - A "variable flip" operation fused with custom logical binary operators.
//!  - Export to `.dot` graphs.
//!
//! More detailed description of all features can be found in our [tutorial module](https://docs.rs/biodivine-lib-bdd/latest/biodivine_lib_bdd/tutorial/index.html), and of course in the [API documentation](https://docs.rs/biodivine-lib-bdd/latest/).
//!
//! ```rust
//! use biodivine_lib_bdd::*;
//!
//! let mut builder = BddVariableSetBuilder::new();
//! let [a, b, c] = builder.make(&["a", "b", "c"]);
//! let variables: BddVariableSet = builder.build();
//!
//! // String expressions:
//! let x = variables.eval_expression_string("(a <=> !b) | c ^ a");
//! // Macro:
//! let y = bdd!(variables, (a <=> (!b)) | (c ^ a));
//! // Logical operators:
//! let z = variables.mk_literal(a, true)
//!     .iff(&variables.mk_literal(b, false))
//!     .or(&variables.mk_literal(c, true).xor(&variables.mk_literal(a, true)));
//!
//! assert!(!x.is_false());
//! assert_eq!(6.0, x.cardinality());
//! assert_eq!(x, y);
//! assert_eq!(y, z);
//! assert_eq!(z, x);
//!
//! for valuation in x.sat_valuations() {
//!     assert!(x.eval_in(&valuation));
//! }
//! ```
//!

use std::collections::{HashMap, HashSet};

pub mod boolean_expression;
pub mod op_function;
pub mod tutorial;

/// **(internal)** Implementations for the `Bdd` struct.
mod _impl_bdd;

/// **(internal)** Several complex test scenarios for the `Bdd` struct.
#[cfg(test)]
mod _test_bdd;

/// **(internal)** Implementation of the `BddNode`.
mod _impl_bdd_node;

/// **(internal)** Implementation of the `BddPointer`.
mod _impl_bdd_pointer;

/// **(internal)** Implementation of the `BddValuation`.
mod _impl_bdd_valuation;

/// **(internal)** Implementation of the `BddPartialValuation`.
mod _impl_bdd_partial_valuation;

/// **(internal)** Implementation of the `BddValuationsIterator`.
mod _impl_bdd_satisfying_valuations;

/// **(internal)** Implementation of the `BddVariable`.
mod _impl_bdd_variable;

/// **(internal)** Implementation of the `BddVariableSet`.
mod _impl_bdd_variable_set;

/// **(internal)** Implementation of the `BddVariableSetBuilder`.
mod _impl_bdd_variable_set_builder;

/// **(internal)** Implementation of the `ValuationOfClauseIterator`.
mod _impl_iterator_valuations_of_clause;

/// **(internal)** Implementation of the `BddPathIterator`.
mod _impl_bdd_path_iterator;

/// **(internal)** A macro module for simplifying BDD operations.
mod _macro_bdd;

/// Several basic utility methods for testing `Bdd`s.
#[cfg(test)]
mod _test_util;

/// **(internal)** Characters that cannot appear in the variable name
/// (based on possible tokens in a boolean expression).
const NOT_IN_VAR_NAME: [char; 9] = ['!', '&', '|', '^', '=', '<', '>', '(', ')'];

/// An array-based encoding of the binary decision diagram implementing basic logical operations.
///
/// To create `Bdd`s for atomic formulas, use a `BddVariableSet`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Bdd(Vec<BddNode>);

/// Identifies one of the variables that can appear as a decision condition in the `Bdd`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BddVariable(u16);

/// Exactly describes one assignment of boolean values to variables of a `Bdd`.
///
/// It can be used as a witness of `Bdd` non-emptiness, since one can evaluate every `Bdd`
/// in some corresponding valuation and get a `true/false` result.
#[derive(Clone, Debug, Eq, Hash, PartialEq, Ord, PartialOrd)]
pub struct BddValuation(Vec<bool>);

/// Describes assignment of some arbitrary number of `Bdd` variables.
///
/// A partial valuation can be used to quickly construct simple conjunctive/disjunctive clauses.
/// It also exactly describes one path in a `Bdd` and hence can be used as an intermediate
/// value when traversing the valuations of a `Bdd`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct BddPartialValuation(Vec<Option<bool>>);

/// Exhaustively iterates over all valuations with a certain number of variables.
///
/// Be aware of the exponential time complexity of such operation!
///
/// *Deprecated in favour of `ValuationsOfClauseIterator` which provides the same
/// functionality when given an empty clause.*
#[deprecated]
pub struct BddValuationIterator(ValuationsOfClauseIterator);

/// An iterator over all satisfying valuations of a specific BDD.
///
/// Be aware of the potential exponential number of iterations!
pub struct BddSatisfyingValuations<'a> {
    bdd: &'a Bdd,
    paths: BddPathIterator<'a>,
    valuations: ValuationsOfClauseIterator,
}

/// An iterator which goes through all paths in the `Bdd`, representing them as clauses using
/// `BddPartialValuation`.
pub struct BddPathIterator<'a> {
    bdd: &'a Bdd,
    // Stack keeps the last discovered path. If last path was consumed, the stack is empty.
    stack: Vec<BddPointer>,
}

/// An iterator which goes through all valuations that satisfy a specific *conjunctive* clause.
///
/// Mind that the number of valuations satisfying a clause can be exponential!
///
/// Note that the clause can be empty, in which case this is equivalent to `BddValuationIterator`.
#[derive(Clone)]
pub struct ValuationsOfClauseIterator {
    next_valuation: Option<BddValuation>,
    clause: BddPartialValuation,
}

/// Maintains the set of variables that can appear in a `Bdd`.
/// Used to create new `Bdd`s for basic formulas.
#[derive(Clone)]
pub struct BddVariableSet {
    num_vars: u16,
    var_names: Vec<String>,
    var_index_mapping: HashMap<String, u16>,
}

/// Used to safely initialize `BddVariableSet`.
///
/// Note that some characters are not allowed in variable names (to allow safe serialisation,
/// formula parsers and export as `.dot`, etc.).
/// These characters are `!`, `&`, `|`, `^`, `=`, `<`, `>`, `(` and `)`.
#[derive(Clone)]
pub struct BddVariableSetBuilder {
    var_names: Vec<String>,
    var_names_set: HashSet<String>,
}

/// A type-safe index into the `Bdd` node array representation.
///
/// BDD pointers are an internal type-safe wrapper around indices into BDD arrays.
/// Outside this crate, no one should know or care about their existence. Since
/// we can't reasonably expect a BDD to be larger than `2^32` right now, the pointer is
/// represented as `u32` instead of `usize`, because `usize` can be 64-bits and pointers
/// represent most of the memory consumed by our BDDs.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BddPointer(u32);

/// **(internal)** Representation of individual vertices of the `Bdd` directed acyclic graph.
///
/// A `BddNode` can be a terminal, in which case it is either `0` or `1`, or a decision node,
/// in which case it contains a variable $v_i$ which it conditions upon and two pointers
/// (`low` and `high`) to other nodes in the same `Bdd`:
///
/// ```mermaid
/// graph LR
///     id1($v_i$)
///     id2($v_j$)
///     id3($v_k$)
///     id1 -->|low| id2
///     id1 -->|high| id3
/// ```
///
/// Internally, we represent terminal nodes using the same structure, giving them cyclic
/// pointers. Instead of variable id, we use the number of variables in the original
/// `BddVariableSet`. This is consistent with the fact that we first condition on smallest
/// variable ids. It can be also used for consistency checks inside the library.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct BddNode {
    pub var: BddVariable,
    pub low_link: BddPointer,
    pub high_link: BddPointer,
}

/// A trait which allows quick conversion of a type into a `Bdd`, assuming an appropriate
/// `BddVariablesSet` is provided.
pub trait IntoBdd {
    fn into_bdd(self, variables: &BddVariableSet) -> Bdd;
}
