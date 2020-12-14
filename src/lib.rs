//! This crate provides a basic implementation of binary decision diagrams (BDDs) — a symbolic data
//! structure for representing boolean functions or other equivalent objects (such as bit-vector
//! sets).
//!
//! Compared to other popular implementations, every BDD owns its memory. It is thus trivial to
//! serialise, but also to share between threads. This makes it useful for applications that
//! process high number of BDDs concurrently.
//!
//! We currently provide support for explicit operations as well as evaluation of basic boolean
//! expressions and a custom `bdd` macro for hybrid usage:
//!
//! ```rust
//! use biodivine_lib_bdd::*;
//!
//! let vars = BddVariableSet::new(vec!["a", "b", "c"]);
//! let a = vars.mk_var_by_name("a");
//! let b = vars.mk_var_by_name("b");
//! let c = vars.mk_var_by_name("c");
//!
//! let f1 = a.iff(&b.not()).or(&c.xor(&a));
//! let f2 = vars.eval_expression_string("(a <=> !b) | c ^ a");
//! let f3 = bdd!((a <=> (!b)) | (c ^ a));
//!
//! assert!(!f1.is_false());
//! assert_eq!(f1.cardinality(), 6.0);
//! assert_eq!(f1, f2);
//! assert_eq!(f2, f3);
//! assert!(f1.iff(&f2).is_true());
//! assert!(f1.iff(&f3).is_true());
//! ```
//!
//! Additionally, we provide serialisation into a custom string and binary formats as well as `.dot`.
//! For a more detailed description, see the [tutorial module](./tutorial/index.html) documentation.
//! There is also an experimental support for converting BDDs back into boolean expressions.

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

/// **(internal)** Implementation of the `BddValuationsIterator`.
mod _impl_bdd_satisfying_valuations;

/// **(internal)** Implementation of the `BddVariable`.
mod _impl_bdd_variable;

/// **(internal)** Implementation of the `BddVariableSet`.
mod _impl_bdd_variable_set;

/// **(internal)** Implementation of the `BddVariableSetBuilder`.
mod _impl_bdd_variable_set_builder;

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

/// Exhaustively iterates over all valuations with a certain number of variables.
///
/// Be aware of the exponential time complexity of such operation!
pub struct BddValuationIterator(Option<BddValuation>);

/// An iterator over all satisfying valuations of a specific BDD.
///
/// Be aware of the potential exponential number of iterations!
pub struct BddSatisfyingValuations<'a> {
    bdd: &'a Bdd,
    continuation: Option<(Vec<BddPointer>, BddValuation, BddValuation)>,
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
pub struct BddVariableSetBuilder {
    var_names: Vec<String>,
    var_names_set: HashSet<String>,
}

/// **(internal)** A type-safe index into the `Bdd` node array representation.
///
/// BDD pointers are an internal type-safe wrapper around indices into BDD arrays.
/// Outside this crate, no one should know or care about their existence. Since
/// we can't reasonably expect a BDD to be larger than `2^32` right now, the pointer is
/// represented as `u32` instead of `usize`, because `usize` can be 64-bits and pointers
/// represent most of the memory consumed by our BDDs.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct BddPointer(u32);

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
