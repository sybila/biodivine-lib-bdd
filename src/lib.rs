#![feature(test)] // necessary for benchmark tests
extern crate test;

#[cfg(test)]
mod benchmarks;

use std::collections::{HashMap, HashSet};

pub mod boolean_expression;
pub mod tutorial;

mod impl_bdd_boolean_ops;
mod impl_bdd_export_dot;
mod impl_bdd_serialisation;
mod impl_bdd_util;

mod impl_bdd_node;
mod impl_bdd_pointer;
mod impl_bdd_valuation;
mod impl_bdd_variable;
mod impl_bdd_variable_set;
mod impl_bdd_variable_set_builder;

mod macro_bdd;

#[cfg(test)]
mod test_bdd_logic_basic;
#[cfg(test)]
mod test_bdd_logic_fuzzing;
#[cfg(test)]
mod test_util;

/// Characters that cannot appear in the variable name
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

/// TODO: Rename this to BitVector and move it to std-lib? The same for the iterator.
/// Exactly describes one assignment of boolean values to variables of a `Bdd`.
///
/// It can be used as a witness of `Bdd` non-emptiness, since one can evaluate every `Bdd`
/// in some corresponding valuation and get a `true/false` result.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct BddValuation(Vec<bool>);

/// Exhaustively iterates over all valuations with a certain number of variables.
///
/// Be aware of the exponential time complexity of such operation!
pub struct BddValuationIterator(Option<BddValuation>);

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
