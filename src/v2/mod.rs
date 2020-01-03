use std::collections::{HashMap, HashSet};

mod bdd_ops;
mod bdd_util;
mod bdd_node_impl;
mod bdd_pointer_impl;
mod bdd_variable_impl;
mod bdd_serialisation;
mod bdd_variable_set_builder_impl;
mod bdd_variable_set_impl;

/// Characters that cannot appear in the variable name
/// (based on possible tokens in a boolean expression).
const NOT_IN_VAR_NAME: [char; 9] = ['!', '&', '|', '^', '=', '<', '>', '(', ')'];

/// BDD object is an array-based encoding of the binary decision diagram. Basic BDDs
/// are created using the `BddVariableSet` object.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Bdd(Vec<BddNode>);

/// BDD variable identifies one of the variables that can appear as a decision condition
/// in the BDDs.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BddVariable(u16);

/// BDD variable set holds the set of variables that can appear in a BDD. Using
/// this object, you can create new BDDs for basic formulas.
#[derive(Clone)]
pub struct BddVariableSet {
    num_vars: u16,
    var_names: Vec<String>,
    var_index_mapping: HashMap<String, u16>,
}

/// BDD variables builder is used to safely create BDD variable set.
pub struct BddVariableSetBuilder {
    var_names: Vec<String>,
    var_names_set: HashSet<String>,
}

/// **(internal)** BDD pointer is an index into the BDD node array representation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct BddPointer(u32);

/// **(internal)** BDD nodes represent individual vertices of the BDD directed acyclic graph.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
struct BddNode {
    pub var: BddVariable,
    pub low_link: BddPointer,
    pub high_link: BddPointer,
}
