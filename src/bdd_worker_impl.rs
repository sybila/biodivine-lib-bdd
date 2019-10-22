//! Provides essential operations for safely creating and manipulating BDDs.
//!
//! TODO: Describe BDD manipulation algorithms.

use std::collections::HashMap;

/// TODO
pub struct BddWorker {
    num_vars: u32,
    var_names: Vec<String>,
    var_index_mapping: HashMap<String, u32>
}