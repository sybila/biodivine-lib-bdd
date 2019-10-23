//! **(internal)** Provides essential operations for safely creating and manipulating BDDs.
//!
//! TODO: Describe BDD manipulation algorithms.

use std::collections::{HashMap, HashSet};
use super::{BddVariable, Bdd};
use super::bdd_node::BddNode;
use super::bdd_pointer::BddPointer;

/// BDD universe implements essential BDD operations.
///
/// It assumes an universe of variables that can appear in the BDDs and allows
/// you to create new atomic BDDs as well as combine existing BDDs into larger ones.
///
/// Operations are typically implemented in two variants. One is "static", i.e. it
/// can be used without actually accessing the BDD universe. The advantage of
/// these methods is that they don't need ownership or mutable reference of BDD universe,
/// hence can be very nicely used in parallel algorithms. The other type of operations
/// actually mutates the universe, which it uses to store some caches and helper values
/// in between operations. This can reduce allocation pressure and simplify some operations,
/// but it requires ownership or mutable reference.
#[derive(Clone)]
pub struct BddUniverse {
    num_vars: u16,
    var_names: Vec<String>,
    var_index_mapping: HashMap<String, u16>
}

impl BddUniverse {

    /// Return the number of variables in this universe.
    pub fn num_vars(&self) -> u16 {
        return self.num_vars;
    }

    /// Create a BDD corresponding to the `true` formula.
    pub fn mk_true(&self) -> Bdd {
        return Bdd::mk_true(self.num_vars);
    }

    /// Create a BDD corresponding to the `false` formula.
    pub fn mk_false(&self) -> Bdd {
        return Bdd::mk_false(self.num_vars);
    }

    /// Create a BDD corresponding to the $v$ formula where `v` is a specific variable in
    /// this universe.
    ///
    /// *Pre:* `var` is valid variable from this universe.
    pub fn mk_var(&self, var: &BddVariable) -> Bdd {
        if cfg!(shields_up) && var.0 >= self.num_vars {
            panic!("Variable {:?} is not in this universe.", var);
        }
        let mut bdd = self.mk_true();
        bdd.push_node(BddNode::mk_node(var.clone(),
        BddPointer::zero(), BddPointer::one()
        ));
        return bdd;
    }

    /// Create a BDD corresponding to the $\neg v$ formula where `v` is a specific variable in
    /// this universe.
    ///
    /// *Pre:* `var` is a valid variable in this universe.
    pub fn mk_not_var(&self, var: &BddVariable) -> Bdd {
        if cfg!(shields_up) && var.0 >= self.num_vars {
            panic!("Variable {:?} is not in this universe.", var);
        }
        let mut bdd = self.mk_true();
        bdd.push_node(BddNode::mk_node(var.clone(),
        BddPointer::one(), BddPointer::zero()
        ));
        return bdd;
    }

    /// Create a BDD corresponding to the $\neg \phi$ formula, where $\phi$ is a specific
    /// formula given by a BDD.
    pub fn mk_not(&self, phi: &Bdd) -> Bdd {
        if cfg!(shields_up) && phi.num_vars() != self.num_vars {
            panic!("BDD is not from this universe. {} != {}", phi.num_vars(), self.num_vars);
        }
        if phi.is_true() {
            return self.mk_false();
        } else if phi.is_false() {
            return self.mk_true();
        } else {
            let mut result_vector = phi.0.clone();
            for i in 2..result_vector.len() {   // skip terminals
                result_vector[i].high_link.flip_if_terminal();
                result_vector[i].low_link.flip_if_terminal();
            }
            return Bdd(result_vector);
        }
    }

    pub fn mk_t

}

/// BDD universe builder is used to safely create BDD universes.
pub struct BddUniverseBuilder {
    var_names: Vec<String>,
    var_names_set: HashSet<String>
}

impl BddUniverseBuilder {

    /// Create a new builder without any variables.
    pub fn new() -> BddUniverseBuilder {
        return BddUniverseBuilder { var_names: Vec::new(), var_names_set: HashSet::new() };
    }

    /// Create a new variable with the given `name`. Returns a BDD variable
    /// instance that can be later used to create and query actual BDDs.
    ///
    /// *Panics*:
    ///  - Each variable name has to be unique.
    ///  - Currently, there can be at most 65535 variables.
    pub fn make_variable(&mut self, name: String) -> BddVariable {
        let new_variable_id = self.var_names.len();
        if new_variable_id >= (std::u16::MAX - 1) as usize {
            panic!("BDD universe is too large. There can be at most {} variables.", std::u16::MAX - 1)
        }
        if self.var_names_set.contains(&name) {
            panic!("BDD variable {} already exists.", name);
        }
        self.var_names_set.insert(name.clone());
        self.var_names.push(name);
        return BddVariable(new_variable_id as u16);
    }

    /// Convert this builder to an actual BDD worker.
    pub fn build(self) -> BddUniverse {
        let mut mapping: HashMap<String, u16> = HashMap::new();
        for name_index in 0..self.var_names.len() {
            let name = self.var_names[name_index].clone();
            mapping.insert(name, name_index as u16);
        }
        return BddUniverse {
            num_vars: self.var_names.len() as u16,
            var_names: self.var_names,
            var_index_mapping: mapping
        }
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn bdd_worker_too_large() {
        let mut builder = BddUniverseBuilder::new();
        for i in 0..std::u16::MAX {
            builder.make_variable(format!("v{}", i));
        }
    }

    #[test]
    #[should_panic]
    fn bdd_worker_duplicate_variable() {
        let mut builder = BddUniverseBuilder::new();
        builder.make_variable("var1".to_string());
        builder.make_variable("var1".to_string());
    }

}