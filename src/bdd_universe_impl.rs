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

/// A macro for simplifying BDD operations. As first argument, you provide
/// a BDD universe. Second argument is an expression over BDDs where you can use
/// standard boolean operators `!`, `&`, `|`, `^`, `=>` and `<=>`. Note that everything
/// needs to be enclosed in parentheses (except ! which can be parsed unambiguously).
///
/// TODO: Usage example.
#[macro_export]
macro_rules! bdd {
        // The extra borrow operator allows us to cover cases where BDDs are either owned
        // directly or they are just references, because rust will automatically turn &&x
        // into &x for us when invoking a function.
        ($b:ident, !($($e:tt)*) ) => { $b.mk_not(&(bdd!($b, $($e)*))) };
        // Not is the only operator which we allow without parentheses because it should
        // not be ambiguous.
        ($b:ident, !$($e:tt)* ) => { $b.mk_not(&(bdd!($b, $($e)*))) };
        // Everything else must be in (), because there are no precedence/priority rules.
        ($b:ident, ($l:tt & $($r:tt)*) ) => { $b.mk_and(&(bdd!($b, $l)), &(bdd!($b, $($r)*))) };
        ($b:ident, ($l:tt | $($r:tt)*) ) => { $b.mk_or(&(bdd!($b, $l)), &(bdd!($b, $($r)*))) };
        ($b:ident, ($l:tt => $($r:tt)*) ) => { $b.mk_imp(&(bdd!($b, $l)), &(bdd!($b, $($r)*))) };
        ($b:ident, ($l:tt <=> $($r:tt)*) ) => { $b.mk_iff(&(bdd!($b, $l)), &(bdd!($b, $($r)*))) };
        ($b:ident, ($l:tt ^ $($r:tt)*) ) => { $b.mk_xor(&(bdd!($b, $l)), &(bdd!($b, $($r)*))) };
        ($b:ident, $e:tt) => { $e };
    }

impl BddUniverse {

    /// Return the number of variables in this universe.
    pub fn num_vars(&self) -> u16 {
        return self.num_vars;
    }

    /// Create a BDD variable based on a variable name. If the name is not valid
    /// in this universe, return `None`.
    pub fn var_by_name(&self, name: &str) -> Option<BddVariable> {
        return self.var_index_mapping.get(name).map(|i| BddVariable(*i));
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
        if cfg!(feature = "shields_up") && var.0 >= self.num_vars {
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
        if cfg!(feature = "shields_up") && var.0 >= self.num_vars {
            panic!("Variable {:?} is not in this universe.", var);
        }
        let mut bdd = self.mk_true();
        bdd.push_node(BddNode::mk_node(var.clone(),
        BddPointer::one(), BddPointer::zero()
        ));
        return bdd;
    }

    /// Create a BDD corresponding to the $v$ formula where `v` is a variable in this universe.
    ///
    /// *Pre:* `var` is a valid variable in this universe.
    pub fn mk_var_by_name(&self, var: &str) -> Bdd {
        return self.var_by_name(var)
            .map(|var| self.mk_var(&var))
            .unwrap_or_else(|| panic!("Variable {} is known present in this universe.", var));
    }

    /// Create a BDD corresponding to the $\neg v$ formula where `v` is a variable in this universe.
    ///
    /// *Pre:* `var` is a valid variable in this universe.
    pub fn mk_not_var_by_name(&self, var: &str) -> Bdd {
        return self.var_by_name(var)
            .map(|var| self.mk_not_var(&var))
            .unwrap_or_else(|| panic!("Variable {} is not known in this universe.", var));
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

    /// Create a BDD corresponding to the $\phi \land \psi$ formula, where $\phi$ and $\psi$
    /// are two specific BDDs.
    pub fn mk_and(&self, left: &Bdd, right: &Bdd) -> Bdd {
        unimplemented!();
    }

    /// Create a BDD corresponding to the $\phi \lor \psi$ formula, where $\phi$ and $\psi$
    /// are two specific BDDs.
    pub fn mk_or(&self, left: &Bdd, right: &Bdd) -> Bdd {
        unimplemented!();
    }

    /// Create a BDD corresponding to the $\phi \Rightarrow \psi$ formula, where $\phi$ and $\psi$
    /// are two specific BDDs.
    pub fn mk_imp(&self, left: &Bdd, right: &Bdd) -> Bdd {
        unimplemented!();
    }

    /// Create a BDD corresponding to the $\phi \Leftrightarrow \psi$ formula, where $\phi$ and $\psi$
    /// are two specific BDDs.
    pub fn mk_iff(&self, left: &Bdd, right: &Bdd) -> Bdd {
        unimplemented!();
    }

    /// Create a BDD corresponding to the $\phi \oplus \psi$ formula, where $\phi$ and $\psi$
    /// are two specific BDDs.
    pub fn mk_xor(&self, left: &Bdd, right: &Bdd) -> Bdd {
        unimplemented!();
    }

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
    pub fn make_variable(&mut self, name: &str) -> BddVariable {
        let new_variable_id = self.var_names.len();
        if new_variable_id >= (std::u16::MAX - 1) as usize {
            panic!("BDD universe is too large. There can be at most {} variables.", std::u16::MAX - 1)
        }
        if self.var_names_set.contains(name) {
            panic!("BDD variable {} already exists.", name);
        }
        self.var_names_set.insert(name.to_string());
        self.var_names.push(name.to_string());
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
    use super::super::tests::mk_small_test_bdd;

    fn mk_universe_with_5_variables() -> BddUniverse {
        let mut builder = BddUniverseBuilder::new();
        builder.make_variable("v1");
        builder.make_variable("v2");
        builder.make_variable("v3");
        builder.make_variable("v4");
        builder.make_variable("v5");
        return builder.build();
    }

    #[test]
    #[should_panic]
    fn bdd_universe_too_large() {
        let mut builder = BddUniverseBuilder::new();
        for i in 0..std::u16::MAX {
            builder.make_variable(&format!("v{}", i));
        }
    }

    #[test]
    #[should_panic]
    fn bdd_universe_duplicate_variable() {
        let mut builder = BddUniverseBuilder::new();
        builder.make_variable("var1");
        builder.make_variable("var1");
    }

    #[test]
    fn bdd_universe_builder() {
        let mut builder = BddUniverseBuilder::new();
        let v1 = builder.make_variable("v1");
        let v2 = builder.make_variable("v2");
        let v3 = builder.make_variable("v3");
        let universe = builder.build();
        assert_eq!(3, universe.num_vars());
        assert_eq!(Some(v1), universe.var_by_name("v1"));
        assert_eq!(Some(v2), universe.var_by_name("v2"));
        assert_eq!(Some(v3), universe.var_by_name("v3"));
        assert_eq!(None, universe.var_by_name("v4"));
    }

    #[test]
    fn bdd_universe_mk_const() {
        let universe = mk_universe_with_5_variables();
        let tt = universe.mk_true();
        let ff = universe.mk_false();
        assert!(tt.is_true());
        assert!(ff.is_false());
        assert_eq!(Bdd::mk_true(5), tt);
        assert_eq!(Bdd::mk_false(5), ff);
    }

    #[test]
    #[should_panic]
    fn bdd_universe_mk_var_invalid_id() {
        mk_universe_with_5_variables().mk_var(&BddVariable(6));
    }

    #[test]
    #[should_panic]
    fn bdd_universe_mk_not_var_invalid_id() {
        mk_universe_with_5_variables().mk_not_var(&BddVariable(6));
    }

    #[test]
    #[should_panic]
    fn bdd_universe_mk_var_by_name_invalid_name() {
        mk_universe_with_5_variables().mk_var_by_name("abc");
    }

    #[test]
    #[should_panic]
    fn bdd_universe_mk_not_var_by_name_invalid_name() {
        mk_universe_with_5_variables().mk_not_var_by_name("abc");
    }

    #[test]
    fn bdd_universe_mk_not() {
        let universe = mk_universe_with_5_variables();
        let bdd = mk_small_test_bdd();
        let mut expected = universe.mk_true();
        expected.push_node(BddNode::mk_node(
            BddVariable(3), BddPointer::zero(), BddPointer::one()
        ));
        expected.push_node(BddNode::mk_node(
            BddVariable(4), BddPointer::one(), BddPointer(2)
        ));
        assert_eq!(expected, universe.mk_not(&bdd));
        assert_eq!(bdd, universe.mk_not(&universe.mk_not(&bdd)));
    }

    #[test]
    fn bdd_macro_test() {
        let universe = mk_universe_with_5_variables();
        let bdd = mk_small_test_bdd();
        let not_bdd = universe.mk_not(&bdd);
        assert_eq!(bdd, bdd!(universe, bdd));
        assert_eq!(not_bdd, bdd!(universe, !bdd));
        assert_eq!(bdd, bdd!(universe, !!bdd));
    }

}