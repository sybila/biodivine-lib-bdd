//! **(internal)** Provides essential operations for safely creating and manipulating BDDs.
//!
//! TODO: Describe BDD manipulation algorithms.

use std::collections::{HashMap, HashSet};
use super::{BddVariable, Bdd};
use super::bdd_node::BddNode;
use super::bdd_pointer::BddPointer;
use std::cmp::min;
use crate::bdd_dot_printer::bdd_as_dot_string;

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
    ($b:ident, ( $($e:tt)* ) ) => { bdd!($b, $($e)*) };
    ($b:ident, $bdd:ident ) => { $bdd };
    ($b:ident, !$e:tt) => { $b.mk_not(&bdd!($b, $e)) };
    ($b:ident, $l:tt & $r:tt) => { $b.mk_and(&bdd!($b, $l), &bdd!($b, $r)) };
    ($b:ident, $l:tt | $r:tt) => { $b.mk_or(&bdd!($b, $l), &bdd!($b, $r)) };
    ($b:ident, $l:tt <=> $r:tt) => { $b.mk_iff(&bdd!($b, $l), &bdd!($b, $r)) };
    ($b:ident, $l:tt => $r:tt) => { $b.mk_imp(&bdd!($b, $l), &bdd!($b, $r)) };
    ($b:ident, $l:tt ^ $r:tt) => { $b.mk_xor(&bdd!($b, $l), &bdd!($b, $r)) };
}

impl BddUniverse {

    /// Create a new BDD universe with anonymous variables $(x_1, \ldots, x_n)$ where $n$ is
    /// the `num_vars` parameter.
    pub fn new_anonymous(num_vars: u16) -> BddUniverse {
        if num_vars >= (std::u16::MAX - 1) {
            panic!("BDD universe is too large. There can be at most {} variables.", std::u16::MAX - 1)
        }
        return BddUniverse {
            num_vars,
            var_names: (0..num_vars).map(|i| format!("x_{}", i)).collect(),
            var_index_mapping: (0..num_vars).map(|i| (format!("x_{}", i), i)).collect()
        }
    }

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
        return self.apply(left, right, |l, r| match (l, r) {
            (Some(true), Some(true)) => Some(true),
            (Some(false), _) => Some(false),
            (_, Some(false)) => Some(false),
            _ => None
        });
    }

    /// Create a BDD corresponding to the $\phi \lor \psi$ formula, where $\phi$ and $\psi$
    /// are two specific BDDs.
    pub fn mk_or(&self, left: &Bdd, right: &Bdd) -> Bdd {
        return self.apply(left, right, |l, r| match (l, r) {
            (Some(false), Some(false)) => Some(false),
            (Some(true), _) => Some(true),
            (_, Some(true)) => Some(true),
            _ => None
        });
    }

    /// Create a BDD corresponding to the $\phi \Rightarrow \psi$ formula, where $\phi$ and $\psi$
    /// are two specific BDDs.
    pub fn mk_imp(&self, left: &Bdd, right: &Bdd) -> Bdd {
        return self.apply(left, right, |l, r| match (l, r) {
            (Some(true), Some(false)) => Some(false),
            (Some(false), _) => Some(true),
            (_, Some(true)) => Some(true),
            _ => None
        });
    }

    /// Create a BDD corresponding to the $\phi \Leftrightarrow \psi$ formula, where $\phi$ and $\psi$
    /// are two specific BDDs.
    pub fn mk_iff(&self, left: &Bdd, right: &Bdd) -> Bdd {
        return self.apply(left, right, |l, r| match (l, r) {
            (Some(l), Some(r)) => Some(l == r),
            _ => None
        });
    }

    /// Create a BDD corresponding to the $\phi \oplus \psi$ formula, where $\phi$ and $\psi$
    /// are two specific BDDs.
    pub fn mk_xor(&self, left: &Bdd, right: &Bdd) -> Bdd {
        return self.apply(left, right, |l, r| match (l, r) {
            (Some(l), Some(r)) => Some(l ^ r),
            _ => None
        });
    }

    /// Convert a BDD object to a string representing its graph as a .dot file.
    ///
    /// Use `zero_pruned` to remove `0` terminal and all edges leading to it. This is
    /// usually much more readable while preserving all information.
    pub fn bdd_as_dot_string(&self, bdd: &Bdd, zero_pruned: bool) -> String {
        return bdd_as_dot_string(bdd, &self.var_names, zero_pruned);
    }

    /// **(internal)** Universal function to implement standard logical operators.
    ///
    /// The `terminal_lookup` function takes the two currently considered terminal BDD nodes (none
    /// if the node is not terminal) and returns a boolean if these two nodes can be evaluated
    /// by the function being implemented. For example, if one of the nodes is `false` and we are
    /// implementing `and`, we can immediately evaluate to `false`.
    fn apply<T>(&self, left: &Bdd, right: &Bdd, terminal_lookup: T) -> Bdd
        where T: Fn(Option<bool>, Option<bool>) -> Option<bool> {
        // Result holds the new BDD we are computing. Initially, `0` and `1` nodes are present. We
        // remember if the result is `false` or not (`is_not_empty`). If it is, we just provide
        // a `false` BDD instead of the result. This is easier than explicitly adding `1` later.
        let mut result: Bdd = Bdd::mk_true(self.num_vars);
        let mut is_not_empty = false;

        // Every node in `result` is inserted into `existing` - this ensures we have no duplicates.
        let mut existing: HashMap<BddNode, BddPointer> = HashMap::new();
        existing.insert(BddNode::mk_zero(self.num_vars), BddPointer::zero());
        existing.insert(BddNode::mk_one(self.num_vars), BddPointer::one());

        // Task is a pair of pointers into the `left` and `right` BDDs.
        #[derive(Eq, PartialEq, Hash, Copy, Clone)]
        struct Task { left: BddPointer, right: BddPointer };

        // `stack` is used to explore the two BDDs "side by side" in DFS-like manner. Each task
        // on the stack is a pair of nodes that needs to be fully processed before we are finished.
        let mut stack: Vec<Task> = Vec::new();
        stack.push(Task { left: left.root_pointer(), right: right.root_pointer() });

        // `finished` is a memoization cache of tasks which are already completed, since the same
        // combination of nodes can be often explored multiple times.
        let mut finished: HashMap<Task, BddPointer> = HashMap::new();

        while let Some(on_stack) = stack.last() {
            if finished.contains_key(on_stack) { stack.pop(); } else {  // skip finished tasks
                let (l, r) = (on_stack.left, on_stack.right);

                // Determine which variable we are conditioning on, moving from smallest to largest.
                let (l_v, r_v) = (left.var_of(&l), right.var_of(&r));
                let decision_var = min(l_v, r_v);

                // If the variable is the same as in the left/right decision node,
                // advance the exploration there. Otherwise, keep the pointers the same.
                let (l_low, l_high) = if l_v != decision_var { (l, l) } else {
                    (left.low_link_of(&l), left.high_link_of(&l))
                };
                let (r_low, r_high) = if r_v != decision_var { (r, r) } else {
                    (right.low_link_of(&r), right.high_link_of(&r))
                };

                // Two tasks which correspond to the two recursive sub-problems we need to solve.
                let comp_low = Task { left: l_low, right: r_low };
                let comp_high = Task { left: l_high, right: r_high };

                // Try to solve the tasks using terminal lookup table or from cache.
                let new_low = terminal_lookup(l_low.as_bool(), r_low.as_bool())
                    .map(BddPointer::from_bool).or_else(|| finished.get(&comp_low).cloned());
                let new_high = terminal_lookup(l_high.as_bool(), r_high.as_bool())
                    .map(BddPointer::from_bool).or_else(|| finished.get(&comp_high).cloned());

                // If both values are computed, mark this task as resolved.
                if let (Some(new_low), Some(new_high)) = (new_low, new_high) {
                    if new_low.is_one() || new_high.is_one() { is_not_empty = true }

                    if new_low == new_high {
                        // There is no decision, just skip this node and point to either child.
                        finished.insert(*on_stack, new_low);
                    } else {
                        // There is a decision here.
                        let node = BddNode::mk_node(
                            decision_var, new_low, new_high
                        );
                        if let Some(index) = existing.get(&node) {
                            // Node already exists, just make it a result of this computation.
                            finished.insert(*on_stack, *index);
                        } else {
                            // Node does not exist, it needs to be pushed to result.
                            result.push_node(node);
                            existing.insert(node, result.root_pointer());
                            finished.insert(*on_stack, result.root_pointer());
                        }
                    }
                    stack.pop();    // Mark as resolved.
                } else {
                    // Otherwise, if either value is unknown, push it to the stack.
                    if new_low.is_none() { stack.push(comp_low); }
                    if new_high.is_none() { stack.push(comp_high); }
                }
            }
        }

        return if is_not_empty { result } else { self.mk_false() }
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

    /// Similar to make_variable, but allows creating multiple variables at the same time.
    pub fn make_variables(&mut self, names: Vec<&str>) -> Vec<BddVariable> {
        return names.into_iter().map(|name| self.make_variable(name)).collect();
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
        builder.make_variables(vec!["v1", "v2", "v3", "v4", "v5"]);
        return builder.build();
    }

    fn v1() -> BddVariable { return BddVariable(0); }
    fn v2() -> BddVariable { return BddVariable(1); }
    fn v3() -> BddVariable { return BddVariable(2); }
    fn v4() -> BddVariable { return BddVariable(3); }

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
    fn bdd_universe_anonymous() {
        let universe = BddUniverse::new_anonymous(5);
        assert_eq!(Some(BddVariable(0)), universe.var_by_name("x_0"));
        assert_eq!(Some(BddVariable(1)), universe.var_by_name("x_1"));
        assert_eq!(Some(BddVariable(2)), universe.var_by_name("x_2"));
        assert_eq!(Some(BddVariable(3)), universe.var_by_name("x_3"));
        assert_eq!(Some(BddVariable(4)), universe.var_by_name("x_4"));
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
        let tt = universe.mk_true();
        let ff = universe.mk_false();
        let mut expected = universe.mk_true();
        expected.push_node(BddNode::mk_node(
            BddVariable(3), BddPointer::zero(), BddPointer::one()
        ));
        expected.push_node(BddNode::mk_node(
            BddVariable(2), BddPointer::one(), BddPointer(2)
        ));
        assert_eq!(expected, bdd!(universe, !bdd));
        assert_eq!(bdd, bdd!(universe, !(!bdd)));
        assert_eq!(tt, bdd!(universe, !ff));
        assert_eq!(ff, bdd!(universe, !tt));
    }

    #[test]
    fn bdd_universe_mk_and() {
        let universe = mk_universe_with_5_variables();
        let bdd = mk_small_test_bdd();  // v3 & !v4
        let v3 = universe.mk_var(&v3());
        let v4 = universe.mk_var(&v4());
        let tt = universe.mk_true();
        let ff = universe.mk_false();
        assert_eq!(bdd, bdd!(universe, v3 & (!v4)));
        assert_eq!(bdd, bdd!(universe, tt & bdd));
        assert_eq!(bdd, bdd!(universe, bdd & tt));
        assert_eq!(ff, bdd!(universe, ff & bdd));
        assert_eq!(ff, bdd!(universe, bdd & ff));
        assert_eq!(bdd, bdd!(universe, bdd & bdd));
    }

    #[test]
    fn bdd_universe_mk_or() {
        let universe = mk_universe_with_5_variables();
        let bdd = mk_small_test_bdd();  // v3 & !v4
        let v3 = universe.mk_var(&v3());
        let v4 = universe.mk_var(&v4());
        let tt = universe.mk_true();
        let ff = universe.mk_false();
        assert_eq!(bdd, bdd!(universe, !((!v3) | v4))); // !(!v3 | v4) <=> v3 & !v4
        assert_eq!(tt, bdd!(universe, tt | bdd));
        assert_eq!(tt, bdd!(universe, bdd | tt));
        assert_eq!(bdd, bdd!(universe, ff | bdd));
        assert_eq!(bdd, bdd!(universe, bdd | ff));
        assert_eq!(bdd, bdd!(universe, bdd | bdd));
    }

    #[test]
    fn bdd_universe_mk_xor() {
        let universe = mk_universe_with_5_variables();
        let bdd = mk_small_test_bdd();  // v3 & !v4
        let v3 = universe.mk_var(&v3());
        let v4 = universe.mk_var(&v4());
        let tt = universe.mk_true();
        let ff = universe.mk_false();

        assert_eq!(bdd!(universe, !bdd), bdd!(universe, tt ^ bdd));
        assert_eq!(bdd!(universe, !bdd), bdd!(universe, bdd ^ tt));
        assert_eq!(ff, bdd!(universe, bdd ^ bdd));
        assert_eq!(bdd, bdd!(universe, ff ^ bdd));
        assert_eq!(bdd, bdd!(universe, bdd ^ ff));
        assert_eq!(bdd, bdd!(universe, v3 & (v3 ^ v4)));
    }

    #[test]
    fn bdd_universe_mk_imp() {
        let universe = mk_universe_with_5_variables();
        let bdd = mk_small_test_bdd();  // v3 & !v4
        let v3 = universe.mk_var(&v3());
        let v4 = universe.mk_var(&v4());
        let tt = universe.mk_true();
        let ff = universe.mk_false();

        assert_eq!(tt, bdd!(universe, ff => bdd));
        assert_eq!(bdd!(universe, !bdd), bdd!(universe, bdd => ff));
        assert_eq!(bdd, bdd!(universe, tt => bdd));
        assert_eq!(tt, bdd!(universe, bdd => tt));
        assert_eq!(tt, bdd!(universe, bdd => bdd));
        assert_eq!(bdd, bdd!(universe, !(v3 => v4)));  // !(v3 => v4) <=> v3 & !v4
    }

    #[test]
    fn bdd_universe_mk_iff() {
        let universe = mk_universe_with_5_variables();
        let bdd = mk_small_test_bdd();  // v3 & !v4
        let v3 = universe.mk_var(&v3());
        let v4 = universe.mk_var(&v4());
        let tt = universe.mk_true();
        let ff = universe.mk_false();

        assert_eq!(bdd, bdd!(universe, bdd <=> tt));
        assert_eq!(bdd, bdd!(universe, tt <=> bdd));
        assert_eq!(bdd!(universe, !bdd), bdd!(universe, ff <=> bdd));
        assert_eq!(bdd!(universe, !bdd), bdd!(universe, bdd <=> ff));
        assert_eq!(tt, bdd!(universe, bdd <=> bdd));
        assert_eq!(bdd, bdd!(universe, v3 & (!(v4 <=> v3))));
    }

    #[test]
    fn bdd_universe_constants() {
        let bdd = mk_universe_with_5_variables();
        let tt = bdd.mk_true();
        let ff = bdd.mk_false();
        assert!(tt.is_true());
        assert!(ff.is_false());
        assert_eq!(ff, bdd!(bdd, (tt & ff)));
        assert_eq!(tt, bdd!(bdd, (tt | ff)));
        assert_eq!(tt, bdd!(bdd, (tt ^ ff)));
        assert_eq!(ff, bdd!(bdd, (tt => ff)));
        assert_eq!(ff, bdd!(bdd, (tt <=> ff)));
    }

    #[test]
    fn simple_identities_syntactic() {
        let bdd = mk_universe_with_5_variables();
        let a = bdd.mk_var(&v1());
        let tt = bdd.mk_true();
        let ff = bdd.mk_false();

        assert_eq!(ff, bdd!(bdd, (ff & a)));
        assert_eq!(a, bdd!(bdd, (ff | a)));
        assert_eq!(tt, bdd!(bdd, (ff => a)));
        assert_eq!(bdd!(bdd, !a), bdd!(bdd, (a => ff)));
        assert_eq!(tt, bdd!(bdd, (a => a)));
    }

    #[test]
    fn bdd_universe_de_morgan() {
        // !(a * b * !c) <=> (!a + !b + c)
        let bdd = mk_universe_with_5_variables();
        let v1 = bdd.mk_var(&v1());
        let v2 = bdd.mk_var(&v2());
        let v3 = bdd.mk_var(&v3());

        let left = bdd!(bdd, !(v1 & (v2 & (!v3))));
        let right = bdd!(bdd, ((!v1) | (!v2)) | v3);

        assert_eq!(left, right);
        assert!(bdd!(bdd, left <=> right).is_true());
    }

    #[test]
    fn nontrivial_identity_syntactic() {
        // dnf (!a * !b * !c) + (!a * !b * c) + (!a * b * c) + (a * !b * c) + (a * b * !c)
        //                                    <=>
        // cnf            !(!a * b * !c) * !(a * !b * !c) * !(a * b * c)
        let bdd = mk_universe_with_5_variables();
        let a = bdd.mk_var(&v1());
        let b = bdd.mk_var(&v2());
        let c = bdd.mk_var(&v3());

        let d1 = bdd!(bdd, ((!a) & (!b)) & (!c));
        let d2 = bdd!(bdd, ((!a) & (!b)) & c);
        let d3 = bdd!(bdd, ((!a) & b) & c);
        let d4 = bdd!(bdd, (a & (!b)) & c);
        let d5 = bdd!(bdd, (a & b) & (!c));

        let c1 = bdd!(bdd, (a | (!b)) | c);
        let c2 = bdd!(bdd, ((!a) | b) | c);
        let c3 = bdd!(bdd, ((!a) | (!b)) | (!c));

        let cnf = bdd!(bdd, ((c1 & c2) & c3));
        let dnf = bdd!(bdd, ((((d1 | d2) | d3) | d4) | d5));

        assert_eq!(cnf, dnf);
        assert!(bdd!(bdd, (cnf <=> dnf)).is_true());
    }

    #[test]
    fn bdd_macro_test() {
        let universe = mk_universe_with_5_variables();
        let v1 = universe.mk_var(&v1());
        let v2 = universe.mk_var(&v2());
        assert_eq!(universe.mk_not(&v1), bdd!(universe, !v1));
        assert_eq!(universe.mk_and(&v1, &v2), bdd!(universe, v1 & v2));
        assert_eq!(universe.mk_or(&v1, &v2), bdd!(universe, v1 | v2));
        assert_eq!(universe.mk_xor(&v1, &v2), bdd!(universe, v1 ^ v2));
        assert_eq!(universe.mk_imp(&v1, &v2), bdd!(universe, v1 => v2));
        assert_eq!(universe.mk_iff(&v1, &v2), bdd!(universe, v1 <=> v2));
    }

}