//! **(internal)** Provides essential operations for safely creating and manipulating BDDs.
//!
//! TODO: Describe BDD manipulation algorithms.

use super::bdd_node::BddNode;
use super::bdd_pointer::BddPointer;
use super::{Bdd, BddValuation, BddVariable};
use crate::bdd_dot_printer::bdd_to_dot_string;
use crate::parse_boolean_formula;
use std::cmp::min;
use std::collections::HashMap;

mod bdd_universe_builder_impl;

#[cfg(test)]
mod tests_bdd_universe_basic_logic;

#[cfg(test)]
mod tests_bdd_universe_fuzzing;

use crate::BooleanFormula;
pub use bdd_universe_builder_impl::BddUniverseBuilder;

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
    var_index_mapping: HashMap<String, u16>,
}

// TODO: separate this huge impl block into smaller submodules
impl BddUniverse {
    /// Create a new BDD universe with anonymous variables $(x_1, \ldots, x_n)$ where $n$ is
    /// the `num_vars` parameter.
    pub fn new_anonymous(num_vars: u16) -> BddUniverse {
        if num_vars >= (std::u16::MAX - 1) {
            panic!(
                "BDD universe is too large. There can be at most {} variables.",
                std::u16::MAX - 1
            )
        }
        return BddUniverse {
            num_vars,
            var_names: (0..num_vars).map(|i| format!("x_{}", i)).collect(),
            var_index_mapping: (0..num_vars).map(|i| (format!("x_{}", i), i)).collect(),
        };
    }

    /// Create a new BDD universe with the given named variables. Same as using the
    /// `BddUniverseBuilder` with this name vector, but the `BddVariable` objects need to be
    /// acquired after creating the universe.
    pub fn new(vars: Vec<&str>) -> BddUniverse {
        let mut builder = BddUniverseBuilder::new();
        builder.make_variables(vars);
        return builder.build();
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

    /// Provides a vector of all BDD variables in this universe.
    pub fn variables(&self) -> Vec<BddVariable> {
        return (0..self.num_vars).map(|i| BddVariable(i)).collect();
    }

    /// Obtain the name of a specific BDD variable.
    pub fn name_of(&self, variable: BddVariable) -> String {
        return self.var_names[variable.0 as usize].clone();
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
    pub fn mk_var(&self, var: BddVariable) -> Bdd {
        if cfg!(feature = "shields_up") && var.0 >= self.num_vars {
            panic!("Variable {:?} is not in this universe.", var);
        }
        let mut bdd = self.mk_true();
        bdd.push_node(BddNode::mk_node(
            var.clone(),
            BddPointer::zero(),
            BddPointer::one(),
        ));
        return bdd;
    }

    /// Create a BDD corresponding to the $\neg v$ formula where `v` is a specific variable in
    /// this universe.
    ///
    /// *Pre:* `var` is a valid variable in this universe.
    pub fn mk_not_var(&self, var: BddVariable) -> Bdd {
        if cfg!(feature = "shields_up") && var.0 >= self.num_vars {
            panic!("Variable {:?} is not in this universe.", var);
        }
        let mut bdd = self.mk_true();
        bdd.push_node(BddNode::mk_node(
            var.clone(),
            BddPointer::one(),
            BddPointer::zero(),
        ));
        return bdd;
    }

    /// Create a BDD corresponding to the $v$ formula where `v` is a variable in this universe.
    ///
    /// *Pre:* `var` is a valid variable in this universe.
    pub fn mk_var_by_name(&self, var: &str) -> Bdd {
        return self
            .var_by_name(var)
            .map(|var| self.mk_var(var))
            .unwrap_or_else(|| panic!("Variable {} is known present in this universe.", var));
    }

    /// Create a BDD corresponding to the $\neg v$ formula where `v` is a variable in this universe.
    ///
    /// *Pre:* `var` is a valid variable in this universe.
    pub fn mk_not_var_by_name(&self, var: &str) -> Bdd {
        return self
            .var_by_name(var)
            .map(|var| self.mk_not_var(var))
            .unwrap_or_else(|| panic!("Variable {} is not known in this universe.", var));
    }

    /// Create a BDD corresponding to the $\neg \phi$ formula, where $\phi$ is a specific
    /// formula given by a BDD.
    pub fn mk_not(&self, phi: &Bdd) -> Bdd {
        if cfg!(shields_up) && phi.num_vars() != self.num_vars {
            panic!(
                "BDD is not from this universe. {} != {}",
                phi.num_vars(),
                self.num_vars
            );
        }
        if phi.is_true() {
            return self.mk_false();
        } else if phi.is_false() {
            return self.mk_true();
        } else {
            let mut result_vector = phi.0.clone();
            for i in 2..result_vector.len() {
                // skip terminals
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
            _ => None,
        });
    }

    /// Create a BDD corresponding to the $\phi \lor \psi$ formula, where $\phi$ and $\psi$
    /// are two specific BDDs.
    pub fn mk_or(&self, left: &Bdd, right: &Bdd) -> Bdd {
        return self.apply(left, right, |l, r| match (l, r) {
            (Some(false), Some(false)) => Some(false),
            (Some(true), _) => Some(true),
            (_, Some(true)) => Some(true),
            _ => None,
        });
    }

    /// Create a BDD corresponding to the $\phi \Rightarrow \psi$ formula, where $\phi$ and $\psi$
    /// are two specific BDDs.
    pub fn mk_imp(&self, left: &Bdd, right: &Bdd) -> Bdd {
        return self.apply(left, right, |l, r| match (l, r) {
            (Some(true), Some(false)) => Some(false),
            (Some(false), _) => Some(true),
            (_, Some(true)) => Some(true),
            _ => None,
        });
    }

    /// Create a BDD corresponding to the $\phi \Leftrightarrow \psi$ formula, where $\phi$ and $\psi$
    /// are two specific BDDs.
    pub fn mk_iff(&self, left: &Bdd, right: &Bdd) -> Bdd {
        return self.apply(left, right, |l, r| match (l, r) {
            (Some(l), Some(r)) => Some(l == r),
            _ => None,
        });
    }

    /// Create a BDD corresponding to the $\phi \oplus \psi$ formula, where $\phi$ and $\psi$
    /// are two specific BDDs.
    pub fn mk_xor(&self, left: &Bdd, right: &Bdd) -> Bdd {
        return self.apply(left, right, |l, r| match (l, r) {
            (Some(l), Some(r)) => Some(l ^ r),
            _ => None,
        });
    }

    /// Convert a BDD object to a string representing its graph as a .dot file.
    ///
    /// Use `zero_pruned` to remove `0` terminal and all edges leading to it. This is
    /// usually much more readable while preserving all information.
    pub fn bdd_to_dot_string(&self, bdd: &Bdd, zero_pruned: bool) -> String {
        return bdd_to_dot_string(bdd, &self.var_names, zero_pruned);
    }

    /// **(internal)** Universal function to implement standard logical operators.
    ///
    /// The `terminal_lookup` function takes the two currently considered terminal BDD nodes (none
    /// if the node is not terminal) and returns a boolean if these two nodes can be evaluated
    /// by the function being implemented. For example, if one of the nodes is `false` and we are
    /// implementing `and`, we can immediately evaluate to `false`.
    fn apply<T>(&self, left: &Bdd, right: &Bdd, terminal_lookup: T) -> Bdd
    where
        T: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    {
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
        struct Task {
            left: BddPointer,
            right: BddPointer,
        };

        // `stack` is used to explore the two BDDs "side by side" in DFS-like manner. Each task
        // on the stack is a pair of nodes that needs to be fully processed before we are finished.
        let mut stack: Vec<Task> = Vec::new();
        stack.push(Task {
            left: left.root_pointer(),
            right: right.root_pointer(),
        });

        // `finished` is a memoization cache of tasks which are already completed, since the same
        // combination of nodes can be often explored multiple times.
        let mut finished: HashMap<Task, BddPointer> = HashMap::new();

        while let Some(on_stack) = stack.last() {
            if finished.contains_key(on_stack) {
                stack.pop();
            } else {
                // skip finished tasks
                let (l, r) = (on_stack.left, on_stack.right);

                // Determine which variable we are conditioning on, moving from smallest to largest.
                let (l_v, r_v) = (left.var_of(l), right.var_of(r));
                let decision_var = min(l_v, r_v);

                // If the variable is the same as in the left/right decision node,
                // advance the exploration there. Otherwise, keep the pointers the same.
                let (l_low, l_high) = if l_v != decision_var {
                    (l, l)
                } else {
                    (left.low_link_of(l), left.high_link_of(l))
                };
                let (r_low, r_high) = if r_v != decision_var {
                    (r, r)
                } else {
                    (right.low_link_of(r), right.high_link_of(r))
                };

                // Two tasks which correspond to the two recursive sub-problems we need to solve.
                let comp_low = Task {
                    left: l_low,
                    right: r_low,
                };
                let comp_high = Task {
                    left: l_high,
                    right: r_high,
                };

                // Try to solve the tasks using terminal lookup table or from cache.
                let new_low = terminal_lookup(l_low.as_bool(), r_low.as_bool())
                    .map(BddPointer::from_bool)
                    .or_else(|| finished.get(&comp_low).cloned());
                let new_high = terminal_lookup(l_high.as_bool(), r_high.as_bool())
                    .map(BddPointer::from_bool)
                    .or_else(|| finished.get(&comp_high).cloned());

                // If both values are computed, mark this task as resolved.
                if let (Some(new_low), Some(new_high)) = (new_low, new_high) {
                    if new_low.is_one() || new_high.is_one() {
                        is_not_empty = true
                    }

                    if new_low == new_high {
                        // There is no decision, just skip this node and point to either child.
                        finished.insert(*on_stack, new_low);
                    } else {
                        // There is a decision here.
                        let node = BddNode::mk_node(decision_var, new_low, new_high);
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
                    stack.pop(); // Mark as resolved.
                } else {
                    // Otherwise, if either value is unknown, push it to the stack.
                    if new_low.is_none() {
                        stack.push(comp_low);
                    }
                    if new_high.is_none() {
                        stack.push(comp_high);
                    }
                }
            }
        }

        return if is_not_empty {
            result
        } else {
            self.mk_false()
        };
    }

    /// Evaluate a BDD for a specific valuation of variables.
    ///
    /// *Pre:* valuation needs to have the same number of variables as this universe.
    pub fn eval_in(&self, formula: &Bdd, valuation: &BddValuation) -> bool {
        if cfg!(feature = "shields_up") && valuation.num_vars() != self.num_vars {
            panic!(
                "Universe has {} variables, but valuation has {}.",
                self.num_vars,
                valuation.num_vars()
            )
        }
        let mut node = formula.root_pointer();
        while !node.is_terminal() {
            let var = formula.var_of(node);
            node = if valuation.value(&var) {
                formula.high_link_of(node)
            } else {
                formula.low_link_of(node)
            }
        }
        return node.is_one();
    }

    /// Use a Boolean formula to create the corresponding BDD. Variable names in the formula
    /// must match the names in this universe, otherwise the function panics.
    pub fn eval_formula(&self, formula: &BooleanFormula) -> Bdd {
        return match formula {
            BooleanFormula::Variable(name) => self.mk_var(self.var_by_name(name).unwrap()),
            BooleanFormula::Not(inner) => self.mk_not(&self.eval_formula(inner)),
            BooleanFormula::And(l, r) => self.mk_and(&self.eval_formula(l), &self.eval_formula(r)),
            BooleanFormula::Or(l, r) => self.mk_or(&self.eval_formula(l), &self.eval_formula(r)),
            BooleanFormula::Xor(l, r) => self.mk_xor(&self.eval_formula(l), &self.eval_formula(r)),
            BooleanFormula::Imp(l, r) => self.mk_imp(&self.eval_formula(l), &self.eval_formula(r)),
            BooleanFormula::Iff(l, r) => self.mk_iff(&self.eval_formula(l), &self.eval_formula(r)),
        };
    }

    /// Parse the given string as Boolean formula and evaluate it into a BDD.
    ///
    /// Panics if the expression cannot be parsed successfully or when it uses names which
    /// are not valid in this universe.
    pub fn eval_expression(&self, expression: &str) -> Bdd {
        if let Ok(formula) = parse_boolean_formula(expression) {
            return self.eval_formula(&formula);
        } else {
            panic!("Cannot parse expression {}", expression);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{bdd, parse_boolean_formula};

    pub fn mk_universe_with_5_variables() -> BddUniverse {
        let mut builder = BddUniverseBuilder::new();
        builder.make_variables(vec!["v1", "v2", "v3", "v4", "v5"]);
        return builder.build();
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
        mk_universe_with_5_variables().mk_var(BddVariable(6));
    }

    #[test]
    #[should_panic]
    fn bdd_universe_mk_not_var_invalid_id() {
        mk_universe_with_5_variables().mk_not_var(BddVariable(6));
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
    fn bdd_universe_eval() {
        let universe = BddUniverse::new_anonymous(2);
        let v1 = universe.var_by_name("x_0").unwrap();
        let v1 = universe.mk_var(v1);
        let v2 = universe.var_by_name("x_1").unwrap();
        let v2 = universe.mk_var(v2);
        let bdd = bdd!(universe, v1 & (!v2));
        assert_eq!(
            true,
            universe.eval_in(&bdd, &BddValuation::new(vec![true, false]))
        );
        assert_eq!(
            false,
            universe.eval_in(&bdd, &BddValuation::new(vec![true, true]))
        );
        assert_eq!(
            false,
            universe.eval_in(&bdd, &BddValuation::new(vec![false, false]))
        );
        assert_eq!(
            false,
            universe.eval_in(&bdd, &BddValuation::new(vec![false, false]))
        );
    }

    #[test]
    #[should_panic]
    fn bdd_universe_eval_invalid() {
        let universe = BddUniverse::new_anonymous(2);
        let tt = universe.mk_true();
        universe.eval_in(&tt, &BddValuation::new(vec![true, true, true]));
    }

    #[test]
    fn bdd_universe_eval_boolean_formula() {
        let universe = BddUniverse::new_anonymous(5);
        let formula =
            parse_boolean_formula("((x_0 & !!x_1) => (!(x_2 | (!!x_0 & x_1)) <=> (x_3 ^ x_4)))")
                .unwrap();
        let x_0 = universe.mk_var_by_name("x_0");
        let x_1 = universe.mk_var_by_name("x_1");
        let x_2 = universe.mk_var_by_name("x_2");
        let x_3 = universe.mk_var_by_name("x_3");
        let x_4 = universe.mk_var_by_name("x_4");

        let expected =
            bdd!(universe, ((x_0 & (!(!x_1))) => ((!(x_2 | ((!(!x_0)) & x_1))) <=> (x_3 ^ x_4))));
        let evaluated = universe.eval_formula(&formula);

        assert_eq!(expected, evaluated);
    }

}
