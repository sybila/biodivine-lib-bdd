use crate::boolean_expression::BooleanExpression;
use crate::boolean_expression::BooleanExpression::Variable;
use crate::*;
use num_bigint::BigInt;
use std::cmp::{max, min};
use std::iter::Map;
use std::ops::Range;
use std::slice::Iter;

/// Several useful (mostly internal) low-level utility methods for `Bdd`s.
impl Bdd {
    /// The number of nodes in this `Bdd`. (Do not confuse with cardinality)
    pub fn size(&self) -> usize {
        self.0.len()
    }

    /// Number of variables in the corresponding `BddVariableSet`.
    pub fn num_vars(&self) -> u16 {
        // Assert: every BDD is not empty - it has at least the terminal zero node.
        self.0[0].var.0
    }

    /// Change the number of variables tracked by this BDD.
    ///
    /// # Safety
    ///
    /// This operation is "unsafe", as it makes the BDD incompatible with the original
    /// `BddVariableSet` and overall can break compatibility of BDD operations. However,
    /// the operation will not allow you to create an invalid BDD. We still check that the
    /// `new_value` covers at least the highest used variable in the BDD, and if the property is
    /// broken, the operation panics.
    pub unsafe fn set_num_vars(&mut self, new_value: u16) {
        for node in self.nodes().skip(2) {
            if node.var.0 >= new_value {
                panic!(
                    "BDD contains `{:?}`, which is invalid with variable count `{}`.",
                    node.var, new_value
                );
            }
        }
        // If the check has passed, we can update the first two nodes.
        self.0[0].var = BddVariable(new_value);
        if self.0.len() > 1 {
            self.0[1].var = BddVariable(new_value);
        }
    }

    /// The same as [Bdd::rename_variable], but applies the renaming across several variables.
    /// Each node is renamed at most one (i.e. if `v1` renames to `v2` and `v2` renames to `v3`,
    /// a decision node based on `v1` only renames to `v2`).
    ///
    /// # Safety
    ///
    /// This operation is "unsafe" because it can change the BDD in a "non-semantic" way. However,
    /// as long as the operation does not panic, the result will be a valid BDD.
    pub unsafe fn rename_variables(&mut self, permutation: &HashMap<BddVariable, BddVariable>) {
        let mut current_vars = Vec::from_iter(self.support_set());

        if current_vars.is_empty() {
            // This is a "trivial" BDD that does not depend on anything. We can rename this
            // however we want because it's not going to change anything.
            return;
        }

        current_vars.sort();
        let vars_after_permutation = current_vars
            .iter()
            .map(|it| permutation.get(it).cloned().unwrap_or(*it))
            .collect::<Vec<_>>();

        // Safety check: Every new variable is valid, and the variables will be still
        // sorted after the permutation.
        assert!(vars_after_permutation
            .iter()
            .all(|it| it.0 < self.num_vars()));
        for i in 0..(vars_after_permutation.len() - 1) {
            assert!(vars_after_permutation[i] < vars_after_permutation[i + 1]);
        }

        for node in self.0.iter_mut() {
            if let Some(new) = permutation.get(&node.var) {
                node.var = *new;
            }
        }
    }

    /// Change the provided variable ID to the new one. This change does not perform any
    /// structural changes to the BDD itself. As such, it is only valid when the BDD does not
    /// depend on any variables that are between `old_id` and `new_id`. Furthermore, `old_id`
    /// and `new_id` must be admissible in this BDD. The method panics otherwise.
    ///
    /// # Safety
    ///
    /// This operation is "unsafe" because it can change the BDD in a "non-semantic" way. However,
    /// as long as the operation does not panic, the result will be a valid BDD.
    pub unsafe fn rename_variable(&mut self, old_id: BddVariable, new_id: BddVariable) {
        assert!(old_id.0 < self.num_vars());
        assert!(new_id.0 < self.num_vars());

        if old_id == new_id {
            return;
        }

        let support_set = self.support_set();
        let low = min(old_id.0, new_id.0);
        let high = max(old_id.0, new_id.0);
        for i in (low + 1)..high {
            if support_set.contains(&BddVariable(i)) {
                panic!("Cannot rename {old_id} to {new_id} due to the presence of {i}.");
            }
        }

        if support_set.contains(&new_id) {
            panic!("Cannot rename {old_id} to {new_id} due to the presence of {new_id}.");
        }

        for node in &mut self.0 {
            if node.var == old_id {
                node.var = new_id;
            }
        }
    }

    /// If this `Bdd` is a constant, convert it to `bool`, otherwise return `None`.
    pub fn as_bool(&self) -> Option<bool> {
        if self.is_true() {
            Some(true)
        } else if self.is_false() {
            Some(false)
        } else {
            None
        }
    }

    /// True if this `Bdd` is exactly the `true` formula.
    pub fn is_true(&self) -> bool {
        self.0.len() == 2
    }

    /// True if this `Bdd` is exactly the `false` formula.
    pub fn is_false(&self) -> bool {
        self.0.len() == 1
    }

    pub fn exact_cardinality(&self) -> BigInt {
        let zero = BigInt::from(0);
        let one = BigInt::from(1);
        if self.is_false() {
            return zero;
        }
        let mut cache = vec![None; self.0.len()];
        cache[0] = Some(zero);
        cache[1] = Some(one.clone());
        let mut stack: Vec<BddPointer> = vec![self.root_pointer()];
        while let Some(node) = stack.last() {
            if cache[node.0 as usize].is_some() {
                stack.pop();
            } else {
                let low = self.low_link_of(*node);
                let high = self.high_link_of(*node);
                let low_var = self.var_of(low).0;
                let high_var = self.var_of(high).0;
                let node_var = self.var_of(*node).0;
                let low = low.0 as usize;
                let high = high.0 as usize;

                if let (Some(cache_low), Some(cache_high)) = (&cache[low], &cache[high]) {
                    let low_card = cache_low * (one.clone() << (low_var - node_var - 1));
                    let high_card = cache_high * (one.clone() << (high_var - node_var - 1));
                    cache[node.0 as usize] = Some(low_card + high_card);
                    stack.pop();
                } else {
                    if cache[low].is_none() {
                        stack.push(BddPointer(low as u32));
                    }
                    if cache[high].is_none() {
                        stack.push(BddPointer(high as u32));
                    }
                }
            }
        }
        let last_var = self.0.last().unwrap().var.0;
        cache.pop().flatten().unwrap() * (one << last_var)
    }

    /// Approximately computes the number of valuations satisfying the formula given
    /// by this `Bdd`.
    pub fn cardinality(&self) -> f64 {
        if self.is_false() {
            return 0.0;
        }
        let mut cache = vec![None; self.0.len()];
        cache[0] = Some(0.0);
        cache[1] = Some(1.0);
        let mut stack: Vec<BddPointer> = vec![self.root_pointer()];
        while let Some(node) = stack.last() {
            if cache[node.0 as usize].is_some() {
                stack.pop();
            } else {
                let low = self.low_link_of(*node);
                let high = self.high_link_of(*node);
                let low_var = self.var_of(low).0;
                let high_var = self.var_of(high).0;
                let node_var = self.var_of(*node).0;
                let low = low.0 as usize;
                let high = high.0 as usize;

                if cache[low].is_some() && cache[high].is_some() {
                    let low_cardinality =
                        cache[low].unwrap() * 2.0_f64.powi((low_var - node_var - 1) as i32);
                    let high_cardinality =
                        cache[high].unwrap() * 2.0_f64.powi((high_var - node_var - 1) as i32);
                    cache[node.0 as usize] = Some(low_cardinality + high_cardinality);
                    stack.pop();
                } else {
                    if cache[low].is_none() {
                        stack.push(BddPointer(low as u32));
                    }
                    if cache[high].is_none() {
                        stack.push(BddPointer(high as u32));
                    }
                }
            }
        }
        let r = cache.last().unwrap().unwrap() * 2.0_f64.powi(self.0.last().unwrap().var.0 as i32);
        if r.is_nan() {
            f64::INFINITY
        } else {
            r
        }
    }

    /// Computes the number of satisfying clauses that are represented within this BDD.
    ///
    /// The result should correspond to the number of items returned by the [Bdd::sat_clauses]
    /// iterator.
    pub fn exact_clause_cardinality(&self) -> BigInt {
        let zero = BigInt::from(0);
        let one = BigInt::from(1);
        if self.is_false() {
            return zero;
        }
        let mut cache = vec![None; self.0.len()];
        cache[0] = Some(zero);
        cache[1] = Some(one.clone());
        let mut stack: Vec<BddPointer> = vec![self.root_pointer()];
        while let Some(node) = stack.last() {
            if cache[node.0 as usize].is_some() {
                stack.pop();
            } else {
                let low = self.low_link_of(*node);
                let high = self.high_link_of(*node);
                let low = low.0 as usize;
                let high = high.0 as usize;

                if let (Some(cache_low), Some(cache_high)) = (&cache[low], &cache[high]) {
                    cache[node.0 as usize] = Some(cache_low + cache_high);
                    stack.pop();
                } else {
                    if cache[low].is_none() {
                        stack.push(BddPointer(low as u32));
                    }
                    if cache[high].is_none() {
                        stack.push(BddPointer(high as u32));
                    }
                }
            }
        }
        cache.pop().flatten().unwrap()
    }

    /// If the `Bdd` is satisfiable, return some `BddValuation` that satisfies the `Bdd`.
    pub fn sat_witness(&self) -> Option<BddValuation> {
        if self.is_false() {
            return None;
        }
        let mut valuation: Vec<bool> = vec![false; self.num_vars() as usize];
        let mut find = BddPointer::one(); // index 1 is the true node

        // Run through the graph backwards, always looking for a parent of a specific node.
        // Initially, that node is a `1` terminal. Since parents are stored after children,
        // we know we will always find the parent.
        for node in self.pointers() {
            if node.is_terminal() {
                continue;
            }
            if self.low_link_of(node) == find {
                valuation[self.var_of(node).0 as usize] = false;
                find = node;
            }
            if self.high_link_of(node) == find {
                valuation[self.var_of(node).0 as usize] = true;
                find = node;
            }
        }

        Some(BddValuation::new(valuation))
    }

    /// Convert this `Bdd` to a `BooleanExpression` (using the variable names from the given
    /// `BddVariableSet`).
    ///
    pub fn to_boolean_expression(&self, variables: &BddVariableSet) -> BooleanExpression {
        if self.is_false() {
            return BooleanExpression::Const(false);
        }
        if self.is_true() {
            return BooleanExpression::Const(true);
        }

        let mut results: Vec<BooleanExpression> = Vec::with_capacity(self.0.len());
        results.push(BooleanExpression::Const(false)); // fake terminals
        results.push(BooleanExpression::Const(true)); // never used
        for node in self.0.iter().skip(2) {
            // skip terminals
            let node_var = node.var;
            let var_name = variables.var_names[node_var.0 as usize].clone();

            let low_link = node.low_link;
            let high_link = node.high_link;
            let expression = if low_link.is_terminal() && high_link.is_terminal() {
                // Both links are terminal, which means this is an exactly determined variable
                if high_link.is_one() && low_link.is_zero() {
                    Variable(var_name)
                } else if high_link.is_zero() && low_link.is_one() {
                    BooleanExpression::Not(Box::new(Variable(var_name)))
                } else {
                    panic!("Invalid node {:?} in bdd {:?}.", node, self.0);
                }
            } else if low_link.is_terminal() {
                if low_link.is_zero() {
                    // a & high
                    BooleanExpression::And(
                        Box::new(Variable(var_name)),
                        Box::new(results[high_link.0 as usize].clone()),
                    )
                } else {
                    // !a | high
                    BooleanExpression::Or(
                        Box::new(BooleanExpression::Not(Box::new(Variable(var_name)))),
                        Box::new(results[high_link.0 as usize].clone()),
                    )
                }
            } else if high_link.is_terminal() {
                if high_link.is_zero() {
                    // !a & low
                    BooleanExpression::And(
                        Box::new(BooleanExpression::Not(Box::new(Variable(var_name)))),
                        Box::new(results[low_link.0 as usize].clone()),
                    )
                } else {
                    // a | low
                    BooleanExpression::Or(
                        Box::new(Variable(var_name)),
                        Box::new(results[low_link.0 as usize].clone()),
                    )
                }
            } else {
                // (a & high) | (!a & low)
                BooleanExpression::Or(
                    Box::new(BooleanExpression::And(
                        Box::new(Variable(var_name.clone())),
                        Box::new(results[high_link.0 as usize].clone()),
                    )),
                    Box::new(BooleanExpression::And(
                        Box::new(BooleanExpression::Not(Box::new(Variable(var_name)))),
                        Box::new(results[low_link.0 as usize].clone()),
                    )),
                )
            };
            results.push(expression);
        }

        results.pop().unwrap()
    }

    /// Pointer to the root of the decision diagram.
    pub fn root_pointer(&self) -> BddPointer {
        BddPointer::from_index(self.0.len() - 1)
    }

    /// Get the low link of the node at a specified location.
    pub fn low_link_of(&self, node: BddPointer) -> BddPointer {
        self.0[node.to_index()].low_link
    }

    /// Get the high link of the node at a specified location.
    pub fn high_link_of(&self, node: BddPointer) -> BddPointer {
        self.0[node.to_index()].high_link
    }

    /// Get the conditioning variable of the node at a specified location.
    ///
    /// Note that this also technically works for terminals, but the returned `BddVariable` is
    /// not valid in this `Bdd`.
    pub fn var_of(&self, node: BddPointer) -> BddVariable {
        self.0[node.to_index()].var
    }

    /// **(internal)** Create a new `Bdd` for the `false` formula.
    pub(crate) fn mk_false(num_vars: u16) -> Bdd {
        Bdd(vec![BddNode::mk_zero(num_vars)])
    }

    /// **(internal)** Create a new `Bdd` for the `true` formula.
    pub(crate) fn mk_true(num_vars: u16) -> Bdd {
        Bdd(vec![BddNode::mk_zero(num_vars), BddNode::mk_one(num_vars)])
    }

    pub(crate) fn mk_var(num_vars: u16, var: BddVariable) -> Bdd {
        let mut bdd = Self::mk_true(num_vars);
        bdd.push_node(BddNode::mk_node(var, BddPointer::zero(), BddPointer::one()));
        bdd
    }

    pub(crate) fn mk_not_var(num_vars: u16, var: BddVariable) -> Bdd {
        let mut bdd = Self::mk_true(num_vars);
        bdd.push_node(BddNode::mk_node(var, BddPointer::one(), BddPointer::zero()));
        bdd
    }

    pub(crate) fn mk_literal(num_vars: u16, var: BddVariable, value: bool) -> Bdd {
        if value {
            Self::mk_var(num_vars, var)
        } else {
            Self::mk_not_var(num_vars, var)
        }
    }

    pub(crate) fn mk_partial_valuation(num_vars: u16, valuation: &BddPartialValuation) -> Bdd {
        let mut bdd = Bdd::mk_true(num_vars);
        for (var, value) in valuation.to_values().into_iter().rev() {
            let node = if value {
                BddNode::mk_node(var, BddPointer::zero(), bdd.root_pointer())
            } else {
                BddNode::mk_node(var, bdd.root_pointer(), BddPointer::zero())
            };
            bdd.push_node(node);
        }

        bdd
    }

    /// **(internal)** Add a new node to an existing `Bdd`, making the new node the root of the `Bdd`.
    pub(crate) fn push_node(&mut self, node: BddNode) {
        self.0.push(node);
    }

    /// **(internal)** Create an iterator over all pointers of the `Bdd` (including terminals!).
    ///
    /// The iteration order is the same as the underlying representation, so you can expect
    /// terminals to be the first two nodes.
    pub(crate) fn pointers(&self) -> Map<Range<usize>, fn(usize) -> BddPointer> {
        (0..self.size()).map(BddPointer::from_index)
    }

    /// **(internal)** Create an iterator over all nodes of the `Bdd` (including terminals).
    pub(crate) fn nodes(&self) -> Iter<'_, BddNode> {
        self.0.iter()
    }

    /// Check if this `Bdd` represents a single valuation with all variables fixed to a
    /// specific value.
    ///
    /// This can be used for example to verify that a set represented by a `Bdd` is a singleton.
    pub fn is_valuation(&self) -> bool {
        // Note that this check works for any ordering of nodes in the BDD, but only
        // works if the BDD itself is canonical (i.e. no duplicates and redundant nodes).
        // If it is not canonical and the result is true, it is indeed a singleton, but
        // if the result is false, it may be just a non-canonical singleton with unnecessary nodes.
        let mut expected_variable: u16 = 0;
        let mut node = self.root_pointer();
        while !node.is_one() {
            if node.is_zero() {
                // This is only triggered for non-canonical BDDs.
                return false;
            }
            // The variables on the path should grow continuously.
            if self.var_of(node).0 != expected_variable {
                return false;
            } else {
                expected_variable += 1;
            }
            // One of the links must be zero, the other link follows the path.
            if self.low_link_of(node).is_zero() {
                node = self.high_link_of(node);
            } else if self.high_link_of(node).is_zero() {
                node = self.low_link_of(node);
            } else {
                return false;
            }
        }

        // We got to the terminal node, but we still need to check that some variable was not
        // skipped by the last edge that got us there.
        self.var_of(node).0 == expected_variable
    }

    /// Check if this `Bdd` represents a single *conjunctive* clause, i.e. that the formula
    /// represented by this `Bdd` is for example `x & !y & z & ...` (here `x`, `!y`, `z` are
    /// some positive/negative literals).
    pub fn is_clause(&self) -> bool {
        // Similar to `is_single_valuation`, this function only works for canonical BDDs,
        // regardless of node order, but can only output false negative for non-canonical BDDs.

        let mut node = self.root_pointer();
        while !node.is_one() {
            if node.is_zero() {
                return false;
            }

            if self.low_link_of(node).is_zero() {
                node = self.high_link_of(node);
            } else if self.high_link_of(node).is_zero() {
                node = self.low_link_of(node);
            } else {
                return false;
            }
        }

        true
    }

    /// Compute the number of BDD nodes that condition on individual variables. If the variable
    /// does not appear in the BDD, it will not be contained in the result (i.e. keys of the
    /// returned map are the support set of the BDD).
    pub fn size_per_variable(&self) -> HashMap<BddVariable, usize> {
        let mut counts = HashMap::new();
        for node in self.pointers().skip(2) {
            let var = self.var_of(node);
            if let Some(reference) = counts.get_mut(&var) {
                *reference += 1;
            } else {
                counts.insert(var, 1);
            }
        }

        counts
    }

    /// Return the set of all variables that actually appear as decision variables in this BDD.
    pub fn support_set(&self) -> HashSet<BddVariable> {
        self.nodes().skip(2).map(|node| node.var).collect()
    }

    /// Return whether the variable actually appears as decision variables in this BDD.
    pub fn support_set_contains(&self, variable: &BddVariable) -> bool {
        self.nodes().skip(2).any(|node| &node.var == variable)
    }

    /// Return the BDD which represents a function where variable `var` was substituted for
    /// `function` (represented as a BDD).
    ///
    /// This should be equivalent to the expression `exists var. (function <=> var) and self`
    /// (assuming `var` does not appear in `function`).
    ///
    /// If `var` does appear in `function`, it is as if `var` in `function` and `var` in the rest
    /// of the expression are different variables (which intuitively corresponds to how syntactic
    /// substitution on expressions typically operates).
    ///
    /// Note that if you want to substitute multiple variables at the same time, there is
    /// currently no method that can do that with the "syntactic substitution" semantics when the
    /// variable names clash. However, if you need it, it should be possible to implement it
    /// later on (please create an issue for this).
    ///
    /// Also note that because a proxy variable is necessary when `var` appears in `function`,
    /// this operation will panic if the number of variables is `u16::MAX`, as no the proxy
    /// variable cannot be created.
    ///
    pub fn substitute(&self, var: BddVariable, function: &Bdd) -> Bdd {
        let input_set = self.support_set();
        if !input_set.contains(&var) {
            // The substituted variable does not appear in this function at all, so no actual
            // change is necessary.
            return self.clone();
        }

        if !function.support_set_contains(&var) {
            // This is a "safe" substitution, because `var` does not appear in `function`
            // and hence can be fully eliminated.
            let var_bdd = Bdd::mk_literal(self.num_vars(), var, true);
            let iff = var_bdd.iff(function);
            Bdd::binary_op_with_exists(self, &iff, op_function::and, &[var])
        } else {
            // This is an "unsafe" substitution, because `var` must be eliminated from the BDD
            // into which we are substituting, but will remain present in the BDD of the
            // substituted function. To enable this, we rename `var` in the original BDD as a
            // new variable that is then safe to eliminate. However, this means we have to mess
            // with the variable ordering.

            // First, shift all the variables `>=var` by one in the BDD in which we are
            // substituting. This effectively creates a new `var_prime` at the same location
            // in the variable ordering and renames `var` to `var_prime`.
            let mut self_copy = self.clone();
            let mut function_copy = function.clone();
            let mut my_inputs = Vec::from_iter(input_set);
            my_inputs.sort();
            let mut permutation = HashMap::new();
            for input in &my_inputs {
                if *input >= var {
                    let shifted = BddVariable::from_index(input.to_index() + 1);
                    permutation.insert(*input, shifted);
                }
            }
            unsafe {
                self_copy.set_num_vars(self_copy.num_vars().checked_add(1).unwrap());
                self_copy.rename_variables(&permutation);
            }

            // Now, do the same for the `function` BDD, except that `var` should keep its
            // original position (hence `var` in `function` is different from `var` in `self`).
            let var_prime = permutation.remove(&var).unwrap();
            unsafe {
                function_copy.set_num_vars(function_copy.num_vars().checked_add(1).unwrap());
                function_copy.rename_variables(&permutation);
            }

            // Now, we can perform the substitution, getting rid of `var_prime` in the process
            // and keeping only `var`.
            let var_bdd = Bdd::mk_literal(self_copy.num_vars(), var_prime, true);
            let iff = var_bdd.iff(&function_copy);
            let mut substituted =
                Bdd::binary_op_with_exists(&self_copy, &iff, op_function::and, &[var_prime]);

            // Finally, we *reverse* the permutation and remove any evidence that `var_prime`
            // ever existed.
            let reverse_permutation = permutation
                .into_iter()
                .map(|(a, b)| (b, a))
                .collect::<HashMap<_, _>>();

            unsafe {
                substituted.rename_variables(&reverse_permutation);
                substituted.set_num_vars(substituted.num_vars() - 1);
            }

            substituted
        }
    }

    /// Consume this [Bdd] and return a vector of BDD nodes that it represents.
    pub fn to_nodes(self) -> Vec<BddNode> {
        self.0
    }

    /// Create a [Bdd] from a "raw" list of nodes.
    ///
    /// The function does not require the input to be minimal/canonical, but the graph
    /// must be a BDD: I.e. the terminal nodes must be correct, each non-terminal node
    /// must reference existing nodes in the vector, and the edges must follow the variable
    /// ordering.
    pub fn from_nodes(data: &[BddNode]) -> Result<Bdd, String> {
        if data.is_empty() {
            return Err("No nodes".to_string());
        }
        if !data[0].is_zero() {
            return Err("Node at position 0 must be the zero literal.".to_string());
        }
        if data.len() > 1 && !data[1].is_one() {
            return Err("Node at position 1 must be the one literal".to_string());
        }

        let num_vars = data[0].var;
        for node in data.iter().skip(2) {
            if node.var >= num_vars {
                return Err(format!("Invalid variable {:?} in {:?}.", node.var, node));
            }
            if node.low_link.to_index() >= data.len() {
                return Err(format!(
                    "Invalid low-link {:?} in {:?}.",
                    node.low_link, node
                ));
            }
            if node.high_link.to_index() >= data.len() {
                return Err(format!(
                    "Invalid high-link {:?} in {:?}.",
                    node.high_link, node
                ));
            }
            if data[node.low_link.to_index()].var < node.var {
                return Err(format!(
                    "Low link {:?} in {:?} breaks ordering.",
                    node.low_link, node
                ));
            }
            if data[node.high_link.to_index()].var < node.var {
                return Err(format!(
                    "Low link {:?} in {:?} breaks ordering.",
                    node.high_link, node
                ));
            }
        }

        Ok(Bdd(data.to_vec()))
    }

    /// Check that this BDD is structurally sound.
    ///
    /// In particular, all nodes reference existing children and there are no unreachable nodes.
    ///
    /// This does not check that the nodes are sorted in DFS post-order, since this should not
    /// be required to correctly interpret the BDD. Also note that the method can loop forever
    /// if the BDD contains a loop (which it normally shouldn't).
    ///
    /// You can use this to validate the BDD after deserialization.
    pub fn validate(&self) -> Result<(), String> {
        // Check constants.
        if self.0.is_empty() {
            return Err("No nodes".to_string());
        }
        if self.0.len() == 1 {
            return if self != &Bdd::mk_false(self.num_vars()) {
                Err("Malformed false BDD.".to_string())
            } else {
                Ok(())
            };
        }
        if self.0.len() == 2 {
            return if self != &Bdd::mk_true(self.num_vars()) {
                Err("Malformed true BDD.".to_string())
            } else {
                Ok(())
            };
        }

        // Check that all references in nodes are valid.
        let num_vars = self.num_vars();
        for node_pointer in self.pointers().skip(2) {
            let node = &self.0[node_pointer.to_index()];
            if node.var.0 >= num_vars {
                return Err(format!("Found invalid variable: {:?}.", node.var));
            }
            if node.low_link.0 >= (self.0.len() as u32) {
                return Err(format!("Found invalid low-link: {:?}.", node.low_link));
            }
            if node.high_link.0 >= (self.0.len() as u32) {
                return Err(format!("Found invalid high-link: {:?}.", node.high_link));
            }
        }

        let mut visited = vec![false; self.0.len()];
        // Mark terminals as visited.
        visited[0] = true;
        visited[1] = true;
        let mut stack = vec![self.root_pointer()];

        // Check reachability and sorted-ness.
        while let Some(top) = stack.pop() {
            if visited[top.to_index()] {
                continue;
            }
            visited[top.to_index()] = true;
            let node = &self.0[top.to_index()];
            let low_child = &self.0[node.low_link.to_index()];
            let high_child = &self.0[node.high_link.to_index()];

            if low_child.var <= node.var || high_child.var <= node.var {
                return Err(format!("Found broken child ordering in node {top:?}."));
            }

            stack.push(node.low_link);
            stack.push(node.high_link);
        }

        if !visited.into_iter().all(|it| it) {
            return Err("BDD has unreachable nodes.".to_string());
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::_test_util::mk_small_test_bdd;
    use crate::boolean_expression::BooleanExpression;
    use crate::*;
    use num_bigint::BigInt;
    use std::convert::TryFrom;

    #[test]
    fn test_validate_bdd() {
        let bdd = mk_small_test_bdd();
        assert!(bdd.validate().is_ok());

        let malformed_false = "|3,1,0|";
        assert!(Bdd::from_string(malformed_false).validate().is_err());
        let malformed_true = "|3,0,0|3,0,0|";
        assert!(Bdd::from_string(malformed_true).validate().is_err());
        let malformed_invalid_var = "|3,0,0|3,1,1|4,0,1|";
        assert!(Bdd::from_string(malformed_invalid_var).validate().is_err());
        let malformed_invalid_low = "|3,0,0|3,1,1|2,0,5|";
        assert!(Bdd::from_string(malformed_invalid_low).validate().is_err());
        let malformed_invalid_high = "|3,0,0|3,1,1|2,5,0|";
        assert!(Bdd::from_string(malformed_invalid_high).validate().is_err());
        let malformed_invalid_low = "|3,0,0|3,1,1|2,0,5|";
        assert!(Bdd::from_string(malformed_invalid_low).validate().is_err());
        let malformed_broken_ordering = "|3,0,0|3,1,1|1,0,1|2,2,0|";
        assert!(Bdd::from_string(malformed_broken_ordering)
            .validate()
            .is_err());
        let malformed_unreachable = "|3,0,0|3,1,1|1,0,1|1,1,0|";
        assert!(Bdd::from_string(malformed_unreachable).validate().is_err());
    }

    #[test]
    fn node_conversion() {
        let bdd = mk_small_test_bdd();

        let nodes = bdd.clone().to_nodes();
        assert_eq!(bdd, Bdd::from_nodes(&nodes).unwrap());

        // Empty.
        assert!(Bdd::from_nodes(&Vec::new()).is_err());
        // Missing zero.
        assert!(Bdd::from_nodes(&nodes[1..]).is_err());
        // Missing one.
        assert!(Bdd::from_nodes(&[nodes[0], nodes[2]]).is_err());

        let mut nodes = bdd.clone().to_nodes();
        nodes[0].var = BddVariable(1);
        nodes[1].var = BddVariable(1);
        // Invalid variables.
        assert!(Bdd::from_nodes(&nodes).is_err());

        // Test with invalid high link.
        let mut nodes = bdd.clone().to_nodes();
        nodes[2].high_link = BddPointer::from_index(100);
        assert!(Bdd::from_nodes(&nodes).is_err());

        // Test with invalid low link.
        let mut nodes = bdd.clone().to_nodes();
        nodes[2].low_link = BddPointer::from_index(100);
        assert!(Bdd::from_nodes(&nodes).is_err());

        // Test broken ordering low link.
        let mut nodes = bdd.clone().to_nodes();
        nodes[2].low_link = BddPointer::from_index(3);
        assert!(Bdd::from_nodes(&nodes).is_err());

        // Test broken ordering high link.
        let mut nodes = bdd.clone().to_nodes();
        nodes[2].high_link = BddPointer::from_index(3);
        assert!(Bdd::from_nodes(&nodes).is_err());
    }

    #[test]
    fn bdd_impl() {
        let bdd = mk_small_test_bdd();

        assert_eq!(4, bdd.size());
        assert_eq!(5, bdd.num_vars());
        assert_eq!(
            HashSet::from([BddVariable(2), BddVariable(3)]),
            bdd.support_set()
        );
        assert!(!bdd.support_set_contains(&BddVariable(0)));
        assert!(!bdd.support_set_contains(&BddVariable(1)));
        assert!(bdd.support_set_contains(&BddVariable(2)));
        assert!(bdd.support_set_contains(&BddVariable(3)));
        assert!(!bdd.support_set_contains(&BddVariable(4)));
        assert_eq!(
            HashMap::from([(BddVariable(2), 1), (BddVariable(3), 1)]),
            bdd.size_per_variable()
        );
        assert_eq!(BddPointer::from_index(3), bdd.root_pointer());
        assert_eq!(
            BddPointer::one(),
            bdd.low_link_of(BddPointer::from_index(2))
        );
        assert_eq!(
            BddPointer::zero(),
            bdd.high_link_of(BddPointer::from_index(2))
        );
        assert_eq!(BddVariable(3), bdd.var_of(BddPointer::from_index(2)));
        assert_eq!(
            BddPointer::zero(),
            bdd.low_link_of(BddPointer::from_index(3))
        );
        assert_eq!(
            BddPointer::from_index(2),
            bdd.high_link_of(BddPointer::from_index(3))
        );
        assert_eq!(BddVariable(2), bdd.var_of(BddPointer::from_index(3)));
    }

    #[test]
    fn bdd_cardinality() {
        // 5 variables, v3 & !v4
        let bdd = mk_small_test_bdd();
        assert_eq!(8.0, bdd.cardinality());
    }

    #[test]
    fn bdd_exact_cardinality() {
        // 5 variables, v3 & !v4
        let bdd = mk_small_test_bdd();
        assert_eq!(BigInt::from(8), bdd.exact_cardinality());
    }

    #[test]
    fn bdd_exact_clause_cardinality() {
        // 5 variables, v3 & !v4
        let bdd = mk_small_test_bdd();
        assert_eq!(BigInt::from(1), bdd.exact_clause_cardinality());
        let vars = BddVariableSet::new_anonymous(5);
        let bdd = vars.eval_expression_string("x_0 & (x_1 | x_2) & (x_0 => x_4)");
        assert_eq!(
            BigInt::from(bdd.sat_clauses().count()),
            bdd.exact_clause_cardinality()
        );
    }

    #[test]
    fn bdd_sat_witness_basic() {
        // v3 & !v4
        let bdd = mk_small_test_bdd();
        let expected = BddValuation(vec![false, false, true, false, false]);
        assert_eq!(bdd.sat_witness().unwrap(), expected);
        assert!(bdd.eval_in(&bdd.sat_witness().unwrap()));
    }

    #[test]
    fn bdd_sat_witness_advanced() {
        let vars = BddVariableSet::new_anonymous(5);
        let bdd = vars.eval_expression_string("x_0 & (x_1 | x_2) & (x_0 => x_4)");
        let valuation = BddValuation(vec![true, false, true, false, true]);
        assert_eq!(bdd.sat_witness().unwrap(), valuation);
        assert!(bdd.eval_in(&bdd.sat_witness().unwrap()));
    }

    #[test]
    fn bdd_to_formula() {
        let vars = BddVariableSet::new_anonymous(5);
        let bdd = vars.eval_expression_string("x_0 & (x_1 | x_2) & (x_0 => x_4)");
        let expected_expression =
            BooleanExpression::try_from("x_0 & ((x_1 & x_4) | (!x_1 & (x_2 & x_4)))").unwrap();
        let actual_expression = bdd.to_boolean_expression(&vars);
        assert_eq!(vars.eval_expression(&actual_expression), bdd);
        assert_eq!(bdd.to_boolean_expression(&vars), expected_expression);
    }

    #[test]
    fn bdd_valuation_check() {
        let vars = BddVariableSet::new_anonymous(4);
        let is_singleton = vars.eval_expression_string("x_0 & !x_1 & !x_2 & x_3");
        let not_singleton_1 = vars.eval_expression_string("x_0 & !x_1 | !x_2 & x_3");
        let not_singleton_2 = vars.eval_expression_string("x_0 & !x_1 & !x_2");
        let not_singleton_3 = vars.eval_expression_string("x_0 & !x_1 & x_3");

        assert!(is_singleton.is_valuation());
        assert!(!not_singleton_1.is_valuation());
        assert!(!not_singleton_2.is_valuation());
        assert!(!not_singleton_3.is_valuation());
    }

    #[test]
    fn bdd_clause_check() {
        let vars = BddVariableSet::new_anonymous(4);

        let is_clause_1 = vars.eval_expression_string("x_0 & !x_1 & x_2 & x_3");
        let is_clause_2 = vars.eval_expression_string("x_0 & !x_2");
        let is_not_clause = vars.eval_expression_string("x_0 | x_1");

        assert!(is_clause_1.is_clause());
        assert!(is_clause_2.is_clause());
        assert!(!is_not_clause.is_clause())
    }

    #[test]
    fn bdd_variable_change() {
        let mut bdd = mk_small_test_bdd();
        assert_eq!(5, bdd.num_vars());
        unsafe {
            bdd.set_num_vars(6);
        }
        assert_eq!(6, bdd.num_vars());
        // The BDD actually does not use all 5 variables.
        unsafe {
            bdd.set_num_vars(4);
        }
        assert_eq!(4, bdd.num_vars());
    }

    #[test]
    #[should_panic]
    fn bdd_variable_change_failing() {
        let mut bdd = mk_small_test_bdd();
        unsafe {
            bdd.set_num_vars(3);
        }
    }

    #[test]
    fn test_variables_rename() {
        let set = BddVariableSet::new_anonymous(10);
        let base = set.eval_expression_string("(!x_0 & x_1) | (!x_2 & x_3)");
        let shift = set.eval_expression_string("(!x_1 & x_2) | (!x_3 & x_4)");
        let spread = set.eval_expression_string("(!x_0 & x_2) | (!x_4 & x_6)");

        let shift_permutation: HashMap<BddVariable, BddVariable> = HashMap::from_iter([
            (BddVariable(0), BddVariable(1)),
            (BddVariable(1), BddVariable(2)),
            (BddVariable(2), BddVariable(3)),
            (BddVariable(3), BddVariable(4)),
            (BddVariable(4), BddVariable(5)),
        ]);

        let spread_permutation: HashMap<BddVariable, BddVariable> = HashMap::from_iter([
            (BddVariable(0), BddVariable(0)),
            (BddVariable(1), BddVariable(2)),
            (BddVariable(2), BddVariable(4)),
            (BddVariable(3), BddVariable(6)),
            (BddVariable(4), BddVariable(8)),
        ]);

        unsafe {
            let mut actual = base.clone();
            actual.rename_variables(&shift_permutation);
            assert_eq!(actual, shift);
        }

        unsafe {
            let mut actual = base.clone();
            actual.rename_variables(&spread_permutation);
            assert_eq!(actual, spread);
        }

        unsafe {
            let mut trivial = set.mk_true();
            trivial.rename_variables(&shift_permutation);
            assert_eq!(set.mk_true(), trivial);
        }
    }

    #[test]
    #[should_panic]
    fn test_variables_rename_invalid_var() {
        let mut bdd = mk_small_test_bdd();
        let permutation: HashMap<BddVariable, BddVariable> =
            HashMap::from_iter([(BddVariable(3), BddVariable(10))]);
        unsafe {
            bdd.rename_variables(&permutation);
        }
    }

    #[test]
    #[should_panic]
    fn test_variables_rename_unordered() {
        let mut bdd = mk_small_test_bdd();
        let permutation: HashMap<BddVariable, BddVariable> = HashMap::from_iter([
            (BddVariable(4), BddVariable(2)),
            (BddVariable(3), BddVariable(1)),
        ]);
        unsafe {
            bdd.rename_variables(&permutation);
        }
    }

    #[test]
    fn test_variable_rename() {
        let mut bdd = mk_small_test_bdd();
        unsafe {
            bdd.rename_variable(BddVariable(2), BddVariable(0));
            bdd.rename_variable(BddVariable(3), BddVariable(4));
        }
        let expected = HashSet::from_iter(vec![BddVariable(0), BddVariable(4)]);
        assert_eq!(expected, bdd.support_set());
    }

    #[test]
    #[should_panic]
    fn test_variable_rename_fail_1() {
        let mut bdd = mk_small_test_bdd();
        unsafe {
            bdd.rename_variable(BddVariable(2), BddVariable(6));
        }
    }

    #[test]
    #[should_panic]
    fn test_variable_rename_fail_2() {
        let mut bdd = mk_small_test_bdd();
        unsafe {
            bdd.rename_variable(BddVariable(6), BddVariable(2));
        }
    }

    #[test]
    #[should_panic]
    fn test_variable_rename_fail_3() {
        let mut bdd = mk_small_test_bdd();
        unsafe {
            bdd.rename_variable(BddVariable(2), BddVariable(6));
        }
    }

    #[test]
    #[should_panic]
    fn test_variable_rename_fail_4() {
        let mut bdd = mk_small_test_bdd();
        unsafe {
            bdd.rename_variable(BddVariable(2), BddVariable(3));
        }
    }

    #[test]
    #[should_panic]
    fn test_variable_rename_fail_5() {
        let mut bdd = mk_small_test_bdd();
        unsafe {
            bdd.rename_variable(BddVariable(2), BddVariable(4));
        }
    }

    #[test]
    fn test_substitution() {
        let vars = BddVariableSet::new_anonymous(5);
        let original = bdd!(vars, "x_0" & ("x_1" | "x_4"));
        let to_swap = bdd!(vars, "x_3" & "x_2");
        let expected = bdd!(vars, "x_0" & (("x_3" & "x_2") | "x_4"));
        let x_1 = vars.var_by_name("x_1").unwrap();
        let substituted = original.substitute(x_1, &to_swap);
        assert!(expected.iff(&substituted).is_true());
        assert_eq!(expected.iff(&substituted).as_bool(), Some(true));
    }

    #[test]
    fn test_substitution_with_clash() {
        let vars = BddVariableSet::new_anonymous(5);
        let original = bdd!(vars, "x_0" & ("x_1" | "x_4"));
        let expected = bdd!(vars, ("x_0" | "x_3") & ("x_1" | "x_4"));
        let to_swap = bdd!(vars, "x_0" | "x_3");
        let x_0 = vars.var_by_name("x_0").unwrap();
        let substituted = original.substitute(x_0, &to_swap);
        assert!(substituted.iff(&expected).is_true());
    }
}
