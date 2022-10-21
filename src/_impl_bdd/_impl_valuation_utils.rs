use crate::{Bdd, BddPartialValuation, BddValuation, BddVariable};
use rand::Rng;
use std::cmp::max;

/// Utilities for extracting interesting valuations and paths from a `Bdd`.
impl Bdd {
    /// Return the lexicographically first satisfying valuation of this `Bdd`.
    ///
    /// (In this context, lexicographically means `0 < 1`, with greatest variable id
    /// being the most significant).
    pub fn first_valuation(&self) -> Option<BddValuation> {
        if self.is_false() {
            return None;
        }

        let mut valuation = BddValuation::all_false(self.num_vars());
        let mut node = self.root_pointer();
        while !node.is_terminal() {
            if self.low_link_of(node).is_zero() {
                valuation.set(self.var_of(node));
                node = self.high_link_of(node);
            } else {
                node = self.low_link_of(node);
            }
        }

        Some(valuation)
    }

    /// Return the lexicographically last satisfying valuation of this `Bdd`.
    ///
    /// (In this context, lexicographically means `0 < 1`, with greatest variable id
    /// being the most significant).
    pub fn last_valuation(&self) -> Option<BddValuation> {
        if self.is_false() {
            return None;
        }

        let mut valuation = BddValuation::all_true(self.num_vars());
        let mut node = self.root_pointer();
        while !node.is_terminal() {
            if self.high_link_of(node).is_zero() {
                valuation.clear(self.var_of(node));
                node = self.low_link_of(node);
            } else {
                node = self.high_link_of(node);
            }
        }

        Some(valuation)
    }

    /// Return the lexicographically fist path in this `Bdd`, represented as
    /// a *conjunctive* clause.
    pub fn first_clause(&self) -> Option<BddPartialValuation> {
        if self.is_false() {
            return None;
        }

        let mut valuation = BddPartialValuation::empty();
        let mut node = self.root_pointer();
        while !node.is_terminal() {
            if self.low_link_of(node).is_zero() {
                valuation.set_value(self.var_of(node), true);
                node = self.high_link_of(node);
            } else {
                valuation.set_value(self.var_of(node), false);
                node = self.low_link_of(node);
            }
        }

        Some(valuation)
    }

    /// Return the lexicographically last path in this `Bdd`, represented as
    /// a *conjunctive* clause.
    pub fn last_clause(&self) -> Option<BddPartialValuation> {
        if self.is_false() {
            return None;
        }

        if self.is_false() {
            return None;
        }

        let mut valuation = BddPartialValuation::empty();
        let mut node = self.root_pointer();
        while !node.is_terminal() {
            if self.high_link_of(node).is_zero() {
                valuation.set_value(self.var_of(node), false);
                node = self.low_link_of(node);
            } else {
                valuation.set_value(self.var_of(node), true);
                node = self.high_link_of(node);
            }
        }

        Some(valuation)
    }

    /// Return a valuation in this `Bdd` that contains the greatest amount of positive literals.
    ///
    /// If such valuation is not unique, the method should return the one that is first
    /// lexicographically.
    pub fn most_positive_valuation(&self) -> Option<BddValuation> {
        if self.is_false() {
            return None;
        }

        let mut cache = Vec::with_capacity(self.size());
        cache.push((0, true));
        cache.push((0, true));

        for i in self.pointers().skip(2) {
            let i_var = self.var_of(i);
            let low_link = self.low_link_of(i);
            let high_link = self.high_link_of(i);

            // Parenthesis to avoid a chance of overflow.
            let low_link_diff =
                cache[low_link.to_index()].0 + ((self.var_of(low_link).0 - i_var.0) - 1);
            let high_link_diff =
                cache[high_link.to_index()].0 + ((self.var_of(high_link).0 - i_var.0) - 1);

            let result = if low_link.is_zero() && high_link.is_zero() {
                panic!("Non canonical BDD.")
            } else if low_link.is_zero() {
                (high_link_diff + 1, true)
            } else if high_link.is_zero() {
                (low_link_diff, false)
            } else if high_link_diff + 1 > low_link_diff {
                (high_link_diff + 1, true)
            } else {
                (low_link_diff, false)
            };

            cache.push(result);
        }

        let mut valuation = BddValuation::all_true(self.num_vars());
        let mut node = self.root_pointer();
        while !node.is_terminal() {
            let (_, child) = cache[node.to_index()];
            if child {
                node = self.high_link_of(node);
            } else {
                valuation.clear(self.var_of(node));
                node = self.low_link_of(node);
            }
        }

        Some(valuation)
    }

    /// Return a valuation in this `Bdd` that contains the greatest amount of negative literals.
    ///
    /// If such valuation is not unique, the method should return the one that is first
    /// lexicographically.
    pub fn most_negative_valuation(&self) -> Option<BddValuation> {
        if self.is_false() {
            return None;
        }

        let mut cache = Vec::with_capacity(self.size());
        cache.push((0, true));
        cache.push((0, true));

        for i in self.pointers().skip(2) {
            let i_var = self.var_of(i);
            let low_link = self.low_link_of(i);
            let high_link = self.high_link_of(i);

            // Parenthesis to avoid a chance of overflow.
            let low_link_diff =
                cache[low_link.to_index()].0 + ((self.var_of(low_link).0 - i_var.0) - 1);
            let high_link_diff =
                cache[high_link.to_index()].0 + ((self.var_of(high_link).0 - i_var.0) - 1);

            let result = if low_link.is_zero() && high_link.is_zero() {
                panic!("Non canonical BDD.")
            } else if low_link.is_zero() {
                (high_link_diff, true)
            } else if high_link.is_zero() {
                (low_link_diff + 1, false)
            } else if high_link_diff > low_link_diff + 1 {
                (high_link_diff, true)
            } else {
                (low_link_diff + 1, false)
            };

            cache.push(result);
        }

        let mut valuation = BddValuation::all_false(self.num_vars());
        let mut node = self.root_pointer();
        while !node.is_terminal() {
            let (_, child) = cache[node.to_index()];
            if child {
                valuation.set(self.var_of(node));
                node = self.high_link_of(node);
            } else {
                node = self.low_link_of(node);
            }
        }

        Some(valuation)
    }

    /// Compute the path in this `Bdd` that has the highest amount of fixed variables.
    ///
    /// If there are multiple such paths, try to order them lexicographically.
    pub fn most_fixed_clause(&self) -> Option<BddPartialValuation> {
        if self.is_false() {
            return None;
        }

        let mut cache: Vec<(usize, bool)> = Vec::with_capacity(self.size());
        cache.push((0, true));
        cache.push((0, true));

        for i in self.pointers().skip(2) {
            let low_link = self.low_link_of(i);
            let high_link = self.high_link_of(i);

            let result = if low_link.is_zero() && high_link.is_zero() {
                panic!("Non canonical BDD.");
            } else if low_link.is_zero() {
                (cache[high_link.to_index()].0 + 1, true)
            } else if high_link.is_zero() {
                (cache[low_link.to_index()].0 + 1, false)
            } else if cache[high_link.to_index()] > cache[low_link.to_index()] {
                (cache[high_link.to_index()].0 + 1, true)
            } else {
                (cache[low_link.to_index()].0 + 1, false)
            };

            cache.push(result);
        }

        let mut valuation = BddPartialValuation::empty();
        let mut node = self.root_pointer();
        while !node.is_terminal() {
            let (_, child) = cache[node.to_index()];
            valuation.set_value(self.var_of(node), child);
            node = if child {
                self.high_link_of(node)
            } else {
                self.low_link_of(node)
            };
        }

        Some(valuation)
    }

    /// Compute the path in this `Bdd` that has the highest amount of free variables.
    ///
    /// If there are multiple such paths, try to order them lexicographically.
    pub fn most_free_clause(&self) -> Option<BddPartialValuation> {
        if self.is_false() {
            return None;
        }

        let mut cache: Vec<(u16, bool)> = Vec::with_capacity(self.size());
        cache.push((0, true));
        cache.push((0, true));

        let mut cache: Vec<(usize, bool)> = Vec::with_capacity(self.size());
        cache.push((0, true));
        cache.push((0, true));

        for i in self.pointers().skip(2) {
            let low_link = self.low_link_of(i);
            let high_link = self.high_link_of(i);

            let result = if low_link.is_zero() && high_link.is_zero() {
                panic!("Non canonical BDD.");
            } else if low_link.is_zero() {
                (cache[high_link.to_index()].0 + 1, true)
            } else if high_link.is_zero() {
                (cache[low_link.to_index()].0 + 1, false)
            } else if cache[high_link.to_index()] < cache[low_link.to_index()] {
                (cache[high_link.to_index()].0 + 1, true)
            } else {
                (cache[low_link.to_index()].0 + 1, false)
            };

            cache.push(result);
        }

        let mut valuation = BddPartialValuation::empty();
        let mut node = self.root_pointer();
        while !node.is_terminal() {
            let (_, child) = cache[node.to_index()];
            valuation.set_value(self.var_of(node), child);
            node = if child {
                self.high_link_of(node)
            } else {
                self.low_link_of(node)
            };
        }

        Some(valuation)
    }

    /// Pick a random valuation that satisfies this `Bdd`, using a provided random number
    /// generator.
    ///
    /// Note that the random distribution with which the valuations are picked depends
    /// on the structure of the `Bdd` and is not necessarily uniform.
    pub fn random_valuation<R: Rng>(&self, rng: &mut R) -> Option<BddValuation> {
        if self.is_false() {
            return None;
        }

        let mut valuation = BddValuation::all_false(self.num_vars());
        let mut node = self.root_pointer();
        for i_var in 0..self.num_vars() {
            let var = BddVariable(i_var);
            if self.var_of(node) != var {
                // Just pick random.
                valuation.set_value(var, rng.gen_bool(0.5));
            } else {
                let child = if self.low_link_of(node).is_zero() {
                    true
                } else if self.high_link_of(node).is_zero() {
                    false
                } else {
                    rng.gen_bool(0.5)
                };

                valuation.set_value(var, child);
                node = if child {
                    self.high_link_of(node)
                } else {
                    self.low_link_of(node)
                }
            }
        }

        Some(valuation)
    }

    /// Pick a random path that appears in this `Bdd`, using a provided random number
    /// generator.
    ///
    /// Note that the distribution with which the path is picked depends on the structure
    /// of the `Bdd` and is not necessarily uniform.
    pub fn random_clause<R: Rng>(&self, rng: &mut R) -> Option<BddPartialValuation> {
        if self.is_false() {
            return None;
        }

        let mut path = BddPartialValuation::empty();
        let mut node = self.root_pointer();
        while !node.is_one() {
            let child = if self.low_link_of(node).is_zero() {
                true
            } else if self.high_link_of(node).is_zero() {
                false
            } else {
                rng.gen_bool(0.5)
            };

            path.set_value(self.var_of(node), child);
            node = if child {
                self.high_link_of(node)
            } else {
                self.low_link_of(node)
            }
        }

        Some(path)
    }

    /// Compute the most restrictive conjunctive clause the covers all satisfying values
    /// in this BDD. In other words, if you compute the BDD corresponding to the resulting
    /// partial valuation, the new BDD will be a superset of this BDD, and it will be the smallest
    /// superset that can be described using a single clause.
    pub fn necessary_clause(&self) -> Option<BddPartialValuation> {
        if self.is_false() {
            return None;
        }

        if self.is_true() {
            return Some(BddPartialValuation::empty());
        }

        let mut seen_one = vec![false; usize::from(self.num_vars())];
        let mut seen_zero = vec![false; usize::from(self.num_vars())];
        let mut seen_any = vec![false; usize::from(self.num_vars())];

        let top_var_id = usize::from(self.var_of(self.root_pointer()).0);
        for i in &mut seen_any[0..top_var_id] {
            *i = true;
        }

        // First, quickly scan the BDD to designate variables based on which decisions are made.
        for id in self.pointers().skip(2) {
            let var_id = usize::from(self.var_of(id).0);
            let high_link = self.high_link_of(id);
            let low_link = self.low_link_of(id);

            if !(low_link.is_zero() || high_link.is_zero()) {
                seen_any[var_id] = true;
            }
        }

        // Then go through the remaining variables, and see if some other variable
        // can also be designated as free. Sadly, this will need to scan the BDD as many times
        // as there are fixed variables, as these will never be
        for var in 0..usize::from(self.num_vars()) {
            if seen_any[var] {
                continue;
            }

            for id in self.pointers().skip(2) {
                let high_link = self.high_link_of(id);
                let low_link = self.low_link_of(id);

                let var_id = usize::from(self.var_of(id).0);
                let high_link_var_id = usize::from(self.var_of(high_link).0);
                let low_link_var_id = usize::from(self.var_of(low_link).0);

                let range = if high_link.is_zero() {
                    (var_id + 1)..low_link_var_id
                } else if low_link.is_zero() {
                    (var_id + 1)..high_link_var_id
                } else {
                    seen_any[var_id] = true;
                    (var_id)..max(high_link_var_id, low_link_var_id)
                };

                if range.contains(&var) {
                    for var in range {
                        seen_any[var] = true;
                    }
                    break;
                }
            }
        }

        // Finally, run one extra loop that just designates all ones/zeroes.
        for id in self.pointers().skip(2) {
            let var_id = usize::from(self.var_of(id).0);
            if !seen_any[var_id] {
                let high_link = self.high_link_of(id);
                let low_link = self.low_link_of(id);

                if high_link.is_zero() {
                    seen_zero[var_id] = true;
                } else if low_link.is_zero() {
                    seen_one[var_id] = true;
                }
            }
        }

        let mut result = BddPartialValuation::empty();
        for i in 0..usize::from(self.num_vars()) {
            match (seen_zero[i], seen_one[i], seen_any[i]) {
                (_, _, true) | (true, true, _) => {
                    // Either we have seen a node which implies both var=1 and var=0 are possible,
                    // or we have seen two decision nodes, one implying var=1 and the other var=0.
                    // In such case, the value is "any" and we do not have to update result.
                }
                (true, false, false) => {
                    result.set_value(BddVariable(i as u16), false);
                }
                (false, true, false) => {
                    result.set_value(BddVariable(i as u16), true);
                }
                (false, false, false) => {
                    // At some point while traversing the graph, one of the three must
                    // have been encountered.
                    unreachable!()
                }
            }
        }

        Some(result)
    }
}

#[cfg(test)]
mod tests {
    use crate::{BddPartialValuation, BddValuation, BddVariableSet};
    use rand::prelude::StdRng;
    use rand::SeedableRng;

    #[test]
    fn first_last_valuation() {
        let vars = BddVariableSet::new_anonymous(5);
        let v = vars.variables();

        let c1 = BddPartialValuation::from_values(&[(v[0], true), (v[1], false)]);
        let c2 = BddPartialValuation::from_values(&[(v[1], true), (v[3], false)]);
        let c3 = BddPartialValuation::from_values(&[(v[2], false), (v[4], true)]);
        let bdd = vars.mk_dnf(&[c1.clone(), c2.clone(), c3.clone()]);

        let first_valuation = BddValuation(vec![false, false, false, false, true]);
        let last_valuation = BddValuation(vec![true, true, true, false, true]);

        assert_eq!(Some(first_valuation), bdd.first_valuation());
        assert_eq!(None, vars.mk_false().first_valuation());
        assert_eq!(Some(last_valuation), bdd.last_valuation());
        assert_eq!(None, vars.mk_false().last_valuation());
    }

    #[test]
    fn first_last_clause() {
        let vars = BddVariableSet::new_anonymous(5);
        let v = vars.variables();

        let c1 = BddPartialValuation::from_values(&[(v[0], true), (v[1], false)]);
        let c2 = BddPartialValuation::from_values(&[(v[1], true), (v[3], false)]);
        let c3 = BddPartialValuation::from_values(&[(v[2], false), (v[4], true)]);
        let bdd = vars.mk_dnf(&[c1.clone(), c2.clone(), c3.clone()]);

        let first_clause = BddPartialValuation::from_values(&[
            (v[0], false),
            (v[1], false),
            (v[2], false),
            (v[4], true),
        ]);

        let last_clause = BddPartialValuation::from_values(&[
            (v[0], true),
            (v[1], true),
            (v[2], true),
            (v[3], false),
        ]);

        assert_eq!(Some(first_clause), bdd.first_clause());
        assert_eq!(None, vars.mk_false().first_clause());
        assert_eq!(Some(last_clause), bdd.last_clause());
        assert_eq!(None, vars.mk_false().last_clause());
    }

    #[test]
    fn most_positive_negative_valuation() {
        let vars = BddVariableSet::new_anonymous(5);
        let v = vars.variables();

        let c1 = BddPartialValuation::from_values(&[(v[0], true), (v[1], false)]);
        let c2 = BddPartialValuation::from_values(&[(v[1], true), (v[3], false)]);
        let c3 = BddPartialValuation::from_values(&[(v[2], false), (v[4], true)]);
        let bdd = vars.mk_dnf(&[c1.clone(), c2.clone(), c3.clone()]);

        let most_positive_valuation = BddValuation(vec![true, false, true, true, true]);
        let most_negative_valuation = BddValuation(vec![false, false, false, false, true]);

        assert_eq!(Some(most_positive_valuation), bdd.most_positive_valuation());
        assert_eq!(None, vars.mk_false().most_positive_valuation());
        assert_eq!(Some(most_negative_valuation), bdd.most_negative_valuation());
        assert_eq!(None, vars.mk_false().most_negative_valuation());
    }

    #[test]
    fn most_fixed_free_clause() {
        let vars = BddVariableSet::new_anonymous(5);
        let v = vars.variables();

        let c1 = BddPartialValuation::from_values(&[(v[0], true), (v[1], false)]);
        let c2 = BddPartialValuation::from_values(&[(v[1], true), (v[3], false)]);
        let c3 = BddPartialValuation::from_values(&[(v[2], false), (v[4], true)]);
        let bdd = vars.mk_dnf(&[c1.clone(), c2.clone(), c3.clone()]);

        //println!("{}", bdd.to_dot_string(&vars, true));

        let fixed_clause = BddPartialValuation::from_values(&[
            (v[0], false),
            (v[1], true),
            (v[2], false),
            (v[3], true),
            (v[4], true),
        ]);
        let free_clause = BddPartialValuation::from_values(&[(v[0], true), (v[1], false)]);

        assert_eq!(Some(fixed_clause), bdd.most_fixed_clause());
        assert_eq!(None, vars.mk_false().most_fixed_clause());
        assert_eq!(Some(free_clause), bdd.most_free_clause());
        assert_eq!(None, vars.mk_false().most_free_clause());
    }

    #[test]
    fn random_valuation() {
        let vars = BddVariableSet::new_anonymous(5);
        let v = vars.variables();

        let c1 = BddPartialValuation::from_values(&[(v[0], true), (v[1], false)]);
        let c2 = BddPartialValuation::from_values(&[(v[1], true), (v[3], false)]);
        let c3 = BddPartialValuation::from_values(&[(v[2], false), (v[4], true)]);
        let bdd = vars.mk_dnf(&[c1.clone(), c2.clone(), c3.clone()]);

        let mut random = StdRng::seed_from_u64(1234567890);
        for _ in 0..100 {
            let valuation = bdd.random_valuation(&mut random).unwrap();
            assert!(bdd.eval_in(&valuation));
        }

        assert_eq!(None, vars.mk_false().random_valuation(&mut random));
    }

    #[test]
    fn random_clause() {
        let vars = BddVariableSet::new_anonymous(5);
        let v = vars.variables();

        let c1 = BddPartialValuation::from_values(&[(v[0], true), (v[1], false)]);
        let c2 = BddPartialValuation::from_values(&[(v[1], true), (v[3], false)]);
        let c3 = BddPartialValuation::from_values(&[(v[2], false), (v[4], true)]);
        let bdd = vars.mk_dnf(&[c1.clone(), c2.clone(), c3.clone()]);

        let mut random = StdRng::seed_from_u64(1234567890);
        for _ in 0..100 {
            let clause = bdd.random_clause(&mut random).unwrap();
            let clause_bdd = vars.mk_conjunctive_clause(&clause);
            assert_eq!(clause_bdd.and(&bdd), clause_bdd);
        }

        assert_eq!(None, vars.mk_false().random_clause(&mut random));
    }

    #[test]
    fn necessary_clause() {
        let vars = BddVariableSet::new_anonymous(5);
        let v = vars.variables();

        let f = vars.eval_expression_string("x_3 & !x_0 & (x_1 | x_2) & (!x_3 | x_4)");

        let mut result = BddPartialValuation::empty();
        result.set_value(v[0], false);
        result.set_value(v[3], true);
        result.set_value(v[4], true);
        assert_eq!(Some(result), f.necessary_clause());

        assert_eq!(
            Some(BddPartialValuation::empty()),
            vars.mk_true().necessary_clause()
        );
        assert_eq!(None, vars.mk_false().necessary_clause());
    }
}
