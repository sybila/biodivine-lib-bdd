use crate::{Bdd, BddPointer, BddSatisfyingValuations, BddValuation, BddVariable};

impl Bdd {
    pub fn sat_valuations(&self) -> BddSatisfyingValuations {
        BddSatisfyingValuations {
            bdd: self,
            continuation: if self.is_false() {
                None
            } else {
                Some(self.first_sat_path())
            },
        }
    }

    /// **(internal)** Find first satisfying path in the Bdd, its path mask (bits where the path
    /// has fixed values) and smallest valuation on this path.
    fn first_sat_path(&self) -> (Vec<BddPointer>, BddValuation, BddValuation) {
        let mut sat_path = Vec::new();
        let mut path_mask = BddValuation::all_false(self.num_vars());
        let mut first_valuation = BddValuation::all_false(self.num_vars());
        sat_path.push(self.root_pointer());
        self.continue_sat_path(&mut sat_path, &mut path_mask, &mut first_valuation);
        (sat_path, path_mask, first_valuation)
    }

    /// **(internal)** Take last node on given `sat_path` and find the first satisfiable path that follows from it.
    ///
    /// When this function returns, last pointer in `sat_path` is the one pointer.
    ///
    /// Assumes `path_mask` and `first_valuation` is cleared for every variable greater than `varOf(last(sat_path))`.
    fn continue_sat_path(
        &self,
        sat_path: &mut Vec<BddPointer>,
        path_mask: &mut BddValuation,
        first_valuation: &mut BddValuation,
    ) {
        while let Some(top) = sat_path.last() {
            if top.is_zero() {
                panic!("No SAT path!");
            } else if top.is_one() {
                return; // Found sat path.
            } else {
                let var = self.var_of(*top);
                let low = self.low_link_of(*top);
                let high = self.high_link_of(*top);
                path_mask.set(var);
                if !low.is_zero() {
                    sat_path.push(low);
                } else {
                    // Can't follow low; follow high.
                    assert!(!high.is_zero());
                    sat_path.push(high);
                    first_valuation.flip_value(var);
                }
            }
        }
    }
}

impl BddSatisfyingValuations<'_> {
    /// **(internal)** Increment the given valuation, but do not change the bits that have mask set to true.
    /// Returns true if increment was successful, false when overflowed.
    fn increment_masked_valuation(valuation: &mut BddValuation, mask: &BddValuation) -> bool {
        for i in (0..valuation.0.len()).rev() {
            if mask.0[i] {
                // This position is fixed, don't change it!
                continue;
            } else {
                // This position can be changed.
                valuation.0[i] = !valuation.0[i];
                if valuation.0[i] {
                    // If it changed from 0 to 1, we are done.
                    return true;
                }
            }
        }
        false // Valuation increment overflow.
    }

    /// **(internal)** Find next satisfying path in the Bdd and update path mask and first valuation
    /// accordingly. If this was the last satisfying path, returns false.
    fn next_sat_path(
        bdd: &Bdd,
        sat_path: &mut Vec<BddPointer>,
        path_mask: &mut BddValuation,
        first_valuation: &mut BddValuation,
    ) -> bool {
        // Pop unusable end of path until a variable that can be flipped from 0 to 1 is found.
        while let Some(top) = sat_path.pop() {
            if let Some(candidate) = sat_path.last() {
                if top == bdd.high_link_of(*candidate) {
                    // This path already follows the high link of candidate - that means we
                    // will pop candidate and look for a completely new path.
                } else {
                    // Here, we can switching from low link to high link.
                    assert_eq!(top, bdd.low_link_of(*candidate));
                    let high = bdd.high_link_of(*candidate);
                    if high.is_zero() {
                        // But if high is zero, there will be no sat path there and we cannot switch,
                        // so just pop it as well.
                    } else {
                        // Here, we actually have a non-empty high link that we can switch to!
                        // But first, we have to clear path_mask and first_valuation up to the variable
                        // of candidate (which remains to be set, just not to 0, but to 1).
                        let var = bdd.var_of(*candidate);
                        assert!(path_mask.value(var));
                        assert!(!first_valuation.value(var));
                        sat_path.push(high);
                        first_valuation.set(var); // flip candidate from 0 to 1
                        for i in (var.0 + 1)..bdd.num_vars() {
                            // clear everything that comes after candidate
                            path_mask.clear(BddVariable(i));
                            first_valuation.clear(BddVariable(i))
                        }
                        // Now we are ready to finalize the fresh path.
                        bdd.continue_sat_path(sat_path, path_mask, first_valuation);
                        return true;
                    }
                }
            }
        }
        // If we got here, it means there was no link on path that we could have flipped from low
        // to high, hence this was the last path...
        false
    }
}

impl Iterator for BddSatisfyingValuations<'_> {
    type Item = BddValuation;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((sat_path, path_mask, next_valuation)) = &mut self.continuation {
            let result = next_valuation.clone();
            if BddSatisfyingValuations::increment_masked_valuation(next_valuation, path_mask) {
                // Done. Valuation successfully incremented.
                Some(result)
            } else {
                // Valuation cannot be incremented (overflow) - find next SAT path.
                if Self::next_sat_path(self.bdd, sat_path, path_mask, next_valuation) {
                    // Done. Found next sat path, continuing with this path.
                    Some(result)
                } else {
                    // No more paths. Return last valuation and then die.
                    self.continuation = None;
                    Some(result)
                }
            }
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::_test_util::mk_5_variable_set;
    use crate::{Bdd, BddValuation, BddValuationIterator};

    #[test]
    fn bdd_sat_valuations_trivial() {
        let t = Bdd::mk_true(4);
        let f = Bdd::mk_false(4);
        assert!(f.sat_valuations().next().is_none());
        let mut sat_valuations: Vec<BddValuation> = t.sat_valuations().collect();
        let mut expected: Vec<BddValuation> = BddValuationIterator::new(4).collect();
        sat_valuations.sort();
        expected.sort();

        assert_eq!(sat_valuations.len(), 16);
        sat_valuations
            .into_iter()
            .zip(expected.into_iter())
            .for_each(|(a, b)| {
                assert_eq!(a, b);
            });
    }

    #[test]
    fn bdd_sat_valuations() {
        let variables = mk_5_variable_set();
        let bdd = variables.eval_expression_string("(v4 => (v1 & v2)) & (!v4 => (!v1 & v3))");

        let mut sat_valuations: Vec<BddValuation> = bdd.sat_valuations().collect();
        let mut expected: Vec<BddValuation> = BddValuationIterator::new(5)
            .filter(|valuation| bdd.eval_in(valuation))
            .collect();

        sat_valuations.sort();
        expected.sort();

        assert_eq!(sat_valuations.len(), expected.len());
        sat_valuations
            .into_iter()
            .zip(expected.into_iter())
            .for_each(|(a, b)| {
                assert_eq!(a, b);
            });
    }
}
