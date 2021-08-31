use crate::{
    Bdd, BddPathIterator, BddSatisfyingValuations, BddValuation, ValuationsOfClauseIterator,
};

impl Bdd {
    pub fn sat_valuations(&self) -> BddSatisfyingValuations {
        let mut path_iter = BddPathIterator::new(self);
        let val_iter = if let Some(first) = path_iter.next() {
            ValuationsOfClauseIterator::new(first, self.num_vars())
        } else {
            // This is a special case for the `false` BDD.
            ValuationsOfClauseIterator::empty()
        };
        BddSatisfyingValuations {
            bdd: self,
            paths: path_iter,
            valuations: val_iter,
        }
    }
}

impl Iterator for BddSatisfyingValuations<'_> {
    type Item = BddValuation;

    fn next(&mut self) -> Option<Self::Item> {
        let next_valuation = self.valuations.next();
        if next_valuation.is_some() {
            next_valuation
        } else {
            if let Some(next_path) = self.paths.next() {
                self.valuations = ValuationsOfClauseIterator::new(next_path, self.bdd.num_vars());
                // A new valuations iterator is never empty unless created using the `empty` constructor.
                self.valuations.next()
            } else {
                // We are done.
                None
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::_test_util::mk_5_variable_set;
    use crate::{Bdd, BddValuation, ValuationsOfClauseIterator};

    #[test]
    fn bdd_sat_valuations_trivial() {
        let t = Bdd::mk_true(4);
        let f = Bdd::mk_false(4);
        assert!(f.sat_valuations().next().is_none());
        let mut sat_valuations: Vec<BddValuation> = t.sat_valuations().collect();
        let mut expected: Vec<BddValuation> =
            ValuationsOfClauseIterator::new_unconstrained(4).collect();
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
        let mut expected: Vec<BddValuation> = ValuationsOfClauseIterator::new_unconstrained(5)
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
