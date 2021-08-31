use crate::{BddPartialValuation, BddValuation, ValuationsOfClauseIterator};
use std::mem::swap;

impl ValuationsOfClauseIterator {
    /// Create an empty valuation iterator.
    pub fn empty() -> ValuationsOfClauseIterator {
        ValuationsOfClauseIterator {
            next_valuation: None,
            clause: BddPartialValuation::empty(),
        }
    }

    /// Create a new valuation iterator from a conjunctive clause and a variable count.
    ///
    /// The iterator will visit every valuation in the `2^num_vars` space that also satisfies
    /// the given `clause`.
    pub fn new(clause: BddPartialValuation, num_vars: u16) -> ValuationsOfClauseIterator {
        let mut first_valuation = BddValuation::all_false(num_vars);
        for (var, value) in clause.to_values() {
            if value {
                first_valuation.flip_value(var);
            }
        }

        ValuationsOfClauseIterator {
            next_valuation: Some(first_valuation),
            clause,
        }
    }

    /// Create a new valuation iterator which is not constrained by any clause and will
    /// iterate over all `2^num_vars`.
    pub fn new_unconstrained(num_vars: u16) -> ValuationsOfClauseIterator {
        ValuationsOfClauseIterator {
            next_valuation: Some(BddValuation::all_false(num_vars)),
            clause: BddPartialValuation::empty(),
        }
    }
}

impl Iterator for ValuationsOfClauseIterator {
    type Item = BddValuation;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(valuation) = &self.next_valuation {
            // Compute the next valuation and then swap it with the current value.
            // In the end, result contains self.next_valuation and next_valuation
            // contains the result of valuation.next.
            let mut result = valuation.next(&self.clause);
            swap(&mut result, &mut self.next_valuation);
            result
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{BddPartialValuation, BddValuation, BddVariable, ValuationsOfClauseIterator};
    use std::convert::TryFrom;

    #[test]
    fn valuations_of_clause_iterator_unconstrained() {
        let singleton = ValuationsOfClauseIterator::new_unconstrained(0);
        assert_eq!(1, singleton.count());
        let three_vars = ValuationsOfClauseIterator::new_unconstrained(3);
        assert_eq!(8, three_vars.count());
    }

    #[test]
    fn valuations_of_clause_iterator_constrained() {
        let x1 = BddVariable(0);
        let x2 = BddVariable(1);
        let x3 = BddVariable(2);
        let clause = BddPartialValuation::from_values(&[(x1, true), (x2, false), (x3, true)]);
        let singleton = ValuationsOfClauseIterator::new(clause.clone(), 3);
        assert_eq!(1, singleton.clone().count());
        assert_eq!(
            BddValuation::try_from(clause).unwrap(),
            singleton.clone().next().unwrap()
        );

        let clause = BddPartialValuation::from_values(&[(x1, true), (x3, false)]);
        let iterator = ValuationsOfClauseIterator::new(clause.clone(), 4);
        assert_eq!(4, iterator.clone().count());
        iterator.for_each(|valuation| {
            assert!(valuation.extends(&clause));
        })
    }
}
