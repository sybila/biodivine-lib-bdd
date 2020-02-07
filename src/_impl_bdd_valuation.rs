use super::{Bdd, BddValuation, BddValuationIterator, BddVariable};
use std::fmt::{Display, Error, Formatter};

impl BddValuation {
    // TODO: This a very low-level API. We should be able to create valuations in some safer manner.
    /// Create a new valuation from a vector of variables.
    pub fn new(values: Vec<bool>) -> BddValuation {
        return BddValuation(values);
    }

    /// Get a value of a specific BDD variable in this valuation.
    pub fn value(&self, variable: BddVariable) -> bool {
        return self.0[variable.0 as usize];
    }

    /// Number of variables in this valuation (used mostly for consistency checks).
    pub fn num_vars(&self) -> u16 {
        return self.0.len() as u16;
    }

    /// "Increment" this valuation if possible. Interpret the valuation as bit-vector and
    /// perform a standard increment. This can be used to iterate over all valuations.
    fn next(&self) -> Option<BddValuation> {
        let mut next_vec = self.0.clone();
        let mut carry = true; // initially, we want to increment
        for i in 0..next_vec.len() {
            let new_value = next_vec[i] ^ carry;
            let new_carry = next_vec[i] && carry;
            next_vec[i] = new_value;
            carry = new_carry;
            if !new_carry {
                break;
            } // if there is no carry, we can just break
        }

        return if carry {
            None
        } else {
            Some(BddValuation(next_vec))
        };
    }
}

impl Display for BddValuation {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        if self.0.is_empty() {
            write!(f, "[]")?;
        } else {
            write!(f, "[{}", if self.0[0] { 1 } else { 0 })?;
            for i in 1..self.0.len() {
                write!(f, ",{}", if self.0[i] { 1 } else { 0 })?
            }
            write!(f, "]")?;
        }
        return Ok(());
    }
}

/// Methods for working with `Bdd` valuations.
impl Bdd {
    /// Evaluate this `Bdd` in a specified `BddValuation`.
    ///
    /// Panics if the number of variables in the valuation is different than the `Bdd`.
    pub fn eval_in(&self, valuation: &BddValuation) -> bool {
        if cfg!(feature = "shields_up") && valuation.num_vars() != self.num_vars() {
            panic!(
                "Universe has {} variables, but valuation has {}.",
                self.num_vars(),
                valuation.num_vars()
            )
        }
        let mut node = self.root_pointer();
        while !node.is_terminal() {
            let var = self.var_of(node);
            node = if valuation.value(var) {
                self.high_link_of(node)
            } else {
                self.low_link_of(node)
            }
        }
        return node.is_one();
    }
}

impl BddValuationIterator {
    /// Create a new iterator with a specified number of variables.
    pub fn new(num_vars: u16) -> BddValuationIterator {
        return BddValuationIterator(Some(BddValuation(vec![false; num_vars as usize])));
    }
}

impl Iterator for BddValuationIterator {
    type Item = BddValuation;

    fn next(&mut self) -> Option<Self::Item> {
        return if let Some(valuation) = &self.0 {
            let ret = valuation.clone();
            let next = valuation.next();
            self.0 = next;
            Some(ret)
        } else {
            None
        };
    }
}

#[cfg(test)]
mod tests {
    use super::super::{BddValuation, BddValuationIterator, BddVariableSet};
    use crate::bdd;

    #[test]
    fn bdd_universe_eval() {
        let universe = BddVariableSet::new_anonymous(2);
        let v1 = universe.mk_var_by_name("x_0");
        let v2 = universe.mk_var_by_name("x_1");
        let bdd = bdd!(v1 & (!v2));
        assert_eq!(true, bdd.eval_in(&BddValuation::new(vec![true, false])));
        assert_eq!(false, bdd.eval_in(&BddValuation::new(vec![true, true])));
        assert_eq!(false, bdd.eval_in(&BddValuation::new(vec![false, false])));
        assert_eq!(false, bdd.eval_in(&BddValuation::new(vec![false, false])));
    }

    #[test]
    fn bdd_valuation_iterator_empty() {
        let mut it = BddValuationIterator::new(0);
        assert_eq!(it.next(), Some(BddValuation::new(Vec::new())));
        assert_eq!(it.next(), None);
    }

    #[test]
    #[should_panic]
    fn bdd_universe_eval_invalid() {
        let universe = BddVariableSet::new_anonymous(2);
        let tt = universe.mk_true();
        tt.eval_in(&BddValuation::new(vec![true, true, true]));
    }

    #[test]
    fn bdd_valuation_print() {
        assert_eq!(
            "[0,1,1,0]".to_string(),
            BddValuation::new(vec![false, true, true, false]).to_string()
        );
    }
}
