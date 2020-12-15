use super::{Bdd, BddValuation, BddValuationIterator, BddVariable};
use crate::{BddNode, BddPointer};
use std::fmt::{Display, Error, Formatter};
use std::ops::Index;

impl BddValuation {
    /// Create a new valuation from a vector of variables.
    pub fn new(values: Vec<bool>) -> BddValuation {
        BddValuation(values)
    }

    /// Create a valuation with all variables set to false.
    pub fn all_false(num_vars: u16) -> BddValuation {
        BddValuation(vec![false; num_vars as usize])
    }

    /// Create a valuation with all variables set to true.
    pub fn all_true(num_vars: u16) -> BddValuation {
        BddValuation(vec![true; num_vars as usize])
    }

    /// Flip the value of a given Bdd variable.
    pub fn flip_value(&mut self, variable: BddVariable) {
        let i = variable.0 as usize;
        self.0[i] = !self.0[i];
    }

    pub fn clear(&mut self, variable: BddVariable) {
        self.0[(variable.0 as usize)] = false;
    }

    pub fn set(&mut self, variable: BddVariable) {
        self.0[(variable.0 as usize)] = true;
    }

    /// Convert the valuation to its underlying vector.
    pub fn vector(self) -> Vec<bool> {
        self.0
    }

    /// Get a value of a specific BDD variable in this valuation.
    pub fn value(&self, variable: BddVariable) -> bool {
        self.0[variable.0 as usize]
    }

    /// Number of variables in this valuation (used mostly for consistency checks).
    pub fn num_vars(&self) -> u16 {
        self.0.len() as u16
    }

    /// **(internal)** "Increment" this valuation if possible. Interpret the valuation as bit-vector and
    /// perform a standard increment. This can be used to iterate over all valuations.
    pub(crate) fn next(&self) -> Option<BddValuation> {
        let mut next_vec = self.0.clone();
        let mut carry = true; // initially, we want to increment
        for bit in &mut next_vec {
            let new_value = *bit ^ carry;
            let new_carry = *bit && carry;
            *bit = new_value;
            carry = new_carry;
            if !new_carry {
                break;
            } // if there is no carry, we can just break
        }

        if carry {
            None
        } else {
            Some(BddValuation(next_vec))
        }
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
        Ok(())
    }
}

/// Allow indexing of `BddValuation` using `BddVariables`.
impl Index<BddVariable> for BddValuation {
    type Output = bool;

    fn index(&self, index: BddVariable) -> &Self::Output {
        &self.0[usize::from(index.0)]
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
            node = if valuation[var] {
                self.high_link_of(node)
            } else {
                self.low_link_of(node)
            }
        }
        node.is_one()
    }
}

/// Convert a BddValuation to a Bdd with, well, exactly that one valuation.
impl From<BddValuation> for Bdd {
    fn from(valuation: BddValuation) -> Self {
        let mut bdd = Bdd::mk_true(valuation.num_vars());
        for i_var in (0..valuation.num_vars()).rev() {
            let var = BddVariable(i_var);
            let is_true = valuation.value(var);
            let low_link = if is_true {
                BddPointer::zero()
            } else {
                bdd.root_pointer()
            };
            let high_link = if is_true {
                bdd.root_pointer()
            } else {
                BddPointer::zero()
            };
            bdd.push_node(BddNode::mk_node(var, low_link, high_link));
        }
        bdd
    }
}

impl BddValuationIterator {
    /// Create a new iterator with a specified number of variables.
    pub fn new(num_vars: u16) -> BddValuationIterator {
        BddValuationIterator(Some(BddValuation(vec![false; num_vars as usize])))
    }
}

impl Iterator for BddValuationIterator {
    type Item = BddValuation;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(valuation) = &self.0 {
            let ret = valuation.clone();
            let next = valuation.next();
            self.0 = next;
            Some(ret)
        } else {
            None
        }
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
