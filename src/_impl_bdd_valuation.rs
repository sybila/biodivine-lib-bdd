use super::{Bdd, BddValuation, BddVariable};
use crate::{BddNode, BddPartialValuation, BddPointer, ValuationsOfClauseIterator};
use std::convert::TryFrom;
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

    /// Set the value of the given `variable` to `false`.
    pub fn clear(&mut self, variable: BddVariable) {
        self.0[(variable.0 as usize)] = false;
    }

    /// Set the value of the given `variable` to `true`.
    pub fn set(&mut self, variable: BddVariable) {
        self.0[(variable.0 as usize)] = true;
    }

    /// Update `value` of the given `variable`.
    pub fn set_value(&mut self, variable: BddVariable, value: bool) {
        self.0[(variable.0 as usize)] = value;
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

    /// Returns true if the values set in this valuation match the values fixed in the
    /// given partial valuation. I.e. the two valuations agree on fixed values.
    ///
    /// In other words `this >= valuation` in terms of specificity.
    pub fn extends(&self, valuation: &BddPartialValuation) -> bool {
        for var_id in 0..self.num_vars() {
            let var = BddVariable(var_id);
            if let Some(value) = valuation.get_value(var) {
                if value != self.value(var) {
                    return false;
                }
            }
        }

        true
    }

    /// **(internal)** "Increment" this valuation if possible. Interpret the valuation as bit-vector and
    /// perform a standard increment. This can be used to iterate over all valuations.
    ///
    /// You can provide a `clause` which restricts which variables of the valuation can change.
    /// That is, any variable that has a fixed value in `clause` is considered to be fixed.
    /// Note that the method also *checks* whether the fixed values are the same as in the
    /// `clause` (i.e. the valuation and clause are mutually compatible) and **panics** if
    /// inconsistencies are found.
    pub(crate) fn next(&self, clause: &BddPartialValuation) -> Option<BddValuation> {
        let mut result = self.clone();
        let mut carry = true; // first value needs to be incremented

        for var_id in 0..self.num_vars() {
            let variable = BddVariable(var_id);

            if clause.has_value(variable) {
                // Do not increment variables that are fixed.
                assert_eq!(clause.get_value(variable), Some(self.value(variable)));
                continue;
            }

            let new_value = self.value(variable) ^ carry;
            let new_carry = self.value(variable) && carry;

            result.set_value(variable, new_value);
            carry = new_carry;
            if !new_carry {
                break;
            } // No need to continue incrementing.
        }

        if carry {
            None
        } else {
            Some(result)
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
    pub fn eval_in(&self, valuation: &BddValuation) -> bool {
        debug_assert!(
            valuation.num_vars() == self.num_vars(),
            "Incompatible variable count."
        );
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

/// If possible, convert the given partial valuation to valuation with the same
/// number of variables. Partial valuation must contain values of all variables.
impl TryFrom<BddPartialValuation> for BddValuation {
    type Error = ();

    fn try_from(value: BddPartialValuation) -> Result<Self, Self::Error> {
        let mut result = BddValuation::all_false(value.0.len() as u16);
        for var_id in 0..result.num_vars() {
            let var = BddVariable(var_id);
            if let Some(value) = value.get_value(var) {
                result.set_value(var, value);
            } else {
                return Err(());
            }
        }

        Ok(result)
    }
}

// This code allows compatibility with older implementations and will be removed
// once `BddValuationIterator` is removed.

#[allow(deprecated)]
impl super::BddValuationIterator {
    /// Create a new iterator with a specified number of variables.
    pub fn new(num_vars: u16) -> super::BddValuationIterator {
        super::BddValuationIterator(ValuationsOfClauseIterator::new_unconstrained(num_vars))
    }
}

#[allow(deprecated)]
impl Iterator for super::BddValuationIterator {
    type Item = BddValuation;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

#[cfg(test)]
mod tests {
    use super::super::{BddValuation, BddVariableSet};
    use crate::{bdd, BddPartialValuation, BddVariable};

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
    #[should_panic]
    #[cfg(debug_assertions)]
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

    #[test]
    fn valuation_consistency() {
        let total = BddValuation::new(vec![true, false, true, false]);
        let partial =
            BddPartialValuation::from_values(&[(BddVariable(1), false), (BddVariable(2), true)]);

        assert!(total.extends(&partial));

        let total = BddValuation::new(vec![true, true, true, false]);
        assert!(!total.extends(&partial));
    }
}
