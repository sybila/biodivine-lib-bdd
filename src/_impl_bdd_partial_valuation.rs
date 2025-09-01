use crate::{BddPartialValuation, BddValuation, BddVariable};
use std::cmp::min;
use std::convert::TryFrom;
use std::hash::{Hash, Hasher};
use std::ops::{Index, IndexMut};

impl BddPartialValuation {
    /// Creates an empty valuation without any variables set.
    pub fn empty() -> BddPartialValuation {
        BddPartialValuation(Vec::new())
    }

    /// True if the valuation contains no values.
    pub fn is_empty(&self) -> bool {
        self.0.iter().all(|it| it.is_none())
    }

    /// Return the number of fixed variables in this valuation.
    pub fn cardinality(&self) -> u16 {
        u16::try_from(self.0.iter().filter(|it| it.is_some()).count()).unwrap()
    }

    /// Return the identifier of the last fixed variable in this valuation. Returns `None` if
    /// no variable is fixed.
    pub fn last_fixed_variable(&self) -> Option<BddVariable> {
        for i in (0..self.0.len()).rev() {
            if self.0[i].is_some() {
                return Some(BddVariable(i as u16));
            }
        }
        None
    }

    /// Create a partial valuation from a list of variables and values.
    ///
    /// The order of variables in the slice can be arbitrary. The operation does not perform
    /// any uniqueness checking. If the slice contains multiple copies of the same variable,
    /// the last value is accepted.
    pub fn from_values(values: &[(BddVariable, bool)]) -> BddPartialValuation {
        Self::from_values_iter(values.into_iter().copied())
    }

    /// Create a partial valuation from a list of variables and values.
    ///
    /// The order of variables in the slice can be arbitrary. The operation does not perform
    /// any uniqueness checking. If the slice contains multiple copies of the same variable,
    /// the last value is accepted.
    pub fn from_values_iter<I: Iterator<Item = (BddVariable, bool)>>(
        values: I,
    ) -> BddPartialValuation {
        let mut result = Self::empty();
        for (id, value) in values {
            result.set_value(id, value)
        }
        result
    }

    /// Consume this valuation and turn it into a vector of values which are stored in it.
    pub fn to_values(&self) -> Vec<(BddVariable, bool)> {
        self.0
            .iter()
            .enumerate()
            .filter_map(|(i, value)| value.map(|value| (BddVariable(i as u16), value)))
            .collect()
    }

    /// Get a value stored for the given variable id, if any.
    pub fn get_value(&self, id: BddVariable) -> Option<bool> {
        let index = usize::from(id.0);
        if index < self.0.len() {
            self.0[index]
        } else {
            None
        }
    }

    /// Returns `true` if this valuation has the value of `id` variable set.
    pub fn has_value(&self, id: BddVariable) -> bool {
        self.get_value(id).is_some()
    }

    /// Update value of the given `id` variable.
    pub fn set_value(&mut self, id: BddVariable, value: bool) {
        let cell = self.mut_cell(id);
        *cell = Some(value);
    }

    /// Remove value of a variable from this valuation.
    ///
    /// If the value was not set, this operation has no effect.
    pub fn unset_value(&mut self, id: BddVariable) {
        let cell = self.mut_cell(id);
        *cell = None;
    }

    fn mut_cell(&mut self, id: BddVariable) -> &mut Option<bool> {
        let index = usize::from(id.0);
        while self.0.len() <= index {
            self.0.push(None);
        }
        &mut self.0[index]
    }

    /// Returns true if the values set in this partial valuation match the values fixed in the
    /// other given valuation. I.e. the two valuations agree on fixed values in `valuation`.
    ///
    /// In other words `this >= valuation` in terms of specificity.
    pub fn extends(&self, valuation: &BddPartialValuation) -> bool {
        for var_id in 0..(valuation.0.len() as u16) {
            let var = BddVariable(var_id);
            let expected = valuation.get_value(var);
            if expected.is_some() && self.get_value(var) != expected {
                return false;
            }
        }

        true
    }
}

impl Default for BddPartialValuation {
    fn default() -> Self {
        Self::empty()
    }
}

impl From<BddValuation> for BddPartialValuation {
    fn from(value: BddValuation) -> Self {
        value.to_partial_valuation()
    }
}

impl Index<BddVariable> for BddPartialValuation {
    type Output = Option<bool>;

    fn index(&self, index: BddVariable) -> &Self::Output {
        let index = usize::from(index.0);
        if index < self.0.len() {
            &self.0[index]
        } else {
            &None
        }
    }
}

impl IndexMut<BddVariable> for BddPartialValuation {
    fn index_mut(&mut self, index: BddVariable) -> &mut Self::Output {
        self.mut_cell(index)
    }
}

impl PartialEq for BddPartialValuation {
    fn eq(&self, other: &Self) -> bool {
        let min_len = min(self.0.len(), other.0.len());
        for i in 0..min_len {
            if self.0[i] != other.0[i] {
                return false;
            }
        }
        for j in min_len..self.0.len() {
            if self.0[j].is_some() {
                return false;
            }
        }
        for j in min_len..other.0.len() {
            if other.0[j].is_some() {
                return false;
            }
        }
        true
    }
}

impl Eq for BddPartialValuation {}

impl Hash for BddPartialValuation {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for (var, value) in self.0.iter().enumerate() {
            if let Some(value) = value {
                state.write_usize(var);
                state.write_u8(u8::from(*value))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{BddPartialValuation, BddValuation, BddVariable};
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    #[test]
    fn basic_partial_valuation_properties() {
        let v1 = BddVariable(1);
        let v2 = BddVariable(2);
        let v5 = BddVariable(5);

        let mut a = BddPartialValuation::default();
        assert!(a.last_fixed_variable().is_none());
        assert!(!a.has_value(v1));
        a.set_value(v1, true);
        assert!(a.has_value(v1));
        assert_eq!(Some(true), a.get_value(v1));
        a.set_value(v2, false);
        a.unset_value(v1);
        assert!(a.has_value(v2));
        assert!(!a.has_value(v1));

        a.set_value(v5, true);
        assert_eq!(Some(v5), a.last_fixed_variable());
        a.set_value(v1, false);
        assert_eq!(3, a.cardinality());

        let b = BddPartialValuation::from_values(&[(v1, false), (v5, true), (v2, false)]);

        assert_eq!(a, b);
        assert_eq!(a, BddPartialValuation::from_values(&a.to_values()));

        a.unset_value(v5);
        let b = BddPartialValuation::from_values(&[(v1, false), (v2, false)]);
        assert_eq!(a, b);

        let mut hasher_a = DefaultHasher::new();
        let mut hasher_b = DefaultHasher::new();
        a.hash(&mut hasher_a);
        b.hash(&mut hasher_b);
        assert_eq!(hasher_a.finish(), hasher_b.finish());
    }

    #[test]
    fn valuation_conversions() {
        let mut val = BddValuation::all_false(24);
        val[BddVariable(14)] = true;
        val[BddVariable(21)] = true;

        assert_eq!(
            BddPartialValuation::from(val.clone()),
            BddPartialValuation::from_values(&val.to_values())
        );

        let mut partial = BddPartialValuation::from(val.clone());
        partial[BddVariable(13)] = Some(true);
        val[BddVariable(13)] = true;

        assert_eq!(val, BddValuation::try_from(partial).unwrap());
    }
}
