use crate::{BddPartialValuation, BddVariable};

impl BddPartialValuation {

    /// Creates an empty valuation without any variables set.
    pub fn empty() -> BddPartialValuation {
        BddPartialValuation(Vec::new())
    }

    /// Create a partial valuation from a list of variables and values.
    ///
    /// The order of variables in the slice can be arbitrary. The operation does not perform
    /// any uniqueness checking. If the slice contains multiple copies of the same variable,
    /// the last value is accepted.
    pub fn from_values(values: &[(BddVariable, bool)]) -> BddPartialValuation {
        let mut result = Self::empty();
        for (id, value) in values {
            result.set_value(*id, *value)
        }
        result
    }

    /// Consume this valuation and turn it into a vector of values which are stored in it.
    pub fn to_values(&self) -> Vec<(BddVariable, bool)> {
        self.0.iter()
            .enumerate()
            .filter_map(|(i, value)| {
                value.map(|value| (BddVariable(i as u16), value))
            })
            .collect()
    }

    /// Get a value stored for the given variable id, if any.
    pub fn get_value(&self, id: BddVariable) -> Option<bool> {
        let index = usize::from(id.0);
        self.0.get(index).cloned().flatten()
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

}

impl Default for BddPartialValuation {
    fn default() -> Self {
        Self::empty()
    }
}

#[cfg(test)]
mod tests {
    use crate::{BddPartialValuation, BddVariable};

    #[test]
    fn basic_partial_valuation_properties() {
        let v1 = BddVariable(1);
        let v2 = BddVariable(2);
        let v5 = BddVariable(5);

        let mut a = BddPartialValuation::default();
        a.set_value(v1, true);
        assert!(a.has_value(v1));
        assert_eq!(Some(true), a.get_value(v1));
        a.set_value(v2, false);
        a.unset_value(v1);
        assert!(a.has_value(v2));
        assert!(!a.has_value(v1));

        a.set_value(v5, true);
        a.set_value(v1, false);

        let b = BddPartialValuation::from_values(&[(v1, false), (v5, true), (v2, false)]);

        assert_eq!(a, b);
        assert_eq!(a, BddPartialValuation::from_values(&a.to_values()));
    }

}