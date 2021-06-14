use crate::{BddCube, BddVariable};
use std::convert::TryFrom;

impl BddCube {
    /// Create a new empty cube over the given number of variables.
    pub fn new(num_vars: u16) -> BddCube {
        BddCube(vec![None; usize::from(num_vars)])
    }

    /// Fix value of the desired [variable] to the given [value].
    pub fn set(&mut self, variable: BddVariable, value: bool) {
        self.0[usize::from(variable.0)] = Some(value);
    }

    /// Free restriction on the specified [variable].
    pub fn unset(&mut self, variable: BddVariable) {
        self.0[usize::from(variable.0)] = None;
    }

    /// Return a vector of values which are fixed in this particular cube.
    /// The vector is sorted, starting with the "smallest" variable.
    pub fn values(&self) -> Vec<(BddVariable, bool)> {
        self.0
            .iter()
            .enumerate()
            .filter_map(|(i, v)| v.map(|value| (BddVariable(u16::try_from(i).unwrap()), value)))
            .collect()
    }
}
