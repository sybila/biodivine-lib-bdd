use super::BddVariable;

/// BDD valuation describes one assignment of variables in the BDD universe.
#[derive(Clone, Debug)]
pub struct BddValuation(Vec<bool>);

/// BDD valuation assigns each boolean variable a value. It can be used
/// as a witness of BDD non-emptiness, since one can evaluate every BDD
/// in some corresponding valuation and get a true/false value.
impl BddValuation {

    /// Create a new valuation from a vector of variables.
    ///
    /// TODO: This a very low-level API. We should be able to create valuations in some safer manner.
    pub fn new(values: Vec<bool>) -> BddValuation {
        return BddValuation(values);
    }

    /// Get a value of a specific BDD variable in this valuation.
    pub fn value(&self, variable: &BddVariable) -> bool {
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
        let mut carry = true;   // initially, we want to increment
        for i in 0..next_vec.len() {
            let new_value = next_vec[i] ^ carry;
            let new_carry = next_vec[i] && carry;
            next_vec[i] = new_value;
            carry = new_carry;
            if !new_carry { break } // if there is no carry, we can just break
        }

        return if carry { None } else { Some(BddValuation(next_vec)) }
    }

}

/// BDD valuation iterator allows to exhaustively iterate over all valuations
/// with a certain number of variables.
///
/// Be aware of the exponential time complexity of such operation!
pub struct BddValuationIterator(Option<BddValuation>);

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
        } else { None }
    }
}