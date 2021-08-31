use crate::{Bdd, BddPartialValuation, BddValuation};

/// Utilities for extracting interesting valuations and paths from a `Bdd`.
impl Bdd {
    /// Return the lexicographically smallest satisfying valuation of this `Bdd`.
    ///
    /// (In this context, lexicographically means `0 < 1`, with greatest variable id
    /// being the most significant).
    pub fn first_valuation(&self) -> Option<BddValuation> {
        if self.is_false() {
            return None;
        }

        let mut valuation = BddValuation::all_false(self.num_vars());
        let mut node = self.root_pointer();
        while !node.is_terminal() {
            if self.low_link_of(node).is_zero() {
                valuation.set(self.var_of(node));
                node = self.high_link_of(node);
            } else {
                node = self.low_link_of(node);
            }
        }

        Some(valuation)
    }

    /// Return the lexicographically largest satisfying valuation of this `Bdd`.
    ///
    /// (In this context, lexicographically means `0 < 1`, with greatest variable id
    /// being the most significant).
    pub fn last_valuation(&self) -> Option<BddValuation> {
        if self.is_false() {
            return None;
        }

        let mut valuation = BddValuation::all_true(self.num_vars());
        let mut node = self.root_pointer();
        while !node.is_terminal() {
            if self.high_link_of(node).is_zero() {
                valuation.clear(self.var_of(node));
                node = self.low_link_of(node);
            } else {
                node = self.high_link_of(node);
            }
        }

        Some(valuation)
    }

    /// Return the lexicographically smallest path in this `Bdd`, represented as
    /// a *conjunctive* clause.
    pub fn first_path(&self) -> Option<BddPartialValuation> {
        if self.is_false() {
            return None;
        }

        let mut valuation = BddPartialValuation::empty();
        let mut node = self.root_pointer();
        while !node.is_terminal() {
            if self.low_link_of(node).is_zero() {
                valuation.set_value(self.var_of(node), true);
                node = self.high_link_of(node);
            } else {
                node = self.low_link_of(node);
            }
        }

        Some(valuation)
    }
}
