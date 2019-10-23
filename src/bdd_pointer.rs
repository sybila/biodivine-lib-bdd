//! **(internal)** BDD pointer identifies one of the nodes in the associated BDD.
//!
//! TODO: Example/Image?

/// BDD nodes represent individual vertices of the BDD directed acyclic graph.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct BddPointer(pub u32);

impl BddPointer {

    /// Make a new pointer to the `0` terminal node.
    pub fn zero() -> BddPointer {
        return BddPointer(0);
    }

    /// Make a new pointer to the `1` terminal node.
    pub fn one() -> BddPointer {
        return BddPointer(1);
    }

    /// Check if the pointer corresponds to the `0` terminal.
    pub fn is_zero(&self) -> bool {
        return self.0 == 0;
    }

    /// Check if the pointer corresponds to the `1` terminal.
    pub fn is_one(&self) -> bool {
        return self.0 == 1;
    }

    /// Check if the pointer corresponds to the `0` or `1` terminal.
    pub fn is_terminal(&self) -> bool {
        return self.0 < 2;
    }

    /// If this pointer corresponds to a terminal node, flip it (switching `1` to `0` and
    /// vice versa).
    pub fn flip_if_terminal(&mut self) {
        if self.0 < 2 {
            self.0 = (self.0 + 1) % 2;
        }
    }

}