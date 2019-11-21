//! **(internal)** BDD pointer identifies one of the nodes in the associated BDD array.
//!
//! BDD pointers are an internal type-safe wrapper around indices into BDD arrays.
//! Outside this crate, no one should know or care about their existence. Since
//! we can't reasonably expect a BDD to be larger than 2^32 right now, the pointer is
//! represented as `u32` instead of `usize`, because `usize` can be 64-bits and pointers
//! represent most of the memory consumed by our BDDs.
//!
//!

use std::fmt::{Display, Error, Formatter};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct BddPointer(u32);

/// For display purposes, pointer is just a number.
impl Display for BddPointer {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        return f.write_fmt(format_args!("{}", self.0));
    }
}

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

    /// Cast this pointer to standard usize index.
    pub fn to_index(&self) -> usize {
        return self.0 as usize;
    }

    /// Create a pointer from an usize index.
    pub fn from_index(index: usize) -> BddPointer {
        return BddPointer(index as u32);
    }

    /// Convert a `bool` value to valid terminal BDD pointer.
    pub fn from_bool(value: bool) -> BddPointer {
        return if value {
            BddPointer::one()
        } else {
            BddPointer::zero()
        };
    }

    /// If this pointer is a terminal, convert it to `bool`, otherwise return `None`.
    pub fn as_bool(&self) -> Option<bool> {
        return match self.0 {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        };
    }

    /// If this pointer corresponds to a terminal node, flip it (switching `1` to `0` and
    /// vice versa).
    pub fn flip_if_terminal(&mut self) {
        if self.0 < 2 {
            self.0 = (self.0 + 1) % 2;
        }
    }
}
