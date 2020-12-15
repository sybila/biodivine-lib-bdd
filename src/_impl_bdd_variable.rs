use super::*;
use std::fmt::{Display, Error, Formatter};

impl Display for BddVariable {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        f.write_fmt(format_args!("{}", self.0))
    }
}

impl BddVariable {
    /// Convert to little endian bytes
    pub(super) fn to_le_bytes(&self) -> [u8; 2] {
        self.0.to_le_bytes()
    }

    /// Read from little endian byte representation
    pub(super) fn from_le_bytes(bytes: [u8; 2]) -> BddVariable {
        BddVariable(u16::from_le_bytes(bytes))
    }
}
