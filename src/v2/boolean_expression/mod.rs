//! Boolean expressions are a simple structures that represent boolean formulas explicitly.
//!
//! They can be parsed from a string representation (using `TryFrom`) and used to create
//! complex `Bdd`s:
//!
//! TODO: Usage example.

mod impl_boolean_expression;
mod impl_parser;

/// Recursive type for boolean expression tree.
#[derive(Debug, Eq, PartialEq)]
pub enum BooleanExpression {
    Variable(String),
    Not(Box<BooleanExpression>),
    And(Box<BooleanExpression>, Box<BooleanExpression>),
    Or(Box<BooleanExpression>, Box<BooleanExpression>),
    Xor(Box<BooleanExpression>, Box<BooleanExpression>),
    Imp(Box<BooleanExpression>, Box<BooleanExpression>),
    Iff(Box<BooleanExpression>, Box<BooleanExpression>),
}
