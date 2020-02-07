//! Boolean expressions are simple structures that represent boolean formulas explicitly.
//!
//! They can be parsed from a string representation (using `TryFrom`) and used to create
//! complex `Bdd`s:
//!
//! ```rust
//! use biodivine_lib_bdd::*;
//! let vars = BddVariableSet::new_anonymous(4);
//! let f: Bdd = vars.eval_expression_string("x_0 & !x_1 => (x_1 ^ x_3 <=> (x_0 | x_1))");
//! ```

/// **(internal)** Implements boolean expression evaluation for `BddVariableSet` and some utility methods.
mod _impl_boolean_expression;

/// **(internal)** Parsing functions for boolean expressions.
mod _impl_parser;

/// Recursive type for boolean expression tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BooleanExpression {
    Const(bool),
    Variable(String),
    Not(Box<BooleanExpression>),
    // TODO: Change this to binary op (also, add BooleanOp to stdlib) - maybe even this whole module?...
    And(Box<BooleanExpression>, Box<BooleanExpression>),
    Or(Box<BooleanExpression>, Box<BooleanExpression>),
    Xor(Box<BooleanExpression>, Box<BooleanExpression>),
    Imp(Box<BooleanExpression>, Box<BooleanExpression>),
    Iff(Box<BooleanExpression>, Box<BooleanExpression>),
}
