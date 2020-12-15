use super::super::{Bdd, BddVariableSet};
use super::BooleanExpression;
use super::BooleanExpression::*;
use super::_impl_parser::parse_boolean_expression;
use std::convert::TryFrom;
use std::fmt::{Display, Error, Formatter};

impl TryFrom<&str> for BooleanExpression {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        parse_boolean_expression(value)
    }
}

impl Display for BooleanExpression {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Const(value) => write!(f, "{}", value),
            Variable(name) => write!(f, "{}", name),
            Not(inner) => write!(f, "!{}", inner),
            And(l, r) => write!(f, "({} & {})", l, r),
            Or(l, r) => write!(f, "({} | {})", l, r),
            Xor(l, r) => write!(f, "({} ^ {})", l, r),
            Imp(l, r) => write!(f, "({} => {})", l, r),
            Iff(l, r) => write!(f, "({} <=> {})", l, r),
        }
    }
}

/// Methods for evaluating boolean expressions.
impl BddVariableSet {
    /// Evaluate the given `BooleanExpression` in the context of this `BddVariableSet`. Return `None` if some
    /// variables are unknown.
    pub fn safe_eval_expression(&self, expression: &BooleanExpression) -> Option<Bdd> {
        match expression {
            Const(value) => Some(if *value {
                self.mk_true()
            } else {
                self.mk_false()
            }),
            Variable(name) => self.var_by_name(name).map(|v| self.mk_var(v)),
            Not(inner) => self.safe_eval_expression(inner).map(|b| b.not()),
            And(l, r) => {
                let left = self.safe_eval_expression(l)?;
                let right = self.safe_eval_expression(r)?;
                Some(left.and(&right))
            }
            Or(l, r) => {
                let left = self.safe_eval_expression(l)?;
                let right = self.safe_eval_expression(r)?;
                Some(left.or(&right))
            }
            Xor(l, r) => {
                let left = self.safe_eval_expression(l)?;
                let right = self.safe_eval_expression(r)?;
                Some(left.xor(&right))
            }
            Imp(l, r) => {
                let left = self.safe_eval_expression(l)?;
                let right = self.safe_eval_expression(r)?;
                Some(left.imp(&right))
            }
            Iff(l, r) => {
                let left = self.safe_eval_expression(l)?;
                let right = self.safe_eval_expression(r)?;
                Some(left.iff(&right))
            }
        }
    }

    /// Evaluate the given `BooleanExpression` in the context of this `BddVariableSet`. Panic if some
    /// variables are unknown.
    pub fn eval_expression(&self, expression: &BooleanExpression) -> Bdd {
        self.safe_eval_expression(expression).unwrap()
    }

    /// Evaluate the given `String` as a `BooleanExpression` in the context of this `BddVariableSet`.
    ///
    /// Panics if the expression cannot be parsed or contains unknown variables.
    pub fn eval_expression_string(&self, expression: &str) -> Bdd {
        let parsed = BooleanExpression::try_from(expression).unwrap();
        self.eval_expression(&parsed)
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::BddVariableSet;
    use crate::bdd;

    #[test]
    fn bdd_universe_eval_boolean_formula() {
        let variables = BddVariableSet::new_anonymous(5);
        let formula = "((x_0 & !!x_1) => (!(x_2 | (!!x_0 & x_1)) <=> (x_3 ^ x_4)))";
        let x_0 = variables.mk_var_by_name("x_0");
        let x_1 = variables.mk_var_by_name("x_1");
        let x_2 = variables.mk_var_by_name("x_2");
        let x_3 = variables.mk_var_by_name("x_3");
        let x_4 = variables.mk_var_by_name("x_4");

        let expected = bdd!(((x_0 & (!(!x_1))) => ((!(x_2 | ((!(!x_0)) & x_1))) <=> (x_3 ^ x_4))));
        let evaluated = variables.eval_expression_string(formula);

        assert_eq!(expected, evaluated);
    }
}
