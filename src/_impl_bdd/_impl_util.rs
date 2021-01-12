use crate::boolean_expression::BooleanExpression;
use crate::boolean_expression::BooleanExpression::Variable;
use crate::*;
use std::iter::Map;
use std::ops::Range;
use std::slice::Iter;

/// Several useful (mostly internal) low-level utility methods for `Bdd`s.
impl Bdd {
    /// The number of nodes in this `Bdd`. (Do not confuse with cardinality)
    pub fn size(&self) -> usize {
        self.0.len()
    }

    /// Number of variables in the corresponding `BddVariableSet`.
    pub fn num_vars(&self) -> u16 {
        // Assert: every BDD is not empty - it has at least the terminal zero node.
        self.0[0].var.0
    }

    /// True if this `Bdd` is exactly the `true` formula.
    pub fn is_true(&self) -> bool {
        self.0.len() == 2
    }

    /// True if this `Bdd` is exactly the `false` formula.
    pub fn is_false(&self) -> bool {
        self.0.len() == 1
    }

    /// Approximately computes the number of valuations satisfying the formula given
    /// by this `Bdd`.
    pub fn cardinality(&self) -> f64 {
        if self.is_false() {
            return 0.0;
        }
        let mut cache = vec![None; self.0.len()];
        cache[0] = Some(0.0);
        cache[1] = Some(1.0);
        let mut stack: Vec<BddPointer> = Vec::new();
        stack.push(self.root_pointer());
        while let Some(node) = stack.last() {
            if cache[node.0 as usize].is_some() {
                stack.pop();
            } else {
                let low = self.low_link_of(*node);
                let high = self.high_link_of(*node);
                let low_var = self.var_of(low).0;
                let high_var = self.var_of(high).0;
                let node_var = self.var_of(*node).0;
                let low = low.0 as usize;
                let high = high.0 as usize;

                if cache[low].is_some() && cache[high].is_some() {
                    let low_cardinality =
                        cache[low].unwrap() * 2.0_f64.powi((low_var - node_var - 1) as i32);
                    let high_cardinality =
                        cache[high].unwrap() * 2.0_f64.powi((high_var - node_var - 1) as i32);
                    cache[node.0 as usize] = Some(low_cardinality + high_cardinality);
                    stack.pop();
                } else {
                    if cache[low].is_none() {
                        stack.push(BddPointer(low as u32));
                    }
                    if cache[high].is_none() {
                        stack.push(BddPointer(high as u32));
                    }
                }
            }
        }
        let r = cache.last().unwrap().unwrap() * 2.0_f64.powi(self.0.last().unwrap().var.0 as i32);
        if r.is_nan() {
            f64::INFINITY
        } else {
            r
        }
    }

    /// If the `Bdd` is satisfiable, return some `BddValuation` that satisfies the `Bdd`.
    pub fn sat_witness(&self) -> Option<BddValuation> {
        if self.is_false() {
            return None;
        }
        let mut valuation: Vec<bool> = vec![false; self.num_vars() as usize];
        let mut stack: Vec<BddPointer> = Vec::new();
        stack.push(self.root_pointer());
        let mut find = BddPointer::one(); // index 1 is the true node

        // Run through the graph backwards, always looking for a parent of a specific node.
        // Initially, that node is a `1` terminal. Since parents are stored after children,
        // we know we will always find the parent.
        for node in self.pointers() {
            if node.is_terminal() {
                continue;
            }
            if self.low_link_of(node) == find {
                valuation[self.var_of(node).0 as usize] = false;
                find = node;
            }
            if self.high_link_of(node) == find {
                valuation[self.var_of(node).0 as usize] = true;
                find = node;
            }
        }

        Some(BddValuation::new(valuation))
    }

    /// Convert this `Bdd` to a `BooleanExpression` (using the variable names from the given
    /// `BddVariableSet`).
    ///
    pub fn to_boolean_expression(&self, variables: &BddVariableSet) -> BooleanExpression {
        if self.is_false() {
            return BooleanExpression::Const(false);
        }
        if self.is_true() {
            return BooleanExpression::Const(true);
        }

        let mut results: Vec<BooleanExpression> = Vec::with_capacity(self.0.len());
        results.push(BooleanExpression::Const(false)); // fake terminals
        results.push(BooleanExpression::Const(true)); // never used
        for node in 2..self.0.len() {
            // skip terminals
            let node_var = self.0[node].var;
            let var_name = variables.var_names[node_var.0 as usize].clone();

            let low_link = self.0[node].low_link;
            let high_link = self.0[node].high_link;
            let expression = if low_link.is_terminal() && high_link.is_terminal() {
                // Both links are terminal, which means this is an exactly determined variable
                if high_link.is_one() && low_link.is_zero() {
                    BooleanExpression::Variable(var_name)
                } else if high_link.is_zero() && low_link.is_one() {
                    BooleanExpression::Not(Box::new(BooleanExpression::Variable(var_name)))
                } else {
                    panic!("Invalid node {:?} in bdd {:?}.", self.0[node], self.0);
                }
            } else if low_link.is_terminal() {
                if low_link.is_zero() {
                    // a & high
                    BooleanExpression::And(
                        Box::new(BooleanExpression::Variable(var_name)),
                        Box::new(results[high_link.0 as usize].clone()),
                    )
                } else {
                    // !a | high
                    BooleanExpression::Or(
                        Box::new(BooleanExpression::Not(Box::new(
                            BooleanExpression::Variable(var_name),
                        ))),
                        Box::new(results[high_link.0 as usize].clone()),
                    )
                }
            } else if high_link.is_terminal() {
                if high_link.is_zero() {
                    // !a & low
                    BooleanExpression::And(
                        Box::new(BooleanExpression::Not(Box::new(
                            BooleanExpression::Variable(var_name),
                        ))),
                        Box::new(results[low_link.0 as usize].clone()),
                    )
                } else {
                    // a | low
                    BooleanExpression::Or(
                        Box::new(BooleanExpression::Variable(var_name)),
                        Box::new(results[low_link.0 as usize].clone()),
                    )
                }
            } else {
                // (a & high) | (!a & low)
                BooleanExpression::Or(
                    Box::new(BooleanExpression::And(
                        Box::new(Variable(var_name.clone())),
                        Box::new(results[high_link.0 as usize].clone()),
                    )),
                    Box::new(BooleanExpression::And(
                        Box::new(BooleanExpression::Not(Box::new(Variable(var_name.clone())))),
                        Box::new(results[low_link.0 as usize].clone()),
                    )),
                )
            };
            results.push(expression);
        }

        results.last().unwrap().clone()
    }

    /// **(internal)** Pointer to the root of the decision diagram.
    pub(crate) fn root_pointer(&self) -> BddPointer {
        BddPointer::from_index(self.0.len() - 1)
    }

    /// **(internal)** Get the low link of the node at a specified location.
    pub(crate) fn low_link_of(&self, node: BddPointer) -> BddPointer {
        self.0[node.to_index()].low_link
    }

    /// **(internal)** Get the high link of the node at a specified location.
    pub(crate) fn high_link_of(&self, node: BddPointer) -> BddPointer {
        self.0[node.to_index()].high_link
    }

    /// **(internal)** Get the conditioning variable of the node at a specified location.
    ///
    /// *Panics:* `node` must not be a terminal.
    pub(crate) fn var_of(&self, node: BddPointer) -> BddVariable {
        if cfg!(shields_up) && (node.is_one() || node.is_zero()) {
            panic!("Terminal nodes don't have a conditioning variable!");
        }
        self.0[node.to_index()].var
    }

    /// **(internal)** Create a new `Bdd` for the `false` formula.
    pub(crate) fn mk_false(num_vars: u16) -> Bdd {
        Bdd(vec![BddNode::mk_zero(num_vars)])
    }

    /// **(internal)** Create a new `Bdd` for the `true` formula.
    pub(crate) fn mk_true(num_vars: u16) -> Bdd {
        Bdd(vec![BddNode::mk_zero(num_vars), BddNode::mk_one(num_vars)])
    }

    pub(crate) fn mk_var(num_vars: u16, var: BddVariable) -> Bdd {
        let mut bdd = Self::mk_true(num_vars);
        bdd.push_node(BddNode::mk_node(var, BddPointer::zero(), BddPointer::one()));
        bdd
    }

    pub(crate) fn mk_not_var(num_vars: u16, var: BddVariable) -> Bdd {
        let mut bdd = Self::mk_true(num_vars);
        bdd.push_node(BddNode::mk_node(var, BddPointer::one(), BddPointer::zero()));
        bdd
    }

    pub(crate) fn mk_literal(num_vars: u16, var: BddVariable, value: bool) -> Bdd {
        if value {
            Self::mk_var(num_vars, var)
        } else {
            Self::mk_not_var(num_vars, var)
        }
    }

    /// **(internal)** Add a new node to an existing `Bdd`, making the new node the root of the `Bdd`.
    pub(crate) fn push_node(&mut self, node: BddNode) {
        self.0.push(node);
    }

    /// **(internal)** Create an iterator over all pointers of the `Bdd` (including terminals!).
    ///
    /// The iteration order is the same as the underlying representation, so you can expect
    /// terminals to be the first two nodes.
    pub(crate) fn pointers(&self) -> Map<Range<usize>, fn(usize) -> BddPointer> {
        (0..self.size()).map(BddPointer::from_index)
    }

    /// **(internal)** Create an iterator over all nodes of the `Bdd` (including terminals).
    pub(crate) fn nodes(&self) -> Iter<BddNode> {
        self.0.iter()
    }
}

#[cfg(test)]
mod tests {
    use crate::_test_util::mk_small_test_bdd;
    use crate::boolean_expression::BooleanExpression;
    use crate::*;
    use std::convert::TryFrom;

    #[test]
    fn bdd_impl() {
        let bdd = mk_small_test_bdd();

        assert_eq!(4, bdd.size());
        assert_eq!(5, bdd.num_vars());
        assert_eq!(BddPointer::from_index(3), bdd.root_pointer());
        assert_eq!(
            BddPointer::one(),
            bdd.low_link_of(BddPointer::from_index(2))
        );
        assert_eq!(
            BddPointer::zero(),
            bdd.high_link_of(BddPointer::from_index(2))
        );
        assert_eq!(BddVariable(3), bdd.var_of(BddPointer::from_index(2)));
        assert_eq!(
            BddPointer::zero(),
            bdd.low_link_of(BddPointer::from_index(3))
        );
        assert_eq!(
            BddPointer::from_index(2),
            bdd.high_link_of(BddPointer::from_index(3))
        );
        assert_eq!(BddVariable(2), bdd.var_of(BddPointer::from_index(3)));
    }

    #[test]
    fn bdd_cardinality() {
        // 5 variables, v3 & !v4
        let bdd = mk_small_test_bdd();
        assert_eq!(8.0, bdd.cardinality());
    }

    #[test]
    fn bdd_sat_witness_basic() {
        // v3 & !v4
        let bdd = mk_small_test_bdd();
        let expected = BddValuation(vec![false, false, true, false, false]);
        assert_eq!(bdd.sat_witness().unwrap(), expected);
        assert!(bdd.eval_in(&bdd.sat_witness().unwrap()));
    }

    #[test]
    fn bdd_sat_witness_advanced() {
        let vars = BddVariableSet::new_anonymous(5);
        let bdd = vars.eval_expression_string("x_0 & (x_1 | x_2) & (x_0 => x_4)");
        let valuation = BddValuation(vec![true, false, true, false, true]);
        assert_eq!(bdd.sat_witness().unwrap(), valuation);
        assert!(bdd.eval_in(&bdd.sat_witness().unwrap()));
    }

    #[test]
    fn bdd_to_formula() {
        let vars = BddVariableSet::new_anonymous(5);
        let bdd = vars.eval_expression_string("x_0 & (x_1 | x_2) & (x_0 => x_4)");
        let expected_expression =
            BooleanExpression::try_from("x_0 & ((x_1 & x_4) | (!x_1 & (x_2 & x_4)))").unwrap();
        let actual_expression = bdd.to_boolean_expression(&vars);
        assert_eq!(vars.eval_expression(&actual_expression), bdd);
        assert_eq!(bdd.to_boolean_expression(&vars), expected_expression);
    }
}
