use super::*;
use std::{
    convert::TryFrom,
    fmt::{Display, Formatter},
};

impl BddVariableSet {
    /// Create a new `BddVariableSet` with anonymous variables $(x_0, \ldots, x_n)$ where $n$ is
    /// the `num_vars` parameter.
    pub fn new_anonymous(num_vars: u16) -> BddVariableSet {
        if num_vars >= (u16::MAX - 1) {
            panic!(
                "Too many BDD variables. There can be at most {} variables.",
                u16::MAX - 1
            )
        }
        BddVariableSet {
            num_vars,
            var_names: (0..num_vars).map(|i| format!("x_{}", i)).collect(),
            var_index_mapping: (0..num_vars).map(|i| (format!("x_{}", i), i)).collect(),
        }
    }

    /// Create a new `BddVariableSet` with the given named variables. Same as using the
    /// `BddVariablesBuilder` with this name vector, but no `BddVariable` objects are returned.
    ///
    /// *Panics:* `vars` must contain unique names which are allowed as variable names.
    pub fn new(vars: &[&str]) -> BddVariableSet {
        let mut builder = BddVariableSetBuilder::new();
        builder.make_variables(vars);
        builder.build()
    }

    /// Return the number of variables in this set.
    pub fn num_vars(&self) -> u16 {
        self.num_vars
    }

    /// Create a `BddVariable` based on a variable name. If the name does not appear
    /// in this set, return `None`.
    pub fn var_by_name(&self, name: &str) -> Option<BddVariable> {
        self.var_index_mapping.get(name).cloned().map(BddVariable)
    }

    /// Provides a vector of all `BddVariable`s in this set.
    pub fn variables(&self) -> Vec<BddVariable> {
        (0..self.num_vars).map(BddVariable).collect()
    }

    /// Obtain the name of a specific `BddVariable`.
    pub fn name_of(&self, variable: BddVariable) -> String {
        self.var_names[variable.0 as usize].clone()
    }

    /// Create a `Bdd` corresponding to the `true` formula.
    pub fn mk_true(&self) -> Bdd {
        Bdd::mk_true(self.num_vars)
    }

    /// Create a `Bdd` corresponding to the `false` formula.
    pub fn mk_false(&self) -> Bdd {
        Bdd::mk_false(self.num_vars)
    }

    /// Create a `Bdd` corresponding to the $v$ formula where `v` is a specific variable in
    /// this set.
    ///
    /// *Panics:* `var` must be a valid variable in this set.
    pub fn mk_var(&self, var: BddVariable) -> Bdd {
        debug_assert!(var.0 < self.num_vars, "Invalid variable id.");
        Bdd::mk_var(self.num_vars, var)
    }

    /// Create a BDD corresponding to the $\neg v$ formula where `v` is a specific variable in
    /// this set.
    ///
    /// *Panics:* `var` must be a valid variable in this set.
    pub fn mk_not_var(&self, var: BddVariable) -> Bdd {
        debug_assert!(var.0 < self.num_vars, "Invalid variable id.");
        Bdd::mk_not_var(self.num_vars, var)
    }

    /// Create a BDD corresponding to the $v <=> \texttt{value}$ formula.
    ///
    /// *Panics:* `var` must be a valid variable in this set.
    pub fn mk_literal(&self, var: BddVariable, value: bool) -> Bdd {
        debug_assert!(var.0 < self.num_vars, "Invalid variable id.");
        Bdd::mk_literal(self.num_vars, var, value)
    }

    /// Create a BDD corresponding to the $v$ formula where `v` is a variable in this set.
    ///
    /// *Panics:* `var` must be a name of a valid variable in this set.
    pub fn mk_var_by_name(&self, var: &str) -> Bdd {
        self.var_by_name(var)
            .map(|var| self.mk_var(var))
            .unwrap_or_else(|| panic!("Variable {} is not known in this set.", var))
    }

    /// Create a BDD corresponding to the $\neg v$ formula where `v` is a variable in this set.
    ///
    /// *Panics:* `var` must be a name of a valid variable in this set.
    pub fn mk_not_var_by_name(&self, var: &str) -> Bdd {
        self.var_by_name(var)
            .map(|var| self.mk_not_var(var))
            .unwrap_or_else(|| panic!("Variable {} is not known in this set.", var))
    }

    /// Create a `Bdd` corresponding to the conjunction of literals in the given
    /// `BddPartialValuation`.
    ///
    /// For example, given a valuation `x = true`, `y = false` and `z = true`, create
    /// a `Bdd` for the formula `x & !y & z`. An empty valuation evaluates to `true`.
    ///
    /// *Panics:* All variables in the partial valuation must belong into this set.
    pub fn mk_conjunctive_clause(&self, clause: &BddPartialValuation) -> Bdd {
        let mut result = self.mk_true();
        // It is important to iterate in this direction, otherwise we are going to mess with
        // variable ordering.
        for (index, value) in clause.0.iter().enumerate().rev() {
            if let Some(value) = value {
                assert!(index < self.num_vars as usize);
                // This is safe because valuation cannot contain larger indices due to the way
                // it is constructed.
                debug_assert!(u16::try_from(index).is_ok());
                let variable = BddVariable(index as u16);

                let node = if *value {
                    // Value is true, so high link "continues", and low link goes to zero.
                    BddNode::mk_node(variable, BddPointer::zero(), result.root_pointer())
                } else {
                    // Value is false, so low link "continues", and high link goes to zero.
                    BddNode::mk_node(variable, result.root_pointer(), BddPointer::zero())
                };

                result.push_node(node);
            }
        }

        result
    }

    /// Create a `Bdd` corresponding to the disjunction of literals in the given
    /// `BddPartialValuation`.
    ///
    /// For example, given a valuation `x = true`, `y = false` and `z = true`, create
    /// a `Bdd` for the formula `x | !y | z`. An empty valuation evaluates to `false`.
    ///
    /// *Panics:* All variables in the valuation must belong into this set.
    pub fn mk_disjunctive_clause(&self, clause: &BddPartialValuation) -> Bdd {
        // See `mk_conjunctive_clause`, for details.
        if clause.is_empty() {
            return self.mk_false();
        }

        let mut result = self.mk_true();
        // Problem with this algorithm is that in the first iteration, we want to consider
        // zero as the root instead of one. So we use a variable which is pre-set in the
        // first iteration but will evaluate to real root in later iterations.
        let mut shadow_root = BddPointer::zero();
        for (index, value) in clause.0.iter().enumerate().rev() {
            if let Some(value) = value {
                assert!(index < self.num_vars as usize);
                debug_assert!(u16::try_from(index).is_ok());
                let variable = BddVariable(index as u16);

                let node = if *value {
                    BddNode::mk_node(variable, shadow_root, BddPointer::one())
                } else {
                    BddNode::mk_node(variable, BddPointer::one(), shadow_root)
                };

                result.push_node(node);
                shadow_root = result.root_pointer();
            }
        }

        result
    }

    /// Interpret each `BddPartialValuation` in `cnf` as a disjunctive clause, and produce
    /// a conjunction of such clauses. Effectively, this constructs a formula based on its
    /// conjunctive normal form.
    pub fn mk_cnf(&self, cnf: &[BddPartialValuation]) -> Bdd {
        Bdd::mk_cnf(self, cnf)
    }

    /// Interpret each `BddPartialValuation` in `dnf` as a conjunctive clause, and produce
    /// a disjunction of such clauses. Effectively, this constructs a formula based on its
    /// disjunctive normal form.
    pub fn mk_dnf(&self, dnf: &[BddPartialValuation]) -> Bdd {
        Bdd::mk_dnf(self.num_vars, dnf)
    }

    /// Build a BDD that is satisfied by all valuations where *up to* $k$ `variables` are `true`.
    ///
    /// Intuitively, this implements a "threshold function" $f(x) = (\sum_{i} x_i \leq k)$
    /// over the given `variables`.
    pub fn mk_sat_up_to_k(&self, k: usize, variables: &[BddVariable]) -> Bdd {
        // This is the same as sat_exactly_k, we just carry the k-1 result over to the next round.
        let mut valuation = BddPartialValuation::empty();
        for var in variables {
            valuation.set_value(*var, false);
        }
        let mut result = self.mk_conjunctive_clause(&valuation);
        for _i in 0..k {
            let mut result_plus_one = result.clone();
            for var in variables {
                let var_is_false = self.mk_not_var(*var);
                // result = result | flip(var, k_minus_one and var_is_false)
                let propagate = Bdd::fused_binary_flip_op(
                    (&result, None),
                    (&var_is_false, None),
                    Some(*var),
                    op_function::and,
                );
                result_plus_one = result_plus_one.or(&propagate);
            }

            result = result_plus_one
        }

        result
    }

    /// Build a BDD that is satisfied by all valuations where *exactly* $k$ `variables` are `true`.
    ///
    /// Intuitively, this implements an "equality function" $f(x) = (\sum_{i} x_i = k)$
    /// over the given `variables`.
    pub fn mk_sat_exactly_k(&self, k: usize, variables: &[BddVariable]) -> Bdd {
        // This is based on the recursion SAT_k = \cup_{v} SAT_{k-1}[flip v].
        let mut valuation = BddPartialValuation::empty();
        for var in variables {
            valuation.set_value(*var, false);
        }
        let mut result = self.mk_conjunctive_clause(&valuation);
        for _i in 0..k {
            let mut result_plus_one = self.mk_false();
            for var in variables {
                let var_is_false = self.mk_not_var(*var);
                // result = result | flip(var, k_minus_one and var_is_false)
                let propagate = Bdd::fused_binary_flip_op(
                    (&result, None),
                    (&var_is_false, None),
                    Some(*var),
                    op_function::and,
                );
                result_plus_one = result_plus_one.or(&propagate);
            }

            result = result_plus_one
        }

        result
    }

    /// This function takes a [Bdd] `bdd` together with its [BddVariableSet] `ctx` and attempts
    /// to translate this `bdd` using the variables of *this* [BddVariableSet].
    ///
    /// In other words, the source and the output [Bdd] are logically equivalent, but each is
    /// valid in its respective [BddVariableSet].
    ///
    /// ### Limitations
    ///
    /// Currently, this method is implemented through "unsafe" variable renaming. I.e. it will
    /// not actually modify the structure of the [Bdd] in any way. As such, the method can fail
    /// (return `None`) when:
    ///   - The `bdd` contains variables that are not present in this [BddVariableSet] (matching
    ///     is performed based on variable names and the support set of `bdd`).
    ///   - The variables used in `bdd` are ordered in a way that is not compatible with this
    ///     [BddVariableSet].
    ///
    pub fn transfer_from(&self, bdd: &Bdd, ctx: &BddVariableSet) -> Option<Bdd> {
        // It's easier to handle constants explicitly.
        if bdd.is_false() {
            return Some(self.mk_false());
        }

        if bdd.is_true() {
            return Some(self.mk_true());
        }

        // Sorted variable IDs that are used in the "old" context.
        let mut old_support_set = bdd.support_set().into_iter().collect::<Vec<_>>();
        old_support_set.sort();

        // Equivalent variable IDs in the "new" context.
        let mut new_support_set = Vec::new();
        for var in &old_support_set {
            let name = ctx.name_of(*var);
            let Some(id) = self.var_by_name(name.as_str()) else {
                // The variable does not exist in the new context.
                return None;
            };
            new_support_set.push(id);
        }

        // Test for ordering validity.
        for i in 1..new_support_set.len() {
            // If x[i] <= x[i-1], then the new vector is not sorted, meaning
            // the variables exist, but cannot be safely renamed in this order.
            if new_support_set[i] <= new_support_set[i - 1] {
                return None;
            }
        }

        // Make a translation map from old to new IDs.
        let map = old_support_set
            .into_iter()
            .zip(new_support_set)
            .collect::<HashMap<_, _>>();

        // Now go through all the non-terminal nodes and copy them to the new BDD
        // using the translated IDs. We don't have to change the links because we are not
        // changing the BDD structure.
        let mut new_bdd = Bdd::mk_true(self.num_vars);
        for node in bdd.nodes().skip(2) {
            let Some(new_var) = map.get(&node.var) else {
                unreachable!()
            };
            let new_node = BddNode::mk_node(*new_var, node.low_link, node.high_link);
            new_bdd.push_node(new_node);
        }

        Some(new_bdd)
    }
}

impl Display for BddVariableSet {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        if self.var_names.is_empty() {
            write!(f, "[]")?;
        } else {
            write!(f, "[{}", self.var_names[0])?;
            for i in 1..self.var_names.len() {
                write!(f, ",{}", self.var_names[i])?
            }
            write!(f, "]")?;
        }
        Ok(())
    }
}

impl FromIterator<String> for BddVariableSet {
    fn from_iter<T: IntoIterator<Item = String>>(iter: T) -> Self {
        let mut builder = BddVariableSetBuilder::new();
        for var_name in iter {
            builder.make_variable(var_name.as_str());
        }
        builder.build()
    }
}

impl From<Vec<String>> for BddVariableSet {
    fn from(value: Vec<String>) -> Self {
        BddVariableSet::from_iter(value)
    }
}

impl From<Vec<&str>> for BddVariableSet {
    fn from(value: Vec<&str>) -> Self {
        BddVariableSet::from_iter(value.iter().map(|it| it.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::_test_util::mk_5_variable_set;
    use super::*;
    use num_bigint::BigInt;

    #[test]
    fn bdd_universe_anonymous() {
        let universe = BddVariableSet::new_anonymous(5);
        assert_eq!(Some(BddVariable(0)), universe.var_by_name("x_0"));
        assert_eq!(Some(BddVariable(1)), universe.var_by_name("x_1"));
        assert_eq!(Some(BddVariable(2)), universe.var_by_name("x_2"));
        assert_eq!(Some(BddVariable(3)), universe.var_by_name("x_3"));
        assert_eq!(Some(BddVariable(4)), universe.var_by_name("x_4"));
    }

    #[test]
    fn bdd_universe_mk_const() {
        let variables = mk_5_variable_set();
        let tt = variables.mk_true();
        let ff = variables.mk_false();
        assert!(tt.is_true());
        assert!(ff.is_false());
        assert_eq!(Bdd::mk_true(5), tt);
        assert_eq!(Bdd::mk_false(5), ff);
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn bdd_universe_mk_var_invalid_id() {
        mk_5_variable_set().mk_var(BddVariable(6));
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn bdd_universe_mk_not_var_invalid_id() {
        mk_5_variable_set().mk_not_var(BddVariable(6));
    }

    #[test]
    #[should_panic]
    fn bdd_universe_mk_var_by_name_invalid_name() {
        mk_5_variable_set().mk_var_by_name("abc");
    }

    #[test]
    #[should_panic]
    fn bdd_universe_mk_not_var_by_name_invalid_name() {
        mk_5_variable_set().mk_not_var_by_name("abc");
    }

    #[test]
    fn bdd_mk_clause() {
        let universe = BddVariableSet::new_anonymous(5);
        let variables = universe.variables();

        let valuation = BddPartialValuation::from_values(&[
            (variables[0], true),
            (variables[2], false),
            (variables[4], true),
        ]);

        let con_expected = universe.eval_expression_string("x_0 & !x_2 & x_4");
        let dis_expected = universe.eval_expression_string("x_0 | !x_2 | x_4");

        assert_eq!(con_expected, universe.mk_conjunctive_clause(&valuation));
        assert_eq!(dis_expected, universe.mk_disjunctive_clause(&valuation));
    }

    #[test]
    fn bdd_mk_empty_clause() {
        let universe = BddVariableSet::new_anonymous(5);
        let empty = BddPartialValuation::empty();
        assert_eq!(universe.mk_true(), universe.mk_conjunctive_clause(&empty));
        assert_eq!(universe.mk_false(), universe.mk_disjunctive_clause(&empty));
    }

    #[test]
    #[should_panic]
    fn bdd_mk_conjunctive_clause_fails() {
        let universe = BddVariableSet::new_anonymous(5);
        let valuation = BddPartialValuation::from_values(&[(BddVariable(7), true)]);
        universe.mk_conjunctive_clause(&valuation);
    }

    #[test]
    #[should_panic]
    fn bdd_mk_disjunctive_clause_fails() {
        let universe = BddVariableSet::new_anonymous(5);
        let valuation = BddPartialValuation::from_values(&[(BddVariable(7), true)]);
        universe.mk_conjunctive_clause(&valuation);
    }

    #[test]
    fn bdd_mk_normal_form() {
        let universe = BddVariableSet::new_anonymous(5);
        let variables = universe.variables();

        let cnf_expected =
            universe.eval_expression_string("(x_0 | !x_4) & (x_1 | !x_3 | !x_0) & x_2");
        let dnf_expected =
            universe.eval_expression_string("(x_0 & !x_4) | (x_1 & !x_3 & !x_0) | x_2");
        // just a sanity check that the formulas are non-trivial
        assert!(!cnf_expected.is_true() && !cnf_expected.is_false());
        assert!(!dnf_expected.is_true() && !dnf_expected.is_false());

        let c1 = BddPartialValuation::from_values(&[(variables[0], true), (variables[4], false)]);
        let c2 = BddPartialValuation::from_values(&[
            (variables[1], true),
            (variables[3], false),
            (variables[0], false),
        ]);
        let c3 = BddPartialValuation::from_values(&[(variables[2], true)]);
        let formula = &[c1, c2, c3];
        assert_eq!(cnf_expected, universe.mk_cnf(formula));
        assert_eq!(dnf_expected, universe.mk_dnf(formula));

        assert_eq!(universe.mk_false(), universe.mk_dnf(&[]));
        assert_eq!(
            universe.mk_true(),
            universe.mk_dnf(&[BddPartialValuation::empty()])
        );
        assert_eq!(universe.mk_true(), universe.mk_cnf(&[]));
        assert_eq!(
            universe.mk_false(),
            universe.mk_cnf(&[BddPartialValuation::empty()])
        );

        // x | !x = true
        assert_eq!(
            universe.mk_true(),
            universe.mk_dnf(&[
                BddPartialValuation::from_values(&[(variables[0], true)]),
                BddPartialValuation::from_values(&[(variables[0], false)]),
            ])
        );

        // x & !x = false
        assert_eq!(
            universe.mk_false(),
            universe.mk_cnf(&[
                BddPartialValuation::from_values(&[(variables[0], true)]),
                BddPartialValuation::from_values(&[(variables[0], false)]),
            ])
        );

        // Test the backwards conversion by converting each formula to the inverse normal form.
        let cnf_as_dnf = universe.mk_cnf(formula).to_dnf();
        let dnf_as_cnf = universe.mk_dnf(formula).to_cnf();
        assert_eq!(cnf_expected, universe.mk_dnf(&cnf_as_dnf));
        assert_eq!(dnf_expected, universe.mk_cnf(&dnf_as_cnf));
    }

    #[test]
    fn bdd_mk_sat_k() {
        fn factorial(x: usize) -> usize {
            if x == 0 {
                1
            } else {
                x * factorial(x - 1)
            }
        }

        fn binomial(n: usize, k: usize) -> usize {
            factorial(n) / (factorial(k) * factorial(n - k))
        }

        let vars = BddVariableSet::new_anonymous(5);
        let variables = vars.variables();

        assert_eq!(
            vars.mk_sat_exactly_k(0, &variables).exact_cardinality(),
            BigInt::from(1)
        );
        assert_eq!(
            vars.mk_sat_exactly_k(1, &variables).exact_cardinality(),
            BigInt::from(variables.len())
        );

        let bdd = vars.mk_sat_exactly_k(3, &vars.variables());
        // The number of such valuations is exactly the binomial coefficient.
        assert_eq!(bdd.exact_cardinality(), BigInt::from(binomial(5, 3)));

        let bdd = vars.mk_sat_up_to_k(3, &vars.variables());
        let expected = binomial(5, 3) + binomial(5, 2) + binomial(5, 1) + binomial(5, 0);
        assert_eq!(bdd.exact_cardinality(), BigInt::from(expected));
    }

    #[test]
    fn bdd_transfer() {
        let ctx_1 = BddVariableSet::new(&["a", "b", "x", "c", "y"]);
        let ctx_2 = BddVariableSet::new(&["a", "x", "b", "z", "c"]);

        // Constants.
        assert_eq!(
            ctx_1.mk_false(),
            ctx_1.transfer_from(&ctx_2.mk_false(), &ctx_2).unwrap()
        );
        assert_eq!(
            ctx_1.mk_true(),
            ctx_1.transfer_from(&ctx_2.mk_true(), &ctx_2).unwrap()
        );

        // Valid translation.
        let f1 = ctx_1.eval_expression_string("a & b | !c");
        let f2 = ctx_2.eval_expression_string("a & b | !c");

        assert_eq!(f1, ctx_1.transfer_from(&f2, &ctx_2).unwrap());
        assert_eq!(f2, ctx_2.transfer_from(&f1, &ctx_1).unwrap());

        // Invalid translation: bad variable ordering.
        let f1 = ctx_1.eval_expression_string("a & !b & x | !c");
        assert_eq!(None, ctx_2.transfer_from(&f1, &ctx_1));

        // Invalid translation: missing variable.
        let f1 = ctx_1.eval_expression_string("a & y | !c");
        assert_eq!(None, ctx_2.transfer_from(&f1, &ctx_1));
    }

    #[test]
    fn bdd_variable_set_print() {
        let ctx = BddVariableSet::new(&["a", "b", "x", "c", "y"]);
        assert_eq!("[a,b,x,c,y]", ctx.to_string());
        let ctx = BddVariableSet::new(&[]);
        assert_eq!("[]", ctx.to_string());
    }
}
