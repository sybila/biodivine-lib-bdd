use super::*;
use std::convert::TryFrom;

impl BddVariableSet {
    /// Create a new `BddVariableSet` with anonymous variables $(x_0, \ldots, x_n)$ where $n$ is
    /// the `num_vars` parameter.
    pub fn new_anonymous(num_vars: u16) -> BddVariableSet {
        if num_vars >= (std::u16::MAX - 1) {
            panic!(
                "Too many BDD variables. There can be at most {} variables.",
                std::u16::MAX - 1
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
    pub fn new(vars: Vec<&str>) -> BddVariableSet {
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
        if cfg!(feature = "shields_up") && var.0 >= self.num_vars {
            panic!("Variable {:?} is not in this set.", var);
        }
        Bdd::mk_var(self.num_vars, var)
    }

    /// Create a BDD corresponding to the $\neg v$ formula where `v` is a specific variable in
    /// this set.
    ///
    /// *Panics:* `var` must be a valid variable in this set.
    pub fn mk_not_var(&self, var: BddVariable) -> Bdd {
        if cfg!(feature = "shields_up") && var.0 >= self.num_vars {
            panic!("Variable {:?} is not in this set.", var);
        }
        Bdd::mk_not_var(self.num_vars, var)
    }

    /// Create a BDD corresponding to the $v <=> \texttt{value}$ formula.
    ///
    /// *Panics:* `var` must be a valid variable in this set.
    pub fn mk_literal(&self, var: BddVariable, value: bool) -> Bdd {
        if cfg!(feature = "shields_up") && var.0 >= self.num_vars {
            panic!("Variable {:?} is not in this set.", var);
        }
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
    pub fn mk_conjunctive_clause(&self, valuation: &BddPartialValuation) -> Bdd {
        let mut result = self.mk_true();
        // It is important to iterate in this direction, otherwise we are going to mess with
        // variable ordering.
        for (index, value) in valuation.0.iter().enumerate().rev() {
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
    pub fn mk_disjunctive_clause(&self, valuation: &BddPartialValuation) -> Bdd {
        // See `mk_conjunctive_clause`, for details.
        if valuation.is_empty() {
            return self.mk_false();
        }

        let mut result = self.mk_true();
        // Problem with this algorithm is that in the first iteration, we want to consider
        // zero as the root instead of one. So we use a variable which is pre-set in the
        // first iteration but will evaluate to real root in later iterations.
        let mut shadow_root = BddPointer::zero();
        for (index, value) in valuation.0.iter().enumerate().rev() {
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
        cnf.iter()
            .map(|it| self.mk_disjunctive_clause(it))
            .fold(self.mk_true(), |a, b| a.and(&b))
    }

    /// Interpret each `BddPartialValuation` in `dnf` as a conjunctive clause, and produce
    /// a disjunction of such clauses. Effectively, this constructs a formula based on its
    /// disjunctive normal form.
    pub fn mk_dnf(&self, dnf: &[BddPartialValuation]) -> Bdd {
        dnf.iter()
            .map(|it| self.mk_conjunctive_clause(it))
            .fold(self.mk_false(), |a, b| a.or(&b))
    }
}

#[cfg(test)]
mod tests {
    use super::_test_util::mk_5_variable_set;
    use super::*;

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
    fn bdd_universe_mk_var_invalid_id() {
        mk_5_variable_set().mk_var(BddVariable(6));
    }

    #[test]
    #[should_panic]
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
    }
}
