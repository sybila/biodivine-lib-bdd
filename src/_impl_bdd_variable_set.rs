use super::*;

impl AsRef<BddVariableSet2<String>> for BddVariableSet {
    fn as_ref(&self) -> &BddVariableSet2<String> {
        &self.inner
    }
}

impl BddVariableSet {
    /// Create a new `BddVariableSet` with anonymous variables $(x_0, \ldots, x_n)$ where $n$ is
    /// the `num_vars` parameter.
    pub fn new_anonymous(num_vars: u16) -> BddVariableSet {
        BddVariableSet {
            inner: BddVariableSet2::<String>::new_anonymous(num_vars),
        }
    }

    /// Create a new `BddVariableSet` with the given named variables. Same as using the
    /// `BddVariablesBuilder` with this name vector, but no `BddVariable` objects are returned.
    ///
    /// *Panics:* `vars` must contain unique names which are allowed as variable names.
    pub fn new(vars: &[&str]) -> BddVariableSet {
        BddVariableSet {
            inner: BddVariableSet2::<String>::new(
                &vars.iter().map(|it| it.to_string()).collect::<Vec<_>>(),
            ),
        }
    }

    /// Return the number of variables in this set.
    pub fn num_vars(&self) -> u16 {
        self.inner.num_vars()
    }

    /// Create a `BddVariable` based on a variable name. If the name does not appear
    /// in this set, return `None`.
    pub fn var_by_name(&self, name: &str) -> Option<BddVariable> {
        self.inner.find_variable(&name.to_string())
    }

    /// Provides a vector of all `BddVariable`s in this set.
    pub fn variables(&self) -> Vec<BddVariable> {
        self.inner.variables()
    }

    /// Obtain the name of a specific `BddVariable`.
    pub fn name_of(&self, variable: BddVariable) -> String {
        self.inner.get_variable(variable).clone()
    }

    /// Create a `Bdd` corresponding to the `true` formula.
    pub fn mk_true(&self) -> Bdd {
        self.inner.mk_true()
    }

    /// Create a `Bdd` corresponding to the `false` formula.
    pub fn mk_false(&self) -> Bdd {
        self.inner.mk_false()
    }

    /// Create a `Bdd` corresponding to the $v$ formula where `v` is a specific variable in
    /// this set.
    ///
    /// *Panics:* `var` must be a valid variable in this set.
    pub fn mk_var(&self, var: BddVariable) -> Bdd {
        self.inner.mk_var(var)
    }

    /// Create a BDD corresponding to the $\neg v$ formula where `v` is a specific variable in
    /// this set.
    ///
    /// *Panics:* `var` must be a valid variable in this set.
    pub fn mk_not_var(&self, var: BddVariable) -> Bdd {
        self.inner.mk_not_var(var)
    }

    /// Create a BDD corresponding to the $v <=> \texttt{value}$ formula.
    ///
    /// *Panics:* `var` must be a valid variable in this set.
    pub fn mk_literal(&self, var: BddVariable, value: bool) -> Bdd {
        self.inner.mk_literal(var, value)
    }

    /// Create a BDD corresponding to the $v$ formula where `v` is a variable in this set.
    ///
    /// *Panics:* `var` must be a name of a valid variable in this set.
    pub fn mk_var_by_name(&self, var: &str) -> Bdd {
        self.inner.mk_var_by_ref(&var.to_string())
    }

    /// Create a BDD corresponding to the $\neg v$ formula where `v` is a variable in this set.
    ///
    /// *Panics:* `var` must be a name of a valid variable in this set.
    pub fn mk_not_var_by_name(&self, var: &str) -> Bdd {
        self.inner.mk_not_var_by_ref(&var.to_string())
    }

    /// Create a `Bdd` corresponding to the conjunction of literals in the given
    /// `BddPartialValuation`.
    ///
    /// For example, given a valuation `x = true`, `y = false` and `z = true`, create
    /// a `Bdd` for the formula `x & !y & z`. An empty valuation evaluates to `true`.
    ///
    /// *Panics:* All variables in the partial valuation must belong into this set.
    pub fn mk_conjunctive_clause(&self, clause: &BddPartialValuation) -> Bdd {
        self.inner.mk_conjunctive_clause(clause)
    }

    /// Create a `Bdd` corresponding to the disjunction of literals in the given
    /// `BddPartialValuation`.
    ///
    /// For example, given a valuation `x = true`, `y = false` and `z = true`, create
    /// a `Bdd` for the formula `x | !y | z`. An empty valuation evaluates to `false`.
    ///
    /// *Panics:* All variables in the valuation must belong into this set.
    pub fn mk_disjunctive_clause(&self, clause: &BddPartialValuation) -> Bdd {
        self.inner.mk_disjunctive_clause(clause)
    }

    /// Interpret each `BddPartialValuation` in `cnf` as a disjunctive clause, and produce
    /// a conjunction of such clauses. Effectively, this constructs a formula based on its
    /// conjunctive normal form.
    pub fn mk_cnf(&self, cnf: &[BddPartialValuation]) -> Bdd {
        self.inner.mk_cnf(cnf)
    }

    /// Interpret each `BddPartialValuation` in `dnf` as a conjunctive clause, and produce
    /// a disjunction of such clauses. Effectively, this constructs a formula based on its
    /// disjunctive normal form.
    pub fn mk_dnf(&self, dnf: &[BddPartialValuation]) -> Bdd {
        self.inner.mk_dnf(dnf)
    }

    /// Build a BDD that is satisfied by all valuations where *up to* $k$ `variables` are `true`.
    ///
    /// Intuitively, this implements a "threshold function" $f(x) = (\sum_{i} x_i \leq k)$
    /// over the given `variables`.
    pub fn mk_sat_up_to_k(&self, k: usize, variables: &[BddVariable]) -> Bdd {
        self.inner.mk_sat_up_to_k(k, variables)
    }

    /// Build a BDD that is satisfied by all valuations where *exactly* $k$ `variables` are `true`.
    ///
    /// Intuitively, this implements an "equality function" $f(x) = (\sum_{i} x_i = k)$
    /// over the given `variables`.
    pub fn mk_sat_exactly_k(&self, k: usize, variables: &[BddVariable]) -> Bdd {
        self.inner.mk_sat_exactly_k(k, variables)
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
        self.inner.transfer_from(bdd, &ctx.inner)
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
}
