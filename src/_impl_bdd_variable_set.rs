use super::*;

impl BddVariableSet {
    /// Create a new `BddVariableSet` with anonymous variables $(x_1, \ldots, x_n)$ where $n$ is
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
}
