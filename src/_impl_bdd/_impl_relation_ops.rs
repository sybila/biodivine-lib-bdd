use crate::{Bdd, BddPartialValuation, BddVariable};
use rand::Rng;

/// Advanced relation-like operations for `Bdd`s.
impl Bdd {
    /// This operation is deprecated in favour of `Bdd::var_exists` which provides the
    /// same functionality but better naming.
    #[deprecated]
    pub fn var_project(&self, variable: BddVariable) -> Bdd {
        self.var_exists(variable)
    }

    /// Eliminates one given variable from the `Bdd` using **existential projection**.
    ///
    /// If we see the Bdd as a set of bitvectors, this is essentially existential quantification:
    /// $\exists x_i : (x_1, ..., x_i, ..., x_n) \in BDD$.
    pub fn var_exists(&self, variable: BddVariable) -> Bdd {
        Bdd::fused_binary_flip_op(
            (self, None),
            (self, Some(variable)),
            None,
            crate::op_function::or,
        )
    }

    /// Eliminates one given variable from the `Bdd` using **universal projection**.
    ///
    /// If we see the Bdd as a set of bitvectors, this is essentially universal quantification:
    /// $\forall x_i : (x_1, ..., x_i, ..., x_n) \in BDD$.
    pub fn var_for_all(&self, variable: BddVariable) -> Bdd {
        Bdd::fused_binary_flip_op(
            (self, None),
            (self, Some(variable)),
            None,
            crate::op_function::and,
        )
    }

    /// This method is deprecated in favour of `Bdd::exists` which provides the same functionality
    /// but better naming.
    #[deprecated]
    pub fn project(&self, variables: &[BddVariable]) -> Bdd {
        self.exists(variables)
    }

    /// Eliminate all given `variables` from the `Bdd` using existential projection.
    ///
    /// This can be used to implement operations like `domain` and `range` for
    /// a specific relation.
    ///
    /// Note that this method should be faster than repeated calls to `var_exists` once
    /// the size of `variables` is non-trivial, but it has a higher overhead. So for very small
    /// instances the performance advantage may not be very high.
    pub fn exists(&self, variables: &[BddVariable]) -> Bdd {
        // x & x is simply identity
        Bdd::binary_op_with_exists(self, self, crate::op_function::and, variables)
    }

    /// Eliminate all given `variables` from the `Bdd` using universal projection.
    ///
    /// Same performance characteristics as `Bdd::exists`.
    pub fn for_all(&self, variables: &[BddVariable]) -> Bdd {
        Bdd::binary_op_with_for_all(self, self, crate::op_function::and, variables)
    }

    /// Picks one valuation for the given `BddVariable`.
    ///
    /// Essentially, what this means is that
    /// $(x_1, ..., x_i, ..., x_n) \in B \Leftrightarrow (x_1, ..., \neg x_i, ..., x_n) \not\in B$.
    /// That is, each valuation (without $x_i$) can be present only with either $x_i = 1$ or
    /// $x_i = 0$, but not both.
    ///
    /// WARNING! `var_pick` is a bit troublesome in terms of composition: `B.var_pick(x).var_pick(y)`
    /// is probably not what you think. So make sure to prove and test thoroughly.
    pub fn var_pick(&self, variable: BddVariable) -> Bdd {
        // original \ flip(original & !x_i)
        Bdd::fused_binary_flip_op(
            (self, None),
            (&self.var_select(variable, false), Some(variable)),
            None,
            crate::op_function::and_not,
        )
    }

    /// Same as `bdd.var_pick`, but the *preferred* value is picked randomly using
    /// the provided generator, instead of defaulting to `false`.
    ///
    /// Note that this is not the same as having a random value picked on each path in the `Bdd`.
    /// Instead, there is one "global" value that is preferred on every path.
    pub fn var_pick_random<R: Rng>(&self, variable: BddVariable, rng: &mut R) -> Bdd {
        let preferred = self.var_select(variable, rng.gen_bool(0.5));
        Bdd::fused_binary_flip_op(
            (self, None),
            (&preferred, Some(variable)),
            None,
            crate::op_function::and_not,
        )
    }

    /// Picks one "witness" valuation for the given variables. This is a generalized variant
    /// of `var_pick`.
    ///
    /// After this operation, if we view `Bdd` as a set of bitvectors, every partial valuation in
    /// the original `Bdd`, disregarding the given `variables`, has exactly one witness valuation
    /// in the result, which was also in the original `Bdd`.
    ///
    /// This can be used to implement non-trivial element picking on relations (for example,
    /// for $A \times B$, picking one $b \in B$ for every $a \in A$).
    pub fn pick(&self, variables: &[BddVariable]) -> Bdd {
        fn r_pick(set: &Bdd, variables: &[BddVariable]) -> Bdd {
            if let Some((last_var, rest)) = variables.split_last() {
                let picked = r_pick(&set.var_exists(*last_var), rest);
                picked.and(&set.var_pick(*last_var))
            } else {
                set.clone()
            }
        }

        r_pick(self, &sorted(variables))
    }

    /// Same as `bdd.pick`, but the preferred value for each variable is picked randomly using
    /// the provided generator.
    pub fn pick_random<R: Rng>(&self, variables: &[BddVariable], rng: &mut R) -> Bdd {
        fn r_pick<R: Rng>(set: &Bdd, variables: &[BddVariable], rng: &mut R) -> Bdd {
            if let Some((last_var, rest)) = variables.split_last() {
                let picked = r_pick(&set.var_exists(*last_var), rest, rng);
                picked.and(&set.var_pick_random(*last_var, rng))
            } else {
                set.clone()
            }
        }

        r_pick(self, &sorted(variables), rng)
    }

    /// Fix the value of a specific `BddVariable` to the given `value`. This is just a shorthand
    /// for $B \land (x \Leftrightarrow \texttt{value})$.
    pub fn var_select(&self, variable: BddVariable, value: bool) -> Bdd {
        self.and(&Bdd::mk_literal(self.num_vars(), variable, value))
    }

    /// Generalized operation to `var_select`, allows effectively fixing multiple variables to
    /// the given values. Similar to `BddValuation.into::<Bdd>()`, but here you don't have to
    /// specify all variables.
    pub fn select(&self, variables: &[(BddVariable, bool)]) -> Bdd {
        let valuation = BddPartialValuation::from_values(variables);
        let valuation_bdd = Bdd::mk_partial_valuation(self.num_vars(), &valuation);
        self.and(&valuation_bdd)
    }

    /// Fixes a `variable` to the given `value`, and then eliminates said variable using
    /// existential projection.
    ///
    /// A valuation `v` satisfies the resulting formula `B_2` if and only if `v[variable = value]`
    /// satisfied the original formula `B_1`.
    pub fn var_restrict(&self, variable: BddVariable, value: bool) -> Bdd {
        let value_literal = Bdd::mk_literal(self.num_vars(), variable, value);
        // TODO:
        //  We should test if this is actually faster than running self.var_select().exists().
        Bdd::binary_op_with_exists(self, &value_literal, crate::op_function::and, &[variable])
    }

    /// Generalized operation to `var_restrict`. Allows fixing multiple Bdd variables and
    /// eliminating them at the same time.
    pub fn restrict(&self, variables: &[(BddVariable, bool)]) -> Bdd {
        let valuation = BddPartialValuation::from_values(variables);
        let valuation_bdd = Bdd::mk_partial_valuation(self.num_vars(), &valuation);
        let variables: Vec<BddVariable> = Vec::from_iter(variables.iter().map(|(x, _)| *x));
        Bdd::binary_op_with_exists(self, &valuation_bdd, crate::op_function::and, &variables)
    }
}

/// **(internal)** Helper function for sorting variable list arguments.
fn sorted(variables: &[BddVariable]) -> Vec<BddVariable> {
    let mut variables: Vec<BddVariable> = variables.to_vec();
    variables.sort();
    variables
}
