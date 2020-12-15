use crate::{Bdd, BddNode, BddPointer, BddVariable};

/// Advanced relation-like operations for `Bdd`s.
impl Bdd {
    /// Eliminates one given variable from the `Bdd`.
    ///
    /// If we see the Bdd as a set of bitvectors, this is essentially existential quantification:
    /// $\exists x_i : (x_1, ..., x_i, ..., x_n) \in BDD$.
    pub fn var_project(&self, variable: BddVariable) -> Bdd {
        Bdd::fused_binary_flip_op(
            (self, None),
            (self, Some(variable)),
            None,
            crate::op_function::or,
        )
    }

    /// Eliminate all given variables from the `Bdd`. This is a generalized variant
    /// of `var_projection`.
    ///
    /// This can be used to implement operations like `domain` and `range` of
    /// a certain relation.
    pub fn project(&self, variables: &[BddVariable]) -> Bdd {
        // Starting from the last Bdd variables is more efficient, we therefore enforce it.
        // (variables vector is always very small anyway)
        sorted(variables)
            .into_iter()
            .rev()
            .fold(self.clone(), |result, v| result.var_project(v))
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
                let picked = r_pick(&set.var_project(*last_var), rest);
                picked.and(&set.var_pick(*last_var))
            } else {
                set.clone()
            }
        }

        r_pick(self, &sorted(variables))
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
        let mut partial_valuation = variables.to_vec();
        partial_valuation.sort_by_key(|(v, _)| *v);
        let mut valuation_bdd = Bdd::mk_true(self.num_vars());
        for (var, value) in partial_valuation.into_iter().rev() {
            let node = if value {
                BddNode::mk_node(var, BddPointer::zero(), valuation_bdd.root_pointer())
            } else {
                BddNode::mk_node(var, valuation_bdd.root_pointer(), BddPointer::zero())
            };
            valuation_bdd.push_node(node);
        }
        self.and(&valuation_bdd)
    }
}

/// **(internal)** Helper function for sorting variable list arguments.
fn sorted(variables: &[BddVariable]) -> Vec<BddVariable> {
    let mut variables: Vec<BddVariable> = variables.to_vec();
    variables.sort();
    variables
}
