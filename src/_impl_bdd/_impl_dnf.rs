use crate::{Bdd, BddPartialValuation, BddPointer, BddValuation, BddVariable};
use num_bigint::BigInt;

impl Bdd {
    /// **(internal)** A specialized algorithm for constructing BDDs from DNFs. It builds the BDD
    /// directly by recursively "splitting" the clauses. The advantage is that we avoid a lot of
    /// memory copying. The disadvantage is that when the number of variables is high and the
    /// number of clauses low, this could be slightly slower due to all the recursion. However,
    /// it definitely needs to be tested at some point.
    pub(crate) fn mk_dnf(num_vars: u16, dnf: &[&BddPartialValuation]) -> Bdd {
        fn _rec(mut var: u16, num_vars: u16, dnf: &[&BddPartialValuation]) -> Bdd {
            loop {
                if dnf.is_empty() {
                    return Bdd::mk_false(num_vars);
                }
                if var == num_vars || dnf.len() == 1 {
                    let c = dnf[0];
                    // At this point, all remaining clauses should just be duplicates.
                    for cx in &dnf[1..] {
                        assert_eq!(*cx, c);
                    }
                    return Bdd::mk_partial_valuation(num_vars, c);
                }

                // If we ever get to this point, the dnf should be always either empty,
                // or consists of a single clause.
                assert!(var < num_vars);

                let variable = BddVariable(var);
                let should_branch = dnf.iter().any(|val| val.has_value(variable));
                if !should_branch {
                    var += 1;
                    continue;
                }

                let mut dont_care = Vec::new();
                let mut has_true = Vec::new();
                let mut has_false = Vec::new();

                for c in dnf {
                    match c.get_value(BddVariable(var)) {
                        None => dont_care.push(*c),
                        Some(true) => has_true.push(*c),
                        Some(false) => has_false.push(*c),
                    }
                }

                let dont_care = _rec(var + 1, num_vars, &dont_care);
                let has_true = _rec(var + 1, num_vars, &has_true);
                let has_false = _rec(var + 1, num_vars, &has_false);

                return dont_care.or(&has_true).or(&has_false);
            }
        }

        _rec(0, num_vars, dnf)
        // TODO:
        //  This algorithm works fine with fully specified clauses, but it can "explode"
        //  with partial clauses because a clause can be used by both recursive paths.
        //  This means every node in the BDD is actually created as many times as it is
        //  visited (i.e. the complexity equates the number of paths in the BDD, which may
        //  be much larger than the size of the DNF).
        /*if dnf.is_empty() {
            return Bdd::mk_false(num_vars);
        }

        fn build_recursive(
            num_vars: u16,
            mut variable: u16,
            dnf: &[&BddPartialValuation],
            result: &mut Bdd,
            node_cache: &mut HashMap<BddNode, BddPointer, FxBuildHasher>,
        ) -> BddPointer {
            // The loop will automatically skip variables that are not relevant for the validity
            // of the provided DNF. This should significantly decrease the risk of stack overflow,
            // since we only run recursion when it is reasonably likely that we actually need to
            // condition on the specific variable. Otherwise, the variable is just skipped, since
            // we would get `low == high` anyway.
            loop {
                if variable == num_vars {
                    return BddPointer::from_bool(!dnf.is_empty());
                }
                if dnf.is_empty() {
                    return BddPointer::zero();
                }

                assert!(variable < num_vars);

                let var = BddVariable(variable);
                let should_branch = dnf.iter().any(|val| val.has_value(var));
                if !should_branch {
                    variable += 1;
                    continue;
                }

                let mut var_true = Vec::new();
                let mut var_false = Vec::new();
                for clause in dnf {
                    match clause.get_value(var) {
                        Some(true) => var_true.push(*clause),
                        Some(false) => var_false.push(*clause),
                        _ => {
                            var_true.push(*clause);
                            var_false.push(*clause);
                        }
                    }
                }

                let high = build_recursive(num_vars, variable + 1, &var_true, result, node_cache);
                let low = build_recursive(num_vars, variable + 1, &var_false, result, node_cache);

                if high == low {
                    return high;
                }

                let node = BddNode::mk_node(var, low, high);
                return if let Some(id) = node_cache.get(&node) {
                    *id
                } else {
                    result.push_node(node);
                    node_cache.insert(node, result.root_pointer());
                    result.root_pointer()
                };
            }
        }

        let mut result = Bdd::mk_true(num_vars);
        let mut node_cache = HashMap::with_capacity_and_hasher(dnf.len(), FxBuildHasher::default());
        node_cache.insert(BddNode::mk_zero(num_vars), BddPointer::zero());
        node_cache.insert(BddNode::mk_one(num_vars), BddPointer::one());

        let dnf = Vec::from_iter(dnf.iter());
        build_recursive(num_vars, 0, &dnf, &mut result, &mut node_cache);

        result*/
    }

    /// [BddValuation] version of [Bdd::mk_dnf]
    pub(crate) fn mk_dnf_valuation(num_vars: u16, dnf: &[&BddValuation]) -> Bdd {
        fn _rec(mut var: u16, num_vars: u16, dnf: &[&BddValuation]) -> Bdd {
            loop {
                if dnf.is_empty() {
                    return Bdd::mk_false(num_vars);
                }
                if var == num_vars || dnf.len() == 1 {
                    let c = dnf[0];
                    // At this point, all remaining clauses should just be duplicates.
                    for cx in &dnf[1..] {
                        assert_eq!(*cx, c);
                    }
                    return c.mk_bdd();
                }

                // If we ever get to this point, the dnf should be always either empty,
                // or consists of a single clause.
                assert!(var < num_vars);

                let variable = BddVariable(var);
                let should_branch = dnf.iter().any(|val| val.value(variable));
                if !should_branch {
                    var += 1;
                    continue;
                }

                let mut has_true = Vec::new();
                let mut has_false = Vec::new();

                for c in dnf {
                    match c.value(BddVariable(var)) {
                        true => has_true.push(*c),
                        false => has_false.push(*c),
                    }
                }

                let has_true = _rec(var + 1, num_vars, &has_true);
                let has_false = _rec(var + 1, num_vars, &has_false);

                return has_true.or(&has_false);
            }
        }
        _rec(0, num_vars, dnf)
    }

    /// Construct a DNF representation of this BDD. This is equivalent to collecting all results
    /// of the `Bdd::sat_clauses` iterator. However, it uses a different algorithm that should be
    /// slightly faster for enumerating all results at the same time (the `sat_clauses` iterator
    /// is optimized for visiting the results one-by-one).
    pub fn to_dnf(&self) -> Vec<BddPartialValuation> {
        let mut results: Vec<BddPartialValuation> = Vec::new();
        let mut path = BddPartialValuation::empty();

        let mut stack: Vec<(BddPointer, Option<bool>)> = vec![(self.root_pointer(), Some(true))];
        while let Some((node, go_low)) = stack.pop() {
            if node.is_zero() {
                // An unsatisfied clause.
                continue;
            }
            if node.is_one() {
                // A satisfied clause.
                results.push(path.clone());
                continue;
            }

            let node_var = self.var_of(node);

            if let Some(go_low) = go_low {
                if go_low {
                    // First, we go into the low child. But even before that,
                    // we add a new item that indicates we should go to the high child
                    // once the low child is done.
                    stack.push((node, Some(false)));

                    // Update `path` to indicate that we are in the low child.
                    path[node_var] = Some(false);
                    stack.push((self.low_link_of(node), Some(true)));
                } else {
                    // Here, we visit the high child. But we still have to retain the current
                    // node to remove it from the `path` once the subgraph is done.
                    stack.push((node, None));

                    path[node_var] = Some(true);
                    stack.push((self.high_link_of(node), Some(true)));
                }
            } else {
                // Finally, both children are processed. We can remove the variable
                // from the current path.
                path.unset_value(node_var);
            }
        }

        results
    }

    /// Similar to [Bdd::to_dnf], but uses a quadratic optimization algorithm to greedily
    /// minimize the number of clauses in the final normal form.
    ///
    /// For very large BDDs, this can require a lot of computation time. However, in such cases,
    /// [Bdd::to_dnf] is likely not going to yield good results either.
    ///
    /// Currently, there is no "iterator" variant of this algorithm that would generate the DNF
    /// on-the-fly. But it should be relatively straightforward, so if you need it, please get
    /// in touch.
    pub fn to_optimized_dnf(&self) -> Vec<BddPartialValuation> {
        self._to_optimized_dnf(&|_dnf| Ok::<(), ()>(())).unwrap()
    }

    /// The `interrupt` takes as an argument the computed DNF. This can be used to terminate
    /// early if the DNF is too large.
    pub fn _to_optimized_dnf<E, I: Fn(&[BddPartialValuation]) -> Result<(), E>>(
        &self,
        interrupt: &I,
    ) -> Result<Vec<BddPartialValuation>, E> {
        if self.is_false() {
            return Ok(Vec::new());
        }
        if self.is_true() {
            return Ok(vec![BddPartialValuation::empty()]);
        }

        fn _rec<E, I: Fn(&[BddPartialValuation]) -> Result<(), E>>(
            bdd: &Bdd,
            partial_clause: &mut BddPartialValuation,
            results: &mut Vec<BddPartialValuation>,
            interrupt: &I,
        ) -> Result<(), E> {
            if bdd.is_false() {
                return Ok(());
            }
            if bdd.is_true() {
                results.push(partial_clause.clone());
                return Ok(());
            }

            let mut support = Vec::from_iter(bdd.support_set());
            support.sort();
            assert!(!support.is_empty());

            // First, check if there is a variable that once eliminated leaves a "common core"
            // which does not depend on said variable. We can then first solve the "common core"
            // without considering that variable at all.

            // Find the largest common core.
            let zero = BigInt::from(0);
            let mut best_core = (support[0], zero.clone());
            for var in &support {
                interrupt(results)?;

                let core = bdd.var_for_all(*var);
                let core_cardinality = core.exact_cardinality();
                if core_cardinality > best_core.1 {
                    best_core = (*var, core_cardinality);
                }
            }

            // Solve the common core first.
            let bdd = if best_core.1 != zero {
                let best_core = bdd.var_for_all(best_core.0);
                _rec(&best_core, partial_clause, results, interrupt)?;
                let mut remaining = bdd.and_not(&best_core);

                // Remaining can be false only if the BDD does not depend on the core var
                // at all, which is not possible.
                assert!(!remaining.is_false());

                let mut core_support = Vec::from_iter(best_core.support_set());
                core_support.sort();

                // Remove variables that were used by the common core and the remaining
                // formula does not depend on them at all.
                for var in core_support {
                    let simplified = remaining.var_exists(var);
                    if &simplified.or(&best_core) == bdd {
                        remaining = simplified;
                    }
                }

                remaining
            } else {
                bdd.clone()
            };

            let mut best = (support[0], usize::MAX);

            for var in &support {
                interrupt(results)?;
                let bdd_t = bdd.var_restrict(*var, true);
                let bdd_f = bdd.var_restrict(*var, false);
                let size = bdd_t.size() + bdd_f.size();
                if size < best.1 {
                    best = (*var, size);
                }
            }

            let (var, _) = best;

            partial_clause[var] = Some(true);
            _rec(
                &bdd.var_restrict(var, true),
                partial_clause,
                results,
                interrupt,
            )?;
            partial_clause[var] = Some(false);
            _rec(
                &bdd.var_restrict(var, false),
                partial_clause,
                results,
                interrupt,
            )?;
            partial_clause[var] = None;

            Ok(())
        }

        let mut buffer = BddPartialValuation::empty();
        let mut results = Vec::new();
        _rec(self, &mut buffer, &mut results, interrupt)?;

        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    use crate::boolean_expression::BooleanExpression;
    use crate::{bdd, Bdd, BddPartialValuation, BddVariable, BddVariableSet};

    fn test_syntactic_monotonicity(var: BddVariable, dnf: &[BddPartialValuation]) -> Option<bool> {
        let mut has_positive = false;
        let mut has_negative = false;
        for c in dnf {
            if c[var] == Some(true) {
                has_positive = true;
            }
            if c[var] == Some(false) {
                has_negative = true;
            }
        }

        match (has_positive, has_negative) {
            (true, false) => Some(true),
            (false, true) => Some(false),
            (true, true) => None,
            (false, false) => unreachable!(),
        }
    }

    fn test_symbolic_monotonicity(
        ctx: &BddVariableSet,
        var: BddVariable,
        fn_is_true: &Bdd,
    ) -> Option<bool> {
        let input_is_true = ctx.mk_var(var);
        let input_is_false = ctx.mk_not_var(var);
        let fn_is_false = fn_is_true.not();
        let fn_x1_to_0 = bdd!(fn_is_false & input_is_true).var_exists(var);
        let fn_x0_to_1 = bdd!(fn_is_true & input_is_false).var_exists(var);
        let is_positive = bdd!(fn_x0_to_1 & fn_x1_to_0)
            .exists(&ctx.variables())
            .not()
            .is_true();

        let fn_x0_to_0 = bdd!(fn_is_false & input_is_false).var_exists(var);
        let fn_x1_to_1 = bdd!(fn_is_true & input_is_true).var_exists(var);
        let is_negative = bdd!(fn_x0_to_0 & fn_x1_to_1)
            .exists(&ctx.variables())
            .not()
            .is_true();

        match (is_positive, is_negative) {
            (true, false) => Some(true),
            (false, true) => Some(false),
            (true, true) => unreachable!(),
            (false, false) => None,
        }
    }

    #[test]
    pub fn comprehensive_dnf_test() {
        for file in std::fs::read_dir("res/test_expressions").unwrap() {
            let file = file.unwrap();
            let name = file.file_name().into_string().unwrap();
            if !name.ends_with(".bnet") {
                continue;
            }

            // These models fail to parse with stack overflow in debug mode,
            // but are ok in release.
            if name == "079.bnet"
                || name == "122.bnet"
                || name == "159.bnet"
                || name == "146.bnet"
                || name == "Skin3DFxd.bnet"
                || name == "Metabolism_demo.free-inputs.bnet"
                || name == "COVID_model.free-inputs.bnet"
                || name == "InVitro.free-inputs.bnet"
                || name == "InVivo.free-inputs.bnet"
            {
                continue;
            }

            println!("Testing {}", name);

            let mut total_monotonicity_tests = 0usize;
            let mut failed_monotonicity_tests = 0usize;

            let file_contents = std::fs::read_to_string(file.path()).unwrap();
            for line in file_contents.lines() {
                // Technically, this will also consider the targets,factors header as an expression,
                // but that's fine here.
                let line = line.trim();
                if line.is_empty() || line.starts_with('#') {
                    continue;
                }

                let expr_string = Vec::from_iter(line.split(","))[1].to_string();
                let expr = BooleanExpression::try_from(expr_string.as_str()).unwrap();
                let mut support = Vec::from_iter(expr.support_set());
                support.sort();
                let ctx = BddVariableSet::from(support);
                let expr_bdd = ctx.eval_expression(&expr);

                // Test that we can build the DNF and that it matches the original function.
                let dnf = expr_bdd.to_optimized_dnf();
                let mut reconstructed = ctx.mk_false();
                for c in &dnf {
                    reconstructed = reconstructed.or(&ctx.mk_conjunctive_clause(&c));
                }
                assert_eq!(reconstructed, expr_bdd);

                // Test that the DNF can be (mostly) used to detect monotonicity of functions.
                for var in expr_bdd.support_set() {
                    let syntactic = test_syntactic_monotonicity(var, &dnf);
                    let semantic = test_symbolic_monotonicity(&ctx, var, &expr_bdd);
                    if semantic.is_some() {
                        total_monotonicity_tests += 1;
                    }
                    if syntactic != semantic {
                        failed_monotonicity_tests += 1;
                    }
                }
            }
            println!(
                "{} / {}",
                failed_monotonicity_tests, total_monotonicity_tests
            );
        }
    }

    #[test]
    pub fn bad_mk_dnf() {
        let ctx = BddVariableSet::new_anonymous(60);
        let variables = ctx.variables();
        let mut clauses = Vec::new();
        for i in 0..30 {
            let mut c = BddPartialValuation::empty();
            c[variables[2 * i]] = Some(true);
            c[variables[2 * i + 1]] = Some(true);
            clauses.push(c);
        }

        assert_eq!(ctx.mk_dnf(&clauses).size(), 62);
    }

    #[test]
    pub fn bad_mk_dnf_2() {
        // Extracted from AEON.py test.
        let ctx = BddVariableSet::new_anonymous(3);
        let a_true = (BddVariable::from_index(0), true);
        let b_false = (BddVariable::from_index(1), false);
        let clauses = vec![
            BddPartialValuation::from_values(&[a_true, b_false]),
            BddPartialValuation::from_values(&[a_true, b_false]),
        ];

        assert_eq!(ctx.mk_dnf(&clauses).size(), 4);
    }
}
