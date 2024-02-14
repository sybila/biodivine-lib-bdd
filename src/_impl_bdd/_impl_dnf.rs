use crate::{Bdd, BddNode, BddPartialValuation, BddPointer, BddVariable};
use fxhash::FxBuildHasher;
use std::collections::HashMap;

impl Bdd {
    /// **(internal)** A specialized algorithm for constructing BDDs from DNFs. It builds the BDD
    /// directly by recursively "splitting" the clauses. The advantage is that we avoid a lot of
    /// memory copying. The disadvantage is that when the number of variables is high and the
    /// number of clauses low, this could be slightly slower due to all the recursion. However,
    /// it definitely needs to be tested at some point.
    pub(crate) fn mk_dnf(num_vars: u16, dnf: &[BddPartialValuation]) -> Bdd {
        if dnf.is_empty() {
            return Bdd::mk_false(num_vars);
        }

        // TODO:
        //  Can we turn the algorithm into a normal loop to prevent stack overflow in
        //  extreme cases?
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

                let var = BddVariable(variable);
                let should_branch = dnf.iter().any(|val| val.get_value(var).is_some());
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

        result
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
        self._to_optimized_dnf(&|| Ok::<(), ()>(())).unwrap()
    }

    /// A cancellable variant of [Bdd::to_optimized_dnf].
    pub fn _to_optimized_dnf<E, I: Fn() -> Result<(), E>>(
        &self,
        interrupt: &I,
    ) -> Result<Vec<BddPartialValuation>, E> {
        if self.is_false() {
            return Ok(Vec::new());
        }
        if self.is_true() {
            return Ok(vec![BddPartialValuation::empty()]);
        }

        fn _rec<E, I: Fn() -> Result<(), E>>(
            bdd: &Bdd,
            clause: &mut BddPartialValuation,
            results: &mut Vec<BddPartialValuation>,
            interrupt: &I,
        ) -> Result<(), E> {
            if bdd.is_false() {
                return Ok(());
            }

            if bdd.is_true() {
                results.push(clause.clone());
                return Ok(());
            }

            let mut support = Vec::from_iter(bdd.support_set());
            support.sort();

            assert!(!support.is_empty());

            let mut best = (support[0], usize::MAX);

            for var in support {
                interrupt()?;

                let bdd_t = bdd.var_restrict(var, true);
                let bdd_f = bdd.var_restrict(var, false);
                let size = bdd_t.size() + bdd_f.size();
                if size < best.1 {
                    best = (var, size);
                }
            }

            let (var, _) = best;

            clause[var] = Some(true);
            _rec(&bdd.var_restrict(var, true), clause, results, interrupt)?;
            clause[var] = Some(false);
            _rec(&bdd.var_restrict(var, false), clause, results, interrupt)?;
            clause[var] = None;

            Ok(())
        }

        let mut buffer = BddPartialValuation::empty();
        let mut results = Vec::new();
        _rec(self, &mut buffer, &mut results, interrupt)?;

        Ok(results)
    }
}
