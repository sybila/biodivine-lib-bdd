use crate::{Bdd, BddNode, BddPartialValuation, BddPointer, BddVariable};
use fxhash::FxBuildHasher;
use std::collections::HashMap;

impl Bdd {
    /// **(internal)** A specialized algorithm for constructing BDDs from CNFs. It builds the BDD
    /// directly by recursively "splitting" the clauses. The advantage is that we avoid a lot of
    /// memory copying. The disadvantage is that when the number of variables is high and the
    /// number of clauses low, this could be slightly slower due to all the recursion. However,
    /// it definitely needs to be tested at some point.
    pub(crate) fn mk_cnf(num_vars: u16, cnf: &[BddPartialValuation]) -> Bdd {
        // This is essentially a "dual" algorithm to the DNF implementation. Relevant explanation
        // can be found there.

        if cnf.is_empty() {
            return Bdd::mk_true(num_vars);
        }

        fn build_recursive(
            num_vars: u16,
            mut variable: u16,
            cnf: &[&BddPartialValuation],
            result: &mut Bdd,
            node_cache: &mut HashMap<BddNode, BddPointer, FxBuildHasher>,
        ) -> BddPointer {
            loop {
                if variable == num_vars {
                    return BddPointer::from_bool(cnf.is_empty());
                }
                if cnf.is_empty() {
                    return BddPointer::one();
                }

                let var = BddVariable(variable);
                let should_branch = cnf.iter().any(|val| val.get_value(var).is_some());
                if !should_branch {
                    variable += 1;
                    continue;
                }

                // Compared to DNF, here we want to *remove* any clause that has the specific
                // fixed value, because then the clause is satisfied. I.e. we want to retain
                // all clauses that are not satisfied by the recursive path so far.

                let mut var_true = Vec::new();
                let mut var_false = Vec::new();
                for clause in cnf {
                    match clause.get_value(var) {
                        Some(true) => var_false.push(*clause),
                        Some(false) => var_true.push(*clause),
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
        let mut node_cache = HashMap::with_capacity_and_hasher(cnf.len(), FxBuildHasher::default());
        node_cache.insert(BddNode::mk_zero(num_vars), BddPointer::zero());
        node_cache.insert(BddNode::mk_one(num_vars), BddPointer::one());

        let cnf = Vec::from_iter(cnf.iter());
        let result_pointer = build_recursive(num_vars, 0, &cnf, &mut result, &mut node_cache);
        if result_pointer.is_zero() {
            Bdd::mk_false(num_vars)
        } else {
            result
        }
    }

    /// Construct a CNF representation of this BDD.
    pub fn to_cnf(&self) -> Vec<BddPartialValuation> {
        // This is a "dual" of the DNF algorithm.
        // However, it also appears in this answer:
        //      https://stackoverflow.com/questions/19488478/convert-bdd-to-cnf

        fn build_recursive(
            bdd: &Bdd,
            path: &mut BddPartialValuation,
            node: BddPointer,
            results: &mut Vec<BddPartialValuation>,
        ) {
            if node.is_terminal() {
                // Compared to DNF, we want to include paths that terminate in the zero nodes.
                if node.is_zero() {
                    results.push(path.clone());
                }
                return;
            }

            let var = bdd.var_of(node);
            let low = bdd.low_link_of(node);
            let high = bdd.high_link_of(node);

            // Compared to DNF, we invert the values on the constructed path (i.e. low node
            // has a value fixed to true and vice versa).

            if !low.is_one() {
                path.set_value(var, true);
                build_recursive(bdd, path, low, results);
                path.unset_value(var);
            }

            if !high.is_one() {
                path.set_value(var, false);
                build_recursive(bdd, path, high, results);
                path.unset_value(var);
            }
        }

        let mut result = Vec::new();
        build_recursive(
            self,
            &mut BddPartialValuation::empty(),
            self.root_pointer(),
            &mut result,
        );
        result
    }
}
