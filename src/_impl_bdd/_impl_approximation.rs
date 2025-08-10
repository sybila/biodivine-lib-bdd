use crate::{Bdd, BddPointer, BddVariable};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashSet};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
struct BfsPointer(BddPointer, BddVariable);

impl PartialOrd for BfsPointer {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BfsPointer {
    fn cmp(&self, other: &Self) -> Ordering {
        self.1.cmp(&other.1).reverse()
    }
}

impl Bdd {
    /// For each node in this BDD, compute the number of satisfying valuations that
    /// "visit" said node, i.e. when evaluating said valuation, we visit this node.
    ///
    /// The result is a vector of [`BigUint`] weights indexed by [`BddPointer`]
    /// values converted to `usize` indices. Note that for root, and for terminal node `1`,
    /// the value is always equal to [`Bdd::exact_cardinality`], and for terminal node `0`,
    /// the value is always also `0`.
    pub fn node_valuation_weights(&self) -> Vec<BigUint> {
        let mut expanded: Vec<bool> = vec![false; self.0.len()];
        let mut incoming_vals: Vec<BigUint> = vec![BigUint::zero(); self.0.len()];
        let mut outgoing_vals: Vec<Option<BigUint>> = vec![None; self.0.len()];
        let root = self.root_pointer();
        let root_var = self.var_of(root);

        outgoing_vals[0] = Some(BigUint::zero());
        outgoing_vals[1] = Some(BigUint::one());

        expanded[0] = true;
        expanded[1] = true;

        incoming_vals[root.to_index()] = BigUint::one();

        // First, compute `outgoing_vals` using DFS. This is the same as cardinality computation.
        let mut stack: Vec<BddPointer> = vec![root];
        while let Some(node) = stack.pop() {
            if outgoing_vals[node.to_index()].is_some() {
                // This node already has outgoing paths computed. Incoming paths can still
                // increase, but that is not computed here.
                continue;
            } else {
                let var = self.var_of(node);
                let low = self.low_link_of(node);
                let high = self.high_link_of(node);

                let low_var = self.var_of(low);
                let high_var = self.var_of(high);

                let low_multiplier = BigUint::one() << ((low_var.to_index() - var.to_index()) - 1);
                let high_multiplier =
                    BigUint::one() << ((high_var.to_index() - var.to_index()) - 1);

                // Now, if both low and high have outgoing paths computed, we can use them
                // to compute outgoing paths for this node as well:
                match (
                    &outgoing_vals[low.to_index()],
                    &outgoing_vals[high.to_index()],
                ) {
                    (Some(low_val), Some(high_val)) => {
                        let outgoing = low_val * &low_multiplier + high_val * &high_multiplier;
                        outgoing_vals[node.to_index()] = Some(outgoing);
                    }
                    (Some(_), None) => {
                        stack.push(node);
                        stack.push(high);
                    }
                    (None, Some(_)) => {
                        stack.push(node);
                        stack.push(low);
                    }
                    (None, None) => {
                        stack.push(node);
                        stack.push(low);
                        stack.push(high);
                    }
                }
            }
        }

        // Second, compute `incoming_vals` using BFS.
        let mut queue: BinaryHeap<BfsPointer> = BinaryHeap::from([BfsPointer(root, root_var)]);
        while let Some(BfsPointer(node, var)) = queue.pop() {
            if !expanded[node.to_index()] {
                // If this is the first time we are expanding the node, we must
                // propagate its incoming paths to its children. (we might expand a node
                // more than one time, because it can be discovered from multiple parents)
                expanded[node.to_index()] = true;

                let low = self.low_link_of(node);
                let high = self.high_link_of(node);

                let low_var = self.var_of(low);
                let high_var = self.var_of(high);

                let low_multiplier = BigUint::one() << ((low_var.to_index() - var.to_index()) - 1);
                let high_multiplier =
                    BigUint::one() << ((high_var.to_index() - var.to_index()) - 1);

                let node_incoming = incoming_vals[node.to_index()].clone();

                incoming_vals[low.to_index()] += &node_incoming * &low_multiplier;
                incoming_vals[high.to_index()] += &node_incoming * &high_multiplier;

                queue.push(BfsPointer(low, low_var));
                queue.push(BfsPointer(high, high_var));
            }
        }

        // All nodes must be expanded, and all outgoing valuation counts are computed.
        debug_assert!(expanded.iter().all(|&b| b));
        debug_assert!(outgoing_vals.iter().all(|x| x.is_some()));
        let outgoing_vals: Vec<BigUint> =
            Vec::from_iter(outgoing_vals.into_iter().map(|it| it.unwrap()));

        // The number of outgoing valuations from the root must be the same as the number
        // incoming to one.
        debug_assert_eq!(&incoming_vals[1], &outgoing_vals[root.to_index()]);

        let root_multiplier = BigUint::one() << root_var.to_index();
        self.pointers()
            .map(|it| {
                &incoming_vals[it.to_index()] * &outgoing_vals[it.to_index()] * &root_multiplier
            })
            .collect::<Vec<_>>()
    }

    /**
    Compute a new BDD `over` which overapproximates `self` BDD by re-routing the `to_eliminate`
    nodes to `1` and removing all nodes that become unreachable due to this operation.

    The BDD `over` is guaranteed to be smaller than `self` in terms of node count.
    */
    pub fn overapproximate(&self, to_eliminate: &[BddPointer]) -> Bdd {
        let to_eliminate: HashSet<BddPointer> = HashSet::from_iter(to_eliminate.iter().cloned());
        if to_eliminate.contains(&self.root_pointer()) {
            // If we are trying to eliminate the root, the result is the true BDD.
            return Bdd::mk_true(self.num_vars());
        }

        let mut copy = self.clone();
        for node in copy.pointers() {
            let low = self.low_link_of(node);
            let high = self.high_link_of(node);
            if to_eliminate.contains(&low) {
                copy.0[node.to_index()].low_link = BddPointer::one();
            }
            if to_eliminate.contains(&high) {
                copy.0[node.to_index()].high_link = BddPointer::one();
            }
        }

        // At this point, `copy` can be in non-reduced state and has unreachable nodes.
        // A simple logical identity should produce a canonical BDD again:
        copy.and(&copy)
    }

    /**
    Compute a new BDD `under` which underapproximates `self` BDD by re-routing the `to_eliminate`
    nodes to `0` and removing all nodes that become unreachable due to this operation.

    The BDD `under` is guaranteed to be smaller than `self` in terms of node count.
    */
    pub fn underapproximate(&self, to_eliminate: &[BddPointer]) -> Bdd {
        let to_eliminate: HashSet<BddPointer> = HashSet::from_iter(to_eliminate.iter().cloned());
        if to_eliminate.contains(&self.root_pointer()) {
            // If we are trying to eliminate the root, the result is the false BDD.
            return Bdd::mk_false(self.num_vars());
        }

        let mut copy = self.clone();
        for node in copy.pointers() {
            let low = self.low_link_of(node);
            let high = self.high_link_of(node);
            if to_eliminate.contains(&low) {
                copy.0[node.to_index()].low_link = BddPointer::zero();
            }
            if to_eliminate.contains(&high) {
                copy.0[node.to_index()].high_link = BddPointer::zero();
            }
        }

        // At this point, `copy` can be in non-reduced state and has unreachable nodes.
        // A simple logical identity should produce a canonical BDD again:
        copy.and(&copy)
    }

    /**
    Compute a new [`Bdd`] `over` for which it holds that `over.size() <= target_size` and it
    holds that `self.implies(over)` (i.e. each valuation that satisfies `self` also
    satisfies `over`). Consequently, it holds that `over.cardinality() >= self.cardinality()`.

    The algorithm works by greedily re-routing BDD nodes to `1` which have the least amount
    of paths going through them, until the target size is achieved.
    */
    pub fn overapproximate_to_size(&self, target_size: usize) -> Bdd {
        let negation = self.not();
        let under_negation = negation.underapproximate_to_size(target_size);
        under_negation.not()
    }

    /**
    Compute a new [`Bdd`] `under` for which it holds that `under.size() <= target_size` and it
    holds that `under.implies(self)` (i.e. each valuation that satisfies `under` also
    satisfies `self`). Consequently, it holds that `under.cardinality() <= self.cardinality()`.

    The algorithm works by greedily re-routing BDD nodes to `0` which have the least amount
    of paths going through them, until the target size is achieved.
    */
    pub fn underapproximate_to_size(&self, target_size: usize) -> Bdd {
        if target_size >= self.size() {
            return self.clone();
        }

        // Compute the number of valuations going through each node and sort them.
        let mut weights = self
            .node_valuation_weights()
            .into_iter()
            .zip(self.pointers())
            .collect::<Vec<_>>();
        weights.sort_by(|(x, px), (y, py)| {
            // Smallest weights go last; if equal, biggest pointers go last.
            x.cmp(y).then(px.cmp(py).reverse())
        });
        let weights = Vec::from_iter(weights.into_iter().map(|(_, x)| x));

        // Binary-search for the number of nodes that bring us the closest to the target size.
        let mut start = 0;
        let mut stop = weights.len();
        loop {
            if start >= stop {
                let result = self.underapproximate(&weights[..stop]);
                return result;
            }
            let check = (start + stop) / 2;
            let maybe_result = self.underapproximate(&weights[..check]);
            if maybe_result.size() == target_size {
                return maybe_result;
            } else if maybe_result.size() < target_size {
                // We don't have to cut as many nodes...
                stop = check;
            } else {
                // We need to cut more nodes...
                start = check + 1;
            }
        }
    }

    /**
    Compute a new [`Bdd`] `over` for which it holds that `over.cardinality() >= target_cardinality`
    and it holds that `self.implies(over)` (i.e. each valuation that satisfies `self` also
    satisfies `over`). Consequently, it holds that `over.cardinality() >= self.cardinality()`.

    The algorithm works by greedily re-routing BDD nodes to `1` which have the least amount
    of paths going through them, until the target cardinality is achieved.
    */
    pub fn overapproximate_to_cardinality(&self, target_cardinality: &BigUint) -> Bdd {
        let target_cardinality_int = BigInt::from(target_cardinality.clone());
        let self_cardinality = self.exact_cardinality();
        if self_cardinality >= target_cardinality_int {
            return self.clone();
        }

        let negation = self.not();
        let difference = target_cardinality_int - self_cardinality;
        let inverse_target = negation.exact_cardinality() - difference;
        let inverse_target_uint = inverse_target.to_biguint().unwrap_or(BigUint::zero());
        let under_negation = negation.underapproximate_to_cardinality(&inverse_target_uint);
        under_negation.not()
    }

    /**
    Compute a new [`Bdd`] `under` for which it holds that `under.cardinality() <= target_cardinality`
    and it holds that `under.implies(self)` (i.e. each valuation that satisfies `under` also
    satisfies `self`). Consequently, it holds that `under.cardinality() <= self.cardinality()`.

    The algorithm works by greedily re-routing BDD nodes to `0` which have the least amount
    of paths going through them, until the target cardinality is achieved.
    */
    pub fn underapproximate_to_cardinality(&self, target_cardinality: &BigUint) -> Bdd {
        let mut result = self.clone();
        let target_cardinality = BigInt::from(target_cardinality.clone());
        if target_cardinality == BigInt::zero() {
            return Bdd::mk_false(self.num_vars());
        }

        loop {
            let result_cardinality = result.exact_cardinality();
            if result_cardinality <= target_cardinality {
                return result;
            }
            // Compute the number of valuations going through each node and sort them.
            let mut weights = result
                .node_valuation_weights()
                .into_iter()
                .zip(result.pointers())
                .collect::<Vec<_>>();
            weights.sort_by(|(x, px), (y, py)| {
                // Smallest weights go last; if equal, biggest pointers go last.
                x.cmp(y).reverse().then(px.cmp(py))
            });

            // Keep saving pointers until we cover the desired cardinality.
            let mut to_remove = &result_cardinality - &target_cardinality;
            let mut to_eliminate: Vec<BddPointer> = Vec::new();
            while let Some((weight, pointer)) = weights.pop() {
                to_eliminate.push(pointer);
                to_remove -= BigInt::from(weight);
                if to_remove <= BigInt::zero() {
                    break;
                }
            }

            result = result.underapproximate(&to_eliminate);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::BddVariableSet;
    use crate::_test_util::mk_small_test_bdd;
    use num_bigint::{BigInt, BigUint};
    use num_traits::Zero;

    #[test]
    fn test_node_valuation_weights_small() {
        // v3 & !v4 over variables v1,...,v5
        let bdd = mk_small_test_bdd();
        let weights = bdd.node_valuation_weights();
        let valuations = bdd.exact_cardinality().to_biguint().unwrap();

        // The BDD is a single linear path, meaning each node actually has the same
        // number of paths passing through it.
        let expected = vec![
            BigUint::zero(),
            valuations.clone(),
            valuations.clone(),
            valuations.clone(),
        ];

        assert_eq!(weights, expected);
    }

    #[test]
    fn test_node_valuation_weights_medium() {
        // We want to build a BDD that looks like this:
        //     x1(a)
        //    /     \
        //   x2(b)  x3(b)
        //  /     \ /
        // x4(c)  x5(d)
        //  \    /
        //    1

        let set = BddVariableSet::new(&["a", "b", "c", "d"]);
        let bdd = set.eval_expression_string("(a => ((b & c) | (!b & d))) & (!a => (b & d))");

        assert_eq!(bdd.exact_cardinality(), BigInt::from(6));
        assert_eq!(bdd.size(), 7);

        let weights = bdd.node_valuation_weights();
        let expected = vec![
            BigUint::zero(),
            BigUint::from(6u8),
            BigUint::from(2u8),
            BigUint::from(4u8),
            BigUint::from(4u8),
            BigUint::from(2u8),
            BigUint::from(6u8),
        ];

        assert_eq!(weights, expected);
    }

    #[test]
    fn test_underapproximate_to_cardinality() {
        let set = BddVariableSet::new(&["a", "b", "c", "d"]);
        let bdd = set.eval_expression_string("(a => ((b & c) | (!b & d))) & (!a => (b & d))");
        let bdd_under_6 = bdd.underapproximate_to_cardinality(&BigUint::from(6u8));
        let bdd_under_5 = bdd.underapproximate_to_cardinality(&BigUint::from(5u8));
        let bdd_under_4 = bdd.underapproximate_to_cardinality(&BigUint::from(4u8));
        let bdd_under_3 = bdd.underapproximate_to_cardinality(&BigUint::from(3u8));
        let bdd_under_2 = bdd.underapproximate_to_cardinality(&BigUint::from(2u8));
        let bdd_under_1 = bdd.underapproximate_to_cardinality(&BigUint::from(1u8));
        assert_eq!(bdd, bdd_under_6);
        assert_eq!(bdd_under_5.exact_cardinality(), BigInt::from(4));
        assert_eq!(bdd_under_4, bdd_under_5);
        assert_eq!(bdd_under_3.exact_cardinality(), BigInt::from(2));
        assert_eq!(bdd_under_2, bdd_under_3);
        assert_eq!(bdd_under_1, set.mk_false());
    }

    #[test]
    fn test_underapproximate_to_size() {
        let set = BddVariableSet::new(&["a", "b", "c", "d"]);
        let bdd = set.eval_expression_string("(a => ((b & c) | (!b & d))) & (!a => (b & d))");
        let bdd_under_7 = bdd.underapproximate_to_size(7);
        let bdd_under_6 = bdd.underapproximate_to_size(6);
        let bdd_under_5 = bdd.underapproximate_to_size(5);
        let bdd_under_4 = bdd.underapproximate_to_size(4);
        assert_eq!(bdd, bdd_under_7);
        assert_eq!(bdd_under_6.exact_cardinality(), BigInt::from(4));
        assert_eq!(bdd_under_5.exact_cardinality(), BigInt::from(2));
        assert_eq!(bdd_under_4, set.mk_false());
    }

    #[test]
    fn test_overapproximate_to_size() {
        let set = BddVariableSet::new(&["a", "b", "c", "d"]);
        let bdd = set.eval_expression_string("(a => ((b & c) | (!b & d))) & (!a => (b & d))");
        let bdd_under_7 = bdd.overapproximate_to_size(7);
        let bdd_under_6 = bdd.overapproximate_to_size(6);
        let bdd_under_5 = bdd.overapproximate_to_size(5);
        let bdd_under_4 = bdd.overapproximate_to_size(4);
        let bdd_under_3 = bdd.overapproximate_to_size(3);
        assert_eq!(bdd, bdd_under_7);
        assert_eq!(bdd_under_6.exact_cardinality(), BigInt::from(8));
        assert_eq!(bdd_under_5.exact_cardinality(), BigInt::from(10));
        assert_eq!(bdd_under_4.exact_cardinality(), BigInt::from(12));
        assert_eq!(bdd_under_3, set.mk_true());
    }

    #[test]
    fn test_overapproximate_to_cardinality() {
        let set = BddVariableSet::new(&["a", "b", "c", "d"]);
        let bdd = set.eval_expression_string("(a => ((b & c) | (!b & d))) & (!a => (b & d))");
        let bdd_over_6 = bdd.overapproximate_to_cardinality(&BigUint::from(6u8));
        let bdd_over_7 = bdd.overapproximate_to_cardinality(&BigUint::from(7u8));
        let bdd_over_8 = bdd.overapproximate_to_cardinality(&BigUint::from(8u8));
        let bdd_over_9 = bdd.overapproximate_to_cardinality(&BigUint::from(9u8));
        let bdd_over_10 = bdd.overapproximate_to_cardinality(&BigUint::from(10u8));
        let bdd_over_11 = bdd.overapproximate_to_cardinality(&BigUint::from(11u8));
        let bdd_over_12 = bdd.overapproximate_to_cardinality(&BigUint::from(12u8));
        let bdd_over_13 = bdd.overapproximate_to_cardinality(&BigUint::from(13u8));
        let bdd_over_14 = bdd.overapproximate_to_cardinality(&BigUint::from(14u8));
        let bdd_over_15 = bdd.overapproximate_to_cardinality(&BigUint::from(15u8));
        let bdd_over_16 = bdd.overapproximate_to_cardinality(&BigUint::from(16u8));
        assert_eq!(bdd, bdd_over_6);
        assert_eq!(bdd_over_7.exact_cardinality(), BigInt::from(8));
        assert_eq!(bdd_over_7, bdd_over_8);
        assert_eq!(bdd_over_9.exact_cardinality(), BigInt::from(10));
        assert_eq!(bdd_over_9, bdd_over_10);
        assert_eq!(bdd_over_11.exact_cardinality(), BigInt::from(12));
        assert_eq!(bdd_over_11, bdd_over_12);
        assert!(bdd_over_13.is_true());
        assert!(bdd_over_14.is_true());
        assert!(bdd_over_15.is_true());
        assert!(bdd_over_16.is_true());
    }
}
