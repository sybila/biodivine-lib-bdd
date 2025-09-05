use crate::{Bdd, BddPointer, BddVariable};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use std::cmp::Ordering;
use std::collections::HashSet;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
struct BfsPointer(BddPointer, BddVariable);

impl PartialOrd for BfsPointer {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BfsPointer {
    fn cmp(&self, other: &Self) -> Ordering {
        self.1.cmp(&other.1)
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
        let node_count = self.size();
        let root = self.root_pointer();
        let root_var = self.var_of(root);

        // First, compute `outgoing_vals` using DFS. This is the same as cardinality computation.

        // The number of satisfying valuations of the function defined by the corresponding node.
        // The `Some`/`None` option encodes whether the node has been already fully processed or
        // not. Due to DFS ordering and acyclicity, we know that the node cannot be visited again
        // until it is fully processed.

        let mut outgoing_vals: Vec<Option<BigUint>> = vec![None; node_count];
        outgoing_vals[0] = Some(BigUint::zero());
        outgoing_vals[1] = Some(BigUint::one());

        let mut stack: Vec<BddPointer> = vec![root];
        while let Some(node) = stack.pop() {
            if outgoing_vals[node.to_index()].is_some() {
                // This node already has outgoing paths computed.
                continue;
            } else {
                let var = self.var_of(node);
                let low = self.low_link_of(node);
                let high = self.high_link_of(node);

                // Now, if both low and high have outgoing paths computed, we can use them
                // to compute outgoing paths for this node as well. Otherwise, simply push
                // all those nodes that are not processed yet.
                match (
                    &outgoing_vals[low.to_index()],
                    &outgoing_vals[high.to_index()],
                ) {
                    (Some(low_val), Some(high_val)) => {
                        let low_var = self.var_of(low);
                        let high_var = self.var_of(high);
                        let low_var_change = (low_var.to_index() - var.to_index()) - 1;
                        let high_var_change = (high_var.to_index() - var.to_index()) - 1;
                        let low_multiplier = BigUint::one() << low_var_change;
                        let high_multiplier = BigUint::one() << high_var_change;

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

        // All outgoing valuation counts are computed.
        debug_assert!(outgoing_vals.iter().all(|x| x.is_some()));

        // Second, compute `incoming vals` using BFS-like search. This is the number of valuations
        // that reaches the given node. It is computed "level-by-level", where each level consists
        // of nodes conditioning on one BDD variable. This ensures that once a node is being
        // processed, all of its parent nodes are already fully computed (`BfsPointer` implements
        // this ordering). To do this, we first pre-sort the BDD pointers based on this "level",
        // and then process them in-order.

        let mut queue = self
            .pointers()
            .skip(2) // Ignore terminal nodes.
            .map(|pointer| BfsPointer(pointer, self.var_of(pointer)))
            .collect::<Vec<_>>();
        queue.sort();

        let mut incoming_vals: Vec<BigUint> = vec![BigUint::zero(); node_count];
        // Need to account for "missing" variables that appear "above" the root.
        incoming_vals[root.to_index()] = BigUint::one();

        for BfsPointer(node, var) in queue {
            // At this point, the iteration order guarantees that all parents have been processed
            // and the number of incoming valuations is final for this node.

            let low = self.low_link_of(node);
            let high = self.high_link_of(node);

            let low_var = self.var_of(low);
            let high_var = self.var_of(high);
            let low_var_change = (low_var.to_index() - var.to_index()) - 1;
            let high_var_change = (high_var.to_index() - var.to_index()) - 1;
            let low_multiplier = BigUint::one() << low_var_change;
            let high_multiplier = BigUint::one() << high_var_change;

            let node_incoming = incoming_vals[node.to_index()].clone();

            incoming_vals[low.to_index()] += &node_incoming * &low_multiplier;
            incoming_vals[high.to_index()] += &node_incoming * &high_multiplier;
        }

        // The number of outgoing valuations from the root must be the same as the number
        // incoming to one.
        debug_assert_eq!(
            &incoming_vals[1],
            outgoing_vals[root.to_index()].as_ref().unwrap()
        );

        let root_multiplier = BigUint::one() << root_var.to_index();
        incoming_vals
            .into_iter()
            .zip(outgoing_vals)
            .map(|(incoming, outgoing)| {
                &root_multiplier
                    * incoming
                    * outgoing.expect("Invariant violation: Missing outgoing valuation count.")
            })
            .collect()
    }

    /// Compute a new BDD `over` which overapproximates `self` BDD by re-routing the `to_eliminate`
    /// nodes to `1` and removing all nodes that become unreachable due to this operation.
    ///
    /// The BDD `over` is guaranteed to be smaller than `self` in terms of node count and greater
    /// in terms of valuation count.
    ///
    /// *The given pointers do not need to be sorted in any specific way or be unique, but
    /// keep in mind that the complexity grows with the list length, so it probably should not
    /// contain duplicates if this can be easily avoided. The pointers must be valid within
    /// this BDD and must not be terminal.*
    pub fn overapproximate(&self, to_eliminate: &[BddPointer]) -> Bdd {
        let to_eliminate: HashSet<BddPointer> = HashSet::from_iter(to_eliminate.iter().cloned());
        if to_eliminate.contains(&self.root_pointer()) {
            // If we are trying to eliminate the root, the result is the true BDD.
            return Bdd::mk_true(self.num_vars());
        }

        if to_eliminate.contains(&BddPointer::zero()) || to_eliminate.contains(&BddPointer::one()) {
            panic!("Precondition violation: Cannot eliminate terminal node.");
        }

        let mut copy = self.clone();
        for node in copy.pointers().skip(2) {
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

    /// Compute a new BDD `under` which underapproximates `self` BDD by re-routing the `to_eliminate`
    /// nodes to `0` and removing all nodes that become unreachable due to this operation.
    ///
    /// The BDD `under` is guaranteed to be smaller than `self` in terms of node count and smaller
    /// in terms of valuation count.
    ///
    /// *The given pointers do not need to be sorted in any specific way or be unique, but
    /// keep in mind that the complexity grows with the list length, so it probably should not
    /// contain duplicates if this can be easily avoided. The pointers must be valid within
    /// this BDD and must not be terminal.*
    pub fn underapproximate(&self, to_eliminate: &[BddPointer]) -> Bdd {
        let to_eliminate: HashSet<BddPointer> = HashSet::from_iter(to_eliminate.iter().cloned());
        if to_eliminate.contains(&self.root_pointer()) {
            // If we are trying to eliminate the root, the result is the false BDD.
            return Bdd::mk_false(self.num_vars());
        }

        if to_eliminate.contains(&BddPointer::zero()) || to_eliminate.contains(&BddPointer::one()) {
            panic!("Precondition violation: Cannot eliminate terminal node.");
        }

        let mut copy = self.clone();
        for node in copy.pointers().skip(2) {
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

    /// Compute a new [`Bdd`] `over` for which it holds that `over.size() <= target_size` and it
    /// holds that `self.implies(over)` (i.e. each valuation that satisfies `self` also
    /// satisfies `over`). Consequently, it holds that `over.cardinality() >= self.cardinality()`.
    ///
    /// See also [`Bdd::overapproximate`].
    pub fn overapproximate_to_size(&self, target_size: usize) -> Bdd {
        /*
           For the overapproximation, I actually want to under-approximate the negation
           of the function, because our greedy metric selects the nodes that *remove* the least
           amount of valuations from the BDD. Hence, to achieve the best over-approximation,
           we want to remove the least amount of valuations from the negation and then negate
           the BDD back (relying on the fact that negation does not change node count).
        */
        self.not().underapproximate_to_size(target_size).not()
    }

    /// Compute a new [`Bdd`] `under` for which it holds that `under.size() <= target_size` and it
    /// holds that `under.implies(self)` (i.e. each valuation that satisfies `under` also
    /// satisfies `self`). Consequently, it holds that `under.cardinality() <= self.cardinality()`.
    ///
    /// See also [`Bdd::underapproximate`].
    pub fn underapproximate_to_size(&self, target_size: usize) -> Bdd {
        /* Check extreme cases: */

        if target_size <= 1 {
            return Bdd::mk_false(self.num_vars());
        }

        if target_size == 2 {
            return if self.is_true() {
                Bdd::mk_true(self.num_vars())
            } else {
                Bdd::mk_false(self.num_vars())
            };
        }

        if target_size >= self.size() {
            return self.clone();
        }

        /* Compute the nodes that should be removed: */

        let to_cut = self.size() - target_size;
        assert!(to_cut > 0 && to_cut < self.size());

        // Compute the number of valuations going through each node and sort them.
        let mut weights: Vec<(BddPointer, BigUint)> = self
            .pointers()
            .zip(self.node_valuation_weights())
            .skip(2) // Do not remove terminal nodes...
            .collect();
        weights.sort_by(|(px, x), (py, y)| {
            // Smallest weights go first; if equal, biggest pointers go last.
            x.cmp(y).then(px.cmp(py).reverse())
        });

        let priorities: Vec<BddPointer> =
            weights.into_iter().take(to_cut).map(|(x, _)| x).collect();

        // Binary-search for the number of nodes that bring us the closest to the target size.

        let mut start = 0; // Index of the first valid search position.
        let mut stop = to_cut; // Index after the last valid position.
        loop {
            if start >= stop {
                let result = self.underapproximate(&priorities[..stop]);
                return result;
            }
            let check = (start + stop) / 2;
            let maybe_result = self.underapproximate(&priorities[..check]);
            match maybe_result.size().cmp(&target_size) {
                Ordering::Equal => {
                    return maybe_result;
                }
                Ordering::Less => {
                    // We don't have to cut as many nodes...
                    stop = check;
                }
                Ordering::Greater => {
                    // We need to cut more nodes...
                    start = check + 1;
                }
            }
        }
    }

    /// Compute a new [`Bdd`] `over` for which it holds that `over.cardinality() >= target_cardinality`
    /// and it holds that `self.implies(over)` (i.e. each valuation that satisfies `self` also
    /// satisfies `over`). Consequently, it holds that `over.cardinality() >= self.cardinality()`.
    ///
    /// See also [`Bdd::overapproximate`].
    pub fn overapproximate_to_cardinality(&self, target_cardinality: &BigUint) -> Bdd {
        let self_cardinality = self
            .exact_cardinality()
            .to_biguint()
            .expect("Invariant violation: Exact cardinality must be non-negative.");
        if &self_cardinality >= target_cardinality {
            return self.clone();
        }

        // The same principle as in `overapproximate_to_size`.

        let negation = self.not();
        let negation_cardinality = negation
            .exact_cardinality()
            .to_biguint()
            .expect("Invariant violation: Exact cardinality must be non-negative.");
        let inverse_target = negation_cardinality - (target_cardinality - self_cardinality);
        let under_negation = negation.underapproximate_to_cardinality(&inverse_target);
        under_negation.not()
    }

    /// Compute a new [`Bdd`] `under` for which it holds that `under.cardinality() <= target_cardinality`
    /// and it holds that `under.implies(self)` (i.e. each valuation that satisfies `under` also
    /// satisfies `self`). Consequently, it holds that `under.cardinality() <= self.cardinality()`.
    pub fn underapproximate_to_cardinality(&self, target_cardinality: &BigUint) -> Bdd {
        let target_cardinality = BigInt::from(target_cardinality.clone());
        let self_cardinality = self.exact_cardinality();

        if target_cardinality <= BigInt::zero() {
            return Bdd::mk_false(self.num_vars());
        }

        if self_cardinality <= target_cardinality {
            return self.clone();
        }

        // Compute the number of valuations going through each node and sort them.
        let mut weights: Vec<(BddPointer, BigUint)> = self
            .pointers()
            .zip(self.node_valuation_weights())
            .skip(2) // Do not remove terminal nodes...
            .collect();
        weights.sort_by(|(px, x), (py, y)| {
            // Smallest weights go last; if equal, biggest pointers go last.
            x.cmp(y).reverse().then(px.cmp(py))
        });

        let mut to_eliminate: Vec<BddPointer> = Vec::new();
        let mut to_remove = &self_cardinality - &target_cardinality;
        loop {
            // Move enough pointers between `weights` and `to_eliminate` to cover at least
            // `to_remove` valuations.
            while let Some((pointer, weight)) = weights.pop() {
                to_eliminate.push(pointer);
                to_remove -= BigInt::from(weight);
                if to_remove <= BigInt::zero() {
                    break;
                }
            }

            let result = self.underapproximate(&to_eliminate);
            let result_cardinality = result.exact_cardinality();

            // This actually may not eliminate *enough* valuations because nodes will cover the
            // same valuations. E.g. if we select two nodes, each covering two valuations, it
            // may very well happen that this only removes three (or even two) valuations, assuming
            // the valuation visits both removed nodes.

            if result_cardinality <= target_cardinality {
                return result;
            } else {
                // In the next iteration, we need to remove at least this many valuations.
                to_remove = &result_cardinality - &target_cardinality;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::_test_util::mk_small_test_bdd;
    use crate::{BddPointer, BddVariable, BddVariableSet};
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
    fn test_base_methods() {
        let set = BddVariableSet::new(&["a", "b", "c", "d"]);
        let bdd = set.eval_expression_string("(a => ((b & c) | (!b & d))) & (!a => (b & d))");

        println!("{:?}", bdd);
        let x1 = BddPointer::from_index(6);
        let x2 = BddPointer::from_index(4);
        let x3 = BddPointer::from_index(5);
        let x4 = BddPointer::from_index(3);
        let x5 = BddPointer::from_index(2);

        assert!(bdd.overapproximate(&[x1]).is_true());
        assert!(bdd.underapproximate(&[x1]).is_false());

        // We completely cut off the last level of the BDD.
        let bdd_under = bdd.underapproximate(&[x4, x5]);
        assert!(bdd_under.is_false());

        // We completely cut off the top level of the BDD.
        let bdd_over = bdd.overapproximate(&[x2, x3]);
        assert!(bdd_over.is_true());
    }

    #[test]
    #[should_panic]
    fn test_over_terminals() {
        let set = BddVariableSet::new(&["a", "b", "c", "d"]);
        let bdd = set.eval_expression_string("(a => ((b & c) | (!b & d))) & (!a => (b & d))");
        let _ = bdd.overapproximate(&[BddPointer::zero()]);
    }

    #[test]
    #[should_panic]
    fn test_under_terminals() {
        let set = BddVariableSet::new(&["a", "b", "c", "d"]);
        let bdd = set.eval_expression_string("(a => ((b & c) | (!b & d))) & (!a => (b & d))");
        let _ = bdd.overapproximate(&[BddPointer::one()]);
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

        // Atomic cases:
        assert_eq!(set.mk_true().underapproximate_to_size(1), set.mk_false());
        assert_eq!(set.mk_true().underapproximate_to_size(2), set.mk_true());
        assert_eq!(
            set.mk_var(BddVariable::from_index(1))
                .underapproximate_to_size(2),
            set.mk_false()
        );

        // Complex case:
        let bdd = set.eval_expression_string("(a => ((b & c) | (!b & d))) & (!a => (b & d))");
        let bdd_under_7 = bdd.underapproximate_to_size(7);
        let bdd_under_6 = bdd.underapproximate_to_size(6);
        let bdd_under_5 = bdd.underapproximate_to_size(5);
        let bdd_under_4 = bdd.underapproximate_to_size(4);
        assert!(bdd_under_7.size() <= 7);
        assert!(bdd_under_6.size() <= 6);
        assert!(bdd_under_5.size() <= 5);
        assert!(bdd_under_4.size() <= 4);
        assert_eq!(bdd, bdd_under_7);
        assert_eq!(bdd_under_6.exact_cardinality(), BigInt::from(4));
        assert_eq!(bdd_under_5.exact_cardinality(), BigInt::from(2));
        assert_eq!(bdd_under_4, set.mk_false());
    }

    #[test]
    fn test_overapproximate_to_size() {
        let set = BddVariableSet::new(&["a", "b", "c", "d"]);
        let bdd = set.eval_expression_string("(a => ((b & c) | (!b & d))) & (!a => (b & d))");
        let bdd_over_7 = bdd.overapproximate_to_size(7);
        let bdd_over_6 = bdd.overapproximate_to_size(6);
        let bdd_over_5 = bdd.overapproximate_to_size(5);
        let bdd_over_4 = bdd.overapproximate_to_size(4);
        let bdd_over_3 = bdd.overapproximate_to_size(3);
        assert!(bdd_over_7.size() <= 7);
        assert!(bdd_over_6.size() <= 6);
        assert!(bdd_over_5.size() <= 5);
        assert!(bdd_over_4.size() <= 4);
        assert_eq!(bdd, bdd_over_7);
        assert_eq!(bdd_over_6.exact_cardinality(), BigInt::from(8));
        assert_eq!(bdd_over_5.exact_cardinality(), BigInt::from(10));
        assert_eq!(bdd_over_4.exact_cardinality(), BigInt::from(12));
        assert_eq!(bdd_over_3, set.mk_true());
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
