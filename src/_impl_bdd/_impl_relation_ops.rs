use crate::{Bdd, BddNode, BddPointer, BddVariable};
use fxhash::FxBuildHasher;
use std::cmp::max;
use std::collections::HashMap;

/// Advanced relation-like operations for `Bdd`s. Currently **experimental/unstable**.
impl Bdd {
    /// Eliminates one given variable from the `Bdd`.
    ///
    /// For variable `x` and bdd `B`, this is equivalent to writing `(x & B) | (!x & B)`. Currently,
    /// this is also the implementation we are using. In the future it is possible to explore more
    /// efficient implementations.
    pub fn var_projection(&self, variable: BddVariable) -> Bdd {
        return self.or(&self.invert_input(variable));
    }

    /// Performs projection, keeping the first `keep` variables in this `Bdd`, unifying the remaining ones.
    /// The variables remain "in the Bdd" (the number of variables does not decrease), they are just
    /// "effectively" quantified away.
    pub fn projection(&self, keep: u16) -> Bdd {
        // ensures result won't be empty
        if self.is_false() {
            return self.clone();
        }
        /*
            This special type of projection is preformed by "forgetting" everything except the
            first `keep` layers of the graph. Then, every reference to a missing node is replaced
            with reference to `1`, since every deleted node must have had at least one path to one.

            Then the BDD is reduced as in the standard `apply` operation.
        */

        let mut result = Bdd::mk_true(self.num_vars());

        // Ensures we don't create duplicates.
        let mut existing: HashMap<BddNode, BddPointer, FxBuildHasher> =
            HashMap::with_capacity_and_hasher(self.size(), FxBuildHasher::default());
        existing.insert(BddNode::mk_zero(self.num_vars()), BddPointer::zero());
        existing.insert(BddNode::mk_one(self.num_vars()), BddPointer::one());

        // Maps pointers in the old Bdd to pointers in the new Bdd.
        let mut finished: HashMap<BddPointer, BddPointer, FxBuildHasher> =
            HashMap::with_capacity_and_hasher(self.size(), FxBuildHasher::default());
        // Terminals automatically map to each other - this ensures terminal never enters stack.
        finished.insert(BddPointer::one(), BddPointer::one());
        finished.insert(BddPointer::zero(), BddPointer::zero());

        let mut stack = Vec::new();
        stack.push(self.root_pointer());

        while let Some(&on_stack) = stack.last() {
            if finished.contains_key(&on_stack) {
                stack.pop();
            } else if self.var_of(on_stack).0 >= keep {
                // everything that leaves top `keep` variables points automatically to `1`
                finished.insert(on_stack, BddPointer::one());
            } else {
                let (l, h) = (self.low_link_of(on_stack), self.high_link_of(on_stack));
                let new_low = finished.get(&l).cloned();
                let new_high = finished.get(&h).cloned();
                if let (Some(new_low), Some(new_high)) = (new_low, new_high) {
                    // Both children are resolved - resolve parent as well.
                    if new_low == new_high {
                        // No decision - skip this node and go directly to
                        finished.insert(on_stack, new_low);
                    } else {
                        // There is a decision here.
                        let node = BddNode::mk_node(self.var_of(on_stack), new_low, new_high);
                        if let Some(&index) = existing.get(&node) {
                            // Node already exists, just make it a result of this computation.
                            finished.insert(on_stack, index);
                        } else {
                            // Node does not exist, it needs to be pushed to result.
                            result.push_node(node);
                            existing.insert(node, result.root_pointer());
                            finished.insert(on_stack, result.root_pointer());
                        }
                    }
                } else {
                    // If child is not resolved, push it and continue.
                    if new_low.is_none() {
                        stack.push(l);
                    }
                    if new_high.is_none() {
                        stack.push(h);
                    }
                }
            }
        }

        return result;
    }

    /// Selects a witness for the first `var_count` variables in this `Bdd`.
    ///
    /// This extends the behaviour of the standard `sat_witness` function which picks one
    /// satisfying valuation from the `Bdd`. Here, we instead pick one full satisfying valuation
    /// for every satisfying prefix on the first `var_count` variables.
    ///
    /// Currently, we only support a variable prefix because this makes the operation almost trivial
    /// to implement. In the future, we should aim to support this operation for an arbitrary
    /// subset of variables.
    pub fn extended_witness(&self, var_count: u16) -> Bdd {
        if self.is_false() {
            return self.clone();
        }

        let mut result = Bdd::mk_true(self.num_vars());

        // Ensures we don't create duplicates.
        let mut existing: HashMap<BddNode, BddPointer, FxBuildHasher> =
            HashMap::with_capacity_and_hasher(self.size(), FxBuildHasher::default());
        existing.insert(BddNode::mk_zero(self.num_vars()), BddPointer::zero());
        existing.insert(BddNode::mk_one(self.num_vars()), BddPointer::one());

        // Maps pointers in the old Bdd to pointers in the new Bdd.
        let mut finished: HashMap<BddPointer, BddPointer, FxBuildHasher> =
            HashMap::with_capacity_and_hasher(self.size(), FxBuildHasher::default());
        // Terminals automatically map to each other - this ensures terminal never enters stack.
        finished.insert(BddPointer::one(), BddPointer::one());
        finished.insert(BddPointer::zero(), BddPointer::zero());

        let mut stack = Vec::new();
        stack.push(self.root_pointer());

        /// Add extra Bdd nodes above new_node to ensure all variables up to the one in
        /// on_stack is fixed. Return a pointer to the "new" new_node that has all variables
        /// fixed.
        fn fix_free_variables(
            last_var_to_fix: u16,
            new_node: BddPointer,
            output: &mut Bdd,
            existing: &mut HashMap<BddNode, BddPointer, FxBuildHasher>,
        ) -> BddPointer {
            /* TODO
                There seems to be a better approach at picking values to fix.
                The idea is to use existing nodes in the Bdd whenever possible. So instead of arbitrarily
                always fixing to zero, check if the node has a parent with the correct variable and if so,
                use that parent instead of creating an entire new node. But this requires computing predecessors...
            */
            if new_node.is_zero() {
                return new_node;
            } // zero needs no fixing
            let mut fix_var = output.var_of(new_node).0;
            if fix_var == 0 {
                return new_node;
            } // nothing to fix, but shouldn't happen...
            fix_var -= 1; // move to the actual variable to fix
            let mut result = new_node;
            while fix_var >= last_var_to_fix {
                // fix `fix_var` to zero
                let node = BddNode::mk_node(BddVariable(fix_var), result, BddPointer::zero());
                if let Some(&index) = existing.get(&node) {
                    result = index;
                } else {
                    output.push_node(node);
                    existing.insert(node, output.root_pointer());
                    result = output.root_pointer();
                }
                if last_var_to_fix == 0 && fix_var == 0 {
                    break;
                } // hack to handle 0 in last_var_to_fix
                fix_var -= 1;
            }
            return result;
        }

        while let Some(&on_stack) = stack.last() {
            if finished.contains_key(&on_stack) {
                stack.pop();
            } else if self.var_of(on_stack).0 < var_count {
                // This node is in the upper layer - that means we need to process both children
                // of the node normally (we might need to fix some values on the boundary though)
                let (l, h) = (self.low_link_of(on_stack), self.high_link_of(on_stack));
                let new_low = finished.get(&l).cloned();
                let new_high = finished.get(&h).cloned();
                if let (Some(new_low), Some(new_high)) = (new_low, new_high) {
                    // Both children are resolved - resolve parent as well
                    if new_low == new_high {
                        // no decision, just propagate either node
                        // (no fixing here because left and right would fix the same way, so we do it on actual decision)
                        finished.insert(on_stack, new_low);
                    } else {
                        // There is a decision here.
                        // In case some variables need fixing...
                        let last_var_to_fix = max(var_count, self.var_of(on_stack).0 + 1);
                        let new_low = fix_free_variables(
                            last_var_to_fix,
                            new_low,
                            &mut result,
                            &mut existing,
                        );
                        let new_high = fix_free_variables(
                            last_var_to_fix,
                            new_high,
                            &mut result,
                            &mut existing,
                        );
                        let node = BddNode::mk_node(self.var_of(on_stack), new_low, new_high);
                        if let Some(&index) = existing.get(&node) {
                            // Node already exists, just make it a result of this computation.
                            finished.insert(on_stack, index);
                        } else {
                            // Node does not exist, it needs to be pushed to result.
                            result.push_node(node);
                            existing.insert(node, result.root_pointer());
                            finished.insert(on_stack, result.root_pointer());
                        }
                    }
                } else {
                    // If child is not resolved, push it and continue.
                    if new_low.is_none() {
                        stack.push(l);
                    }
                    if new_high.is_none() {
                        stack.push(h);
                    }
                }
            } else {
                // This is the lower layer - here, we only need to process one child that
                // corresponds to the path we are taking.

                /* TODO: A better greedy strategy would prefer a finished node instead of picking left always. */
                // Pick one child that has a valid path
                let follow_in = if self.low_link_of(on_stack).is_zero() {
                    self.high_link_of(on_stack)
                } else {
                    self.low_link_of(on_stack)
                };

                if let Some(follow_in) = finished.get(&follow_in).cloned() {
                    let last_var_to_fix = max(var_count, self.var_of(on_stack).0 + 1);
                    let follow_in =
                        fix_free_variables(last_var_to_fix, follow_in, &mut result, &mut existing);
                    // Make a new node, erasing one branch of the graph.
                    let node = if self.low_link_of(on_stack).is_zero() {
                        BddNode::mk_node(self.var_of(on_stack), BddPointer::zero(), follow_in)
                    } else {
                        BddNode::mk_node(self.var_of(on_stack), follow_in, BddPointer::zero())
                    };
                    if let Some(&index) = existing.get(&node) {
                        // Node already exists, just make it a result of this computation.
                        finished.insert(on_stack, index);
                    } else {
                        // Node does not exist, it needs to be pushed to result.
                        result.push_node(node);
                        existing.insert(node, result.root_pointer());
                        finished.insert(on_stack, result.root_pointer());
                    }
                } else {
                    stack.push(follow_in);
                }
            }
        }

        // At this point, the root pointer might still need fixing - although this should happen
        // only when var_count == 0
        if result.var_of(result.root_pointer()).0 > var_count {
            fix_free_variables(var_count, result.root_pointer(), &mut result, &mut existing);
        }

        return result;
    }
}
