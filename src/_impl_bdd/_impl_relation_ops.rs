use crate::{Bdd, BddNode, BddPointer};
use fxhash::FxBuildHasher;
use std::collections::HashMap;

/// Advanced relation-like operations for `Bdd`s. Currently **experimental/unstable**.
impl Bdd {
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
    pub fn extended_witness(&self, _var_count: usize) -> Bdd {
        todo!("Maybe skip for now?")
        /*if var_count == 0 { return self.clone() };
        /*
            The algorithm "cuts" the Bdd into two parts - first var_count layers which will remain
            the same and the remaining layers which will be pruned. From each node on the
            var_count+1-st layer, select one (arbitrary) path by marking the nodes. If the
            path meets an already marked node, just follow the already marked path (avoid
            unnecessary markings). The new BDD then contains only the marked nodes in the second part.

            This will ensure every valuation in the first layer will eventually lead to a single
            path in the second layer. However, this approach technically does not minimise the
            number of resulting nodes, however, is obviously always linear.

            Also, remember that we have to actually fix "undecided" nodes (i.e. skipped variables).

            Here, we actually perform marking and creation of new Bdd at the same time to save some
            memory and time...
         */

        let mut result = Bdd::mk_true(self.num_vars());
        // Maps the old BddPointer to the index in the new Bdd
        let mut mapping: HashMap<BddPointer, BddPointer> = HashMap::new();

        // iterate the Bdd nodes (we have to process from bottom to top because otherwise copy
        // would not be valid)
        for i in self.pointers() {
            if self.var_of(i) < var_count {
                // We are in the first layer - just copy the node
                let low = self.low_link_of(i);
                let high = self.high_link_of(i);
                // See that mapping[low]/mapping[high] must exist because low/high is already processed.
                result.push_node(BddNode::mk_node(self.var_of(i), mapping[low], mapping[high]));
                mapping.insert(i, result.root_pointer());
            } else if self.var_of(i) == var_count {    // only mark paths from boundary layer
                if mapping.contains_key(&i) { continue; }   // this could sometimes happen
                // First, find path from boundary node to terminal or marked node
                let mut path = Vec::new();
                path.push(i);
                while let Some(node) = path.last() {
                    let low = self.low_link_of(*node);
                    let high = self.high_link_of(*node);
                    let to_add = if !low.is_zero() { low } else { high };
                    if to_add.is_terminal() || mapping.contains_key(&node) { break; }
                    path.push(to_add);
                }
                // Mark path
                let mut node = i;
                while !node.is_terminal() {
                    if marked.contains(&node) { break; }    // if already marked, path is finished
                    marked.insert(node);
                    let low = self.low_link_of(node);
                    let high = self.high_link_of(node);
                    if !low.is_zero() {
                        node = low;
                    } else {
                        node = high;
                    }
                }
                assert!(node.is_one());
            } else {
                // Non-boundary nodes are either processed inside the while loop above, or skipped
                // entirely.
            }
        }

        /*
            Alternative algorithm to consider in the future: Reverse the edges in the lower layer
            and compute a DFS tree starting from `1` node. Potentially simpler, but requires reversed
            edges...
         */

        return ...*/
    }
}
