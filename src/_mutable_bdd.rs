use crate::{Bdd, BddNode, BddPointer, BddVariable, MutableBdd};
use fxhash::FxBuildHasher;
use std::cmp::{max, min};
use std::collections::HashMap;

impl MutableBdd {
    pub fn as_bdd(&self) -> &Bdd {
        &self.0
    }

    pub fn from_bdd(bdd: Bdd) -> MutableBdd {
        let mut map = HashMap::with_capacity_and_hasher(bdd.size(), FxBuildHasher::default());
        for pointer in bdd.pointers() {
            map.insert(bdd.0[pointer.to_index()].clone(), pointer);
        }
        MutableBdd(bdd, map, 0)
    }

    #[inline(always)]
    pub fn num_vars(&self) -> u16 {
        self.as_bdd().num_vars()
    }

    #[inline(always)]
    fn root_pointer(&self) -> BddPointer {
        self.0.root_pointer()
    }

    #[inline(always)]
    pub fn size(&self) -> usize {
        self.as_bdd().size()
    }

    #[inline(always)]
    fn var_of(&self, pointer: BddPointer) -> BddVariable {
        self.as_bdd().var_of(pointer)
    }

    #[inline(always)]
    fn low_link_of(&self, pointer: BddPointer) -> BddPointer {
        self.as_bdd().low_link_of(pointer)
    }

    #[inline(always)]
    fn high_link_of(&self, pointer: BddPointer) -> BddPointer {
        self.as_bdd().high_link_of(pointer)
    }

    fn ensure_node(&mut self, node: BddNode) -> BddPointer {
        if let Some(index) = self.1.get(&node) {
            *index
        } else {
            self.0.push_node(node.clone());
            self.1.insert(node, self.0.root_pointer());
            self.2 += 1;
            self.0.root_pointer()
        }
    }

    fn finish_operation(&mut self, new_root: BddPointer) {
        // Since the BDD may not be minimal, the root might already exists and be deeper in the
        // BDD. For now, as a hack, we recreate the node again at the end of the BDD if this
        // happens.
        if self.0.root_pointer() != new_root {
            let node = self.0 .0[new_root.to_index()].clone();
            self.0.push_node(node.clone());
            self.1.insert(node.clone(), self.0.root_pointer());
            self.2 += 1;
        }

        // As the BDD gets bigger, it will accumulate extra nodes that are no longer used.
        // To do "garbage collection", we can just run a very simple sweep through the whole BDD.
        // We do this if at least half the nodes are "fresh".
        if self.2 > self.0.size() / 2 {
            println!("Running GC on {} nodes.", self.0.size());
            // This quite sub-optimal, but should be good enough for now.
            *self = MutableBdd::from_bdd(self.0.and(&Bdd::mk_true(self.0.num_vars())));
            println!("GC finished. New size is {}.", self.0.size());
        }
    }

    /// Apply a general binary operation to two given `Bdd` objects.
    ///
    /// The `op_function` specifies the actual logical operation that will be performed. See
    /// `crate::op_function` module for examples.
    ///
    /// In general, this function can be used to slightly speed up less common Boolean operations
    /// or to fuse together several operations (like negation and binary operation).
    pub fn binary_op<T>(left: &mut MutableBdd, right: &Bdd, op_function: T)
    where
        T: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    {
        apply(left, right, op_function)
    }

    /// Apply a general binary operation together with up-to three Bdd variable flips. See also `binary_op`.
    ///
    /// A flip exchanges the edges of all decision nodes with the specified variable `x`.
    /// As a result, the set of bitvectors represented by this Bdd has the value of `x` negated.
    ///
    /// With this operation, you can apply such flip to both input operands as well as the output
    /// Bdd. This can greatly simplify implementation of state space generators for asynchronous
    /// systems.
    pub fn fused_binary_flip_op<T>(
        left: (&mut MutableBdd, Option<BddVariable>),
        right: (&Bdd, Option<BddVariable>),
        flip_output: Option<BddVariable>,
        op_function: T,
    ) where
        T: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    {
        apply_with_flip(left.0, right.0, left.1, right.1, flip_output, op_function)
    }
}

fn apply<T>(left: &mut MutableBdd, right: &Bdd, terminal_lookup: T)
where
    T: Fn(Option<bool>, Option<bool>) -> Option<bool>,
{
    apply_with_flip(left, right, None, None, None, terminal_lookup)
}

fn apply_with_flip<T>(
    left: &mut MutableBdd,
    right: &Bdd,
    flip_left_if: Option<BddVariable>,
    flip_right_if: Option<BddVariable>,
    flip_out_if: Option<BddVariable>,
    terminal_lookup: T,
) where
    T: Fn(Option<bool>, Option<bool>) -> Option<bool>,
{
    let num_vars = left.num_vars();
    if right.num_vars() != num_vars {
        panic!(
            "Var count mismatch: BDDs are not compatible. {} != {}",
            num_vars,
            right.num_vars()
        );
    }
    check_flip_bounds(num_vars, flip_left_if);
    check_flip_bounds(num_vars, flip_right_if);
    check_flip_bounds(num_vars, flip_out_if);

    // Task is a pair of pointers into the `left` and `right` BDDs.
    #[derive(Eq, PartialEq, Hash, Copy, Clone)]
    struct Task {
        left: BddPointer,
        right: BddPointer,
    }

    // `stack` is used to explore the two BDDs "side by side" in DFS-like manner. Each task
    // on the stack is a pair of nodes that needs to be fully processed before we are finished.
    let mut stack: Vec<Task> = Vec::with_capacity(2 * usize::from(num_vars));
    let root_task = Task {
        left: left.root_pointer(),
        right: right.root_pointer(),
    };
    stack.push(root_task.clone());

    // `finished` is a memoization cache of tasks which are already completed, since the same
    // combination of nodes can be often explored multiple times.
    let mut finished: HashMap<Task, BddPointer, FxBuildHasher> =
        HashMap::with_capacity_and_hasher(max(left.size(), right.size()), FxBuildHasher::default());

    while let Some(on_stack) = stack.last() {
        if finished.contains_key(on_stack) {
            stack.pop();
        } else {
            // skip finished tasks
            let (l, r) = (on_stack.left, on_stack.right);

            // Determine which variable we are conditioning on, moving from smallest to largest.
            let (l_v, r_v) = (left.var_of(l), right.var_of(r));
            let decision_var = min(l_v, r_v);

            // If the variable is the same as in the left/right decision node,
            // advance the exploration there. Otherwise, keep the pointers the same.
            let (l_low, l_high) = if l_v != decision_var {
                (l, l)
            } else if Some(l_v) == flip_left_if {
                (left.high_link_of(l), left.low_link_of(l))
            } else {
                (left.low_link_of(l), left.high_link_of(l))
            };
            let (r_low, r_high) = if r_v != decision_var {
                (r, r)
            } else if Some(r_v) == flip_right_if {
                (right.high_link_of(r), right.low_link_of(r))
            } else {
                (right.low_link_of(r), right.high_link_of(r))
            };

            // Two tasks which correspond to the two recursive sub-problems we need to solve.
            let comp_low = Task {
                left: l_low,
                right: r_low,
            };
            let comp_high = Task {
                left: l_high,
                right: r_high,
            };

            // Try to solve the tasks using terminal lookup table or from cache.
            let new_low = terminal_lookup(l_low.as_bool(), r_low.as_bool())
                .map(BddPointer::from_bool)
                .or_else(|| finished.get(&comp_low).cloned());
            let new_high = terminal_lookup(l_high.as_bool(), r_high.as_bool())
                .map(BddPointer::from_bool)
                .or_else(|| finished.get(&comp_high).cloned());

            // If both values are computed, mark this task as resolved.
            if let (Some(new_low), Some(new_high)) = (new_low, new_high) {
                if new_low == new_high {
                    // There is no decision, just skip this node and point to either child.
                    finished.insert(*on_stack, new_low);
                } else {
                    // There is a decision here.
                    let node = if flip_out_if == Some(decision_var) {
                        BddNode::mk_node(decision_var, new_high, new_low)
                    } else {
                        BddNode::mk_node(decision_var, new_low, new_high)
                    };
                    finished.insert(*on_stack, left.ensure_node(node));
                }
                stack.pop(); // Mark as resolved.
            } else {
                // Otherwise, if either value is unknown, push it to the stack.
                if flip_out_if == Some(decision_var) {
                    // If we are flipping output, we have to compute subtasks in the right order.
                    if new_high.is_none() {
                        stack.push(comp_high);
                    }
                    if new_low.is_none() {
                        stack.push(comp_low);
                    }
                } else {
                    if new_low.is_none() {
                        stack.push(comp_low);
                    }
                    if new_high.is_none() {
                        stack.push(comp_high);
                    }
                }
            }
        }
    }

    let new_root = finished.get(&root_task).unwrap().clone();
    left.finish_operation(new_root);
}

/// **(internal)** A simple utility method for checking bounds of a flip variable.
fn check_flip_bounds(num_vars: u16, var: Option<BddVariable>) {
    if let Some(BddVariable(var)) = var {
        if var >= num_vars {
            panic!(
                "Cannot flip variable {} in Bdd with {} variables.",
                var, num_vars
            );
        }
    }
}
