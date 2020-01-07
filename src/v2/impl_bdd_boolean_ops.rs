//! **(internal)** Implementation of basic logical operators for `Bdd`s using the `apply` function.

use super::*;
use std::cmp::min;

/// Basic boolean logical operations for `Bdd`s:
/// $\neg, \land, \lor, \Rightarrow, \Leftrightarrow, \oplus$.
impl Bdd {
    /// Create a `Bdd` corresponding to the $\neg \phi$ formula, where $\phi$ is this `Bdd`.
    pub fn not(&self) -> Bdd {
        if self.is_true() {
            return Bdd::mk_false(self.num_vars());
        } else if self.is_false() {
            return Bdd::mk_true(self.num_vars());
        } else {
            let mut result_vector = self.0.clone();
            for i in 2..result_vector.len() {
                // skip terminals
                result_vector[i].high_link.flip_if_terminal();
                result_vector[i].low_link.flip_if_terminal();
            }
            return Bdd(result_vector);
        }
    }

    /// Create a `Bdd` corresponding to the $\phi \land \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn and(&self, right: &Bdd) -> Bdd {
        return apply(self, right, |l, r| match (l, r) {
            (Some(true), Some(true)) => Some(true),
            (Some(false), _) => Some(false),
            (_, Some(false)) => Some(false),
            _ => None,
        });
    }

    /// Create a `Bdd` corresponding to the $\phi \lor \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn or(&self, right: &Bdd) -> Bdd {
        return apply(self, right, |l, r| match (l, r) {
            (Some(false), Some(false)) => Some(false),
            (Some(true), _) => Some(true),
            (_, Some(true)) => Some(true),
            _ => None,
        });
    }

    /// Create a `Bdd` corresponding to the $\phi \Rightarrow \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn imp(&self, right: &Bdd) -> Bdd {
        return apply(self, right, |l, r| match (l, r) {
            (Some(true), Some(false)) => Some(false),
            (Some(false), _) => Some(true),
            (_, Some(true)) => Some(true),
            _ => None,
        });
    }

    /// Create a `Bdd` corresponding to the $\phi \Leftrightarrow \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn iff(&self, right: &Bdd) -> Bdd {
        return apply(self, right, |l, r| match (l, r) {
            (Some(l), Some(r)) => Some(l == r),
            _ => None,
        });
    }

    /// Create a `Bdd` corresponding to the $\phi \oplus \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn xor(&self, right: &Bdd) -> Bdd {
        return apply(self, right, |l, r| match (l, r) {
            (Some(l), Some(r)) => Some(l ^ r),
            _ => None,
        });
    }
}

/// **(internal)** Universal function to implement standard logical operators.
///
/// The `terminal_lookup` function takes the two currently considered terminal BDD nodes (none
/// if the node is not terminal) and returns a boolean if these two nodes can be evaluated
/// by the function being implemented. For example, if one of the nodes is `false` and we are
/// implementing `and`, we can immediately evaluate to `false`.
fn apply<T>(left: &Bdd, right: &Bdd, terminal_lookup: T) -> Bdd
where
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
    // Result holds the new BDD we are computing. Initially, `0` and `1` nodes are present. We
    // remember if the result is `false` or not (`is_not_empty`). If it is, we just provide
    // a `false` BDD instead of the result. This is easier than explicitly adding `1` later.
    let mut result: Bdd = Bdd::mk_true(num_vars);
    let mut is_not_empty = false;

    // Every node in `result` is inserted into `existing` - this ensures we have no duplicates.
    let mut existing: HashMap<BddNode, BddPointer> = HashMap::new();
    existing.insert(BddNode::mk_zero(num_vars), BddPointer::zero());
    existing.insert(BddNode::mk_one(num_vars), BddPointer::one());

    // Task is a pair of pointers into the `left` and `right` BDDs.
    #[derive(Eq, PartialEq, Hash, Copy, Clone)]
    struct Task {
        left: BddPointer,
        right: BddPointer,
    };

    // `stack` is used to explore the two BDDs "side by side" in DFS-like manner. Each task
    // on the stack is a pair of nodes that needs to be fully processed before we are finished.
    let mut stack: Vec<Task> = Vec::new();
    stack.push(Task {
        left: left.root_pointer(),
        right: right.root_pointer(),
    });

    // `finished` is a memoization cache of tasks which are already completed, since the same
    // combination of nodes can be often explored multiple times.
    let mut finished: HashMap<Task, BddPointer> = HashMap::new();

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
            } else {
                (left.low_link_of(l), left.high_link_of(l))
            };
            let (r_low, r_high) = if r_v != decision_var {
                (r, r)
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
                if new_low.is_one() || new_high.is_one() {
                    is_not_empty = true
                }

                if new_low == new_high {
                    // There is no decision, just skip this node and point to either child.
                    finished.insert(*on_stack, new_low);
                } else {
                    // There is a decision here.
                    let node = BddNode::mk_node(decision_var, new_low, new_high);
                    if let Some(index) = existing.get(&node) {
                        // Node already exists, just make it a result of this computation.
                        finished.insert(*on_stack, *index);
                    } else {
                        // Node does not exist, it needs to be pushed to result.
                        result.push_node(node);
                        existing.insert(node, result.root_pointer());
                        finished.insert(*on_stack, result.root_pointer());
                    }
                }
                stack.pop(); // Mark as resolved.
            } else {
                // Otherwise, if either value is unknown, push it to the stack.
                if new_low.is_none() {
                    stack.push(comp_low);
                }
                if new_high.is_none() {
                    stack.push(comp_high);
                }
            }
        }
    }

    return if is_not_empty {
        result
    } else {
        Bdd::mk_false(num_vars)
    };
}
