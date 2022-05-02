use crate::{Bdd, BddNode, BddPointer, BddVariable};
use fxhash::FxBuildHasher;
use std::cmp::{max, min};
use std::collections::HashMap;

impl Bdd {
    pub fn ternary_op<T>(a: &Bdd, b: &Bdd, c: &Bdd, op_function: T) -> Bdd
    where
        T: Fn(Option<bool>, Option<bool>, Option<bool>) -> Option<bool>,
    {
        ternary_apply(a, b, c, None, None, None, None, op_function)
    }

    pub fn fused_ternary_op<T>(
        a: (&Bdd, Option<BddVariable>),
        b: (&Bdd, Option<BddVariable>),
        c: (&Bdd, Option<BddVariable>),
        flip_output: Option<BddVariable>,
        op_function: T,
    ) -> Bdd
    where
        T: Fn(Option<bool>, Option<bool>, Option<bool>) -> Option<bool>,
    {
        ternary_apply(a.0, b.0, c.0, a.1, b.1, c.1, flip_output, op_function)
    }
}

fn ternary_apply<T>(
    a: &Bdd,
    b: &Bdd,
    c: &Bdd,
    flip_a_if: Option<BddVariable>,
    flip_b_if: Option<BddVariable>,
    flip_c_if: Option<BddVariable>,
    flip_out_if: Option<BddVariable>,
    terminal_lookup: T,
) -> Bdd
where
    T: Fn(Option<bool>, Option<bool>, Option<bool>) -> Option<bool>,
{
    let num_vars = a.num_vars();
    if a.num_vars() != b.num_vars() || b.num_vars() != c.num_vars() {
        panic!(
            "Var count mismatch: BDDs are not compatible. {} vs. {} vs. {}",
            a.num_vars(),
            b.num_vars(),
            c.num_vars()
        );
    }
    check_flip_bounds(num_vars, flip_a_if);
    check_flip_bounds(num_vars, flip_b_if);
    check_flip_bounds(num_vars, flip_c_if);
    check_flip_bounds(num_vars, flip_out_if);

    // Result holds the new BDD we are computing. Initially, `0` and `1` nodes are present. We
    // remember if the result is `false` or not (`is_not_empty`). If it is, we just provide
    // a `false` BDD instead of the result. This is easier than explicitly adding `1` later.
    let mut result: Bdd = Bdd::mk_true(num_vars);
    let mut is_not_empty = false;

    // Every node in `result` is inserted into `existing` - this ensures we have no duplicates.
    let expected_capacity = max(a.size(), max(b.size(), c.size()));
    let mut existing: HashMap<BddNode, BddPointer, FxBuildHasher> =
        HashMap::with_capacity_and_hasher(expected_capacity, FxBuildHasher::default());
    existing.insert(BddNode::mk_zero(num_vars), BddPointer::zero());
    existing.insert(BddNode::mk_one(num_vars), BddPointer::one());

    // Task is a triple of pointers into the `a`, `b`, and `c` BDDs.
    #[derive(Eq, PartialEq, Hash, Copy, Clone)]
    struct Task {
        a: BddPointer,
        b: BddPointer,
        c: BddPointer,
    }

    // `stack` is used to explore the BDDs "side by side" in DFS-like manner. Each task
    // on the stack is a triple of nodes that needs to be fully processed before we are finished.
    let mut stack: Vec<Task> = Vec::with_capacity(2 * usize::from(num_vars));
    stack.push(Task {
        a: a.root_pointer(),
        b: b.root_pointer(),
        c: c.root_pointer(),
    });

    // `finished` is a memoization cache of tasks that are already completed, since the same
    // combination of nodes can be often explored multiple times.
    let mut finished: HashMap<Task, BddPointer, FxBuildHasher> =
        HashMap::with_capacity_and_hasher(expected_capacity, FxBuildHasher::default());

    while let Some(on_stack) = stack.last() {
        if finished.contains_key(on_stack) {
            // skip finished tasks
            stack.pop();
        } else {
            let (p_a, p_b, p_c) = (on_stack.a, on_stack.b, on_stack.c);

            // Determine which variable we are conditioning on, moving from smallest to largest.
            let (v_a, v_b, v_c) = (a.var_of(p_a), b.var_of(p_b), c.var_of(p_c));
            let decision_var = min(v_a, min(v_b, v_c));

            // If the variable is the same as in the left/right decision node,
            // advance the exploration there. Otherwise, keep the pointers the same.
            let (low_a, high_a) = if v_a != decision_var {
                (p_a, p_a)
            } else if Some(v_a) == flip_a_if {
                (a.high_link_of(p_a), a.low_link_of(p_a))
            } else {
                (a.low_link_of(p_a), a.high_link_of(p_a))
            };

            let (low_b, high_b) = if v_b != decision_var {
                (p_b, p_b)
            } else if Some(v_b) == flip_b_if {
                (b.high_link_of(p_b), b.low_link_of(p_b))
            } else {
                (b.low_link_of(p_b), b.high_link_of(p_b))
            };

            let (low_c, high_c) = if v_c != decision_var {
                (p_c, p_c)
            } else if Some(v_c) == flip_c_if {
                (c.high_link_of(p_c), c.low_link_of(p_c))
            } else {
                (c.low_link_of(p_c), c.high_link_of(p_c))
            };

            // Two tasks which correspond to the two recursive sub-problems we need to solve.
            let comp_low = Task {
                a: low_a,
                b: low_b,
                c: low_c,
            };
            let comp_high = Task {
                a: high_a,
                b: high_b,
                c: high_c,
            };

            // Try to solve the tasks using terminal lookup table or from cache.
            let new_low = terminal_lookup(low_a.as_bool(), low_b.as_bool(), low_c.as_bool())
                .map(BddPointer::from_bool)
                .or_else(|| finished.get(&comp_low).cloned());
            let new_high = terminal_lookup(high_a.as_bool(), high_b.as_bool(), high_c.as_bool())
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
                    let node = if flip_out_if == Some(decision_var) {
                        BddNode::mk_node(decision_var, new_high, new_low)
                    } else {
                        BddNode::mk_node(decision_var, new_low, new_high)
                    };
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

    if is_not_empty {
        result
    } else {
        Bdd::mk_false(num_vars)
    }
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
