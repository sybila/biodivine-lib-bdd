use crate::_impl_bdd::Task;
use crate::{Bdd, BddNode, BddPointer, BddVariable};
use fxhash::FxBuildHasher;
use std::cmp::{max, min};
use std::collections::{HashMap, HashSet};

impl Bdd {
    /// Performs a logical operation (`op`) on two BDDs while performing a **universal projection**
    /// on the given `variables` in the result BDD.
    pub fn binary_op_with_for_all<F>(
        left: &Bdd,
        right: &Bdd,
        op: F,
        variables: &[BddVariable],
    ) -> Bdd
    where
        F: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    {
        let set: HashSet<BddVariable, FxBuildHasher> =
            HashSet::from_iter(variables.iter().copied());
        let trigger = |var: BddVariable| set.contains(&var);

        Bdd::binary_op_with_for_all_trigger(left, right, trigger, op)
    }

    /// Performs a logical operation (`op`) on two BDDs while performing a **universal projection**
    /// on the given `variables` in the result BDD.
    pub fn binary_op_with_for_all_trigger<F, Trigger>(
        left: &Bdd,
        right: &Bdd,
        trigger: Trigger,
        op: F,
    ) -> Bdd
    where
        Trigger: Fn(BddVariable) -> bool,
        F: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    {
        Bdd::binary_op_nested(left, right, trigger, op, crate::op_function::and)
    }

    /// Performs a logical operation (`op`) on two BDDs while performing an
    /// **existential projection** on the given `variables` in the result BDD.
    pub fn binary_op_with_exists<F>(
        left: &Bdd,
        right: &Bdd,
        op: F,
        variables: &[BddVariable],
    ) -> Bdd
    where
        F: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    {
        let set: HashSet<BddVariable, FxBuildHasher> =
            HashSet::from_iter(variables.iter().copied());
        let trigger = |var: BddVariable| set.contains(&var);

        Bdd::binary_op_with_exists_trigger(left, right, trigger, op)
    }

    /// Performs a logical operation (`op`) on two BDDs while performing an
    /// **existential projection** on the given `variables` in the result BDD.
    pub fn binary_op_with_exists_trigger<F, Trigger>(
        left: &Bdd,
        right: &Bdd,
        trigger: Trigger,
        op: F,
    ) -> Bdd
    where
        Trigger: Fn(BddVariable) -> bool,
        F: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    {
        Bdd::binary_op_nested(left, right, trigger, op, crate::op_function::or)
    }

    /// A "nested" apply function performs two "nested" passes of the apply algorithm:
    ///   - First, the `outer_op` is applied to combine the `left` and `right` BDDs.
    ///   - Then, for each node of the newly created BDD, the `trigger` function is executed and if
    ///     it returns true, the `inner_op` is applied to the two children of this node and the
    ///     result replaces the original node in the final BDD.
    ///
    /// This operation can be used to implement various combinations of logic + projection.
    /// Specifically, using `inner_op = or` implements existential projection and `inner_op = and`
    /// implements universal projection on the result of the "outer" operation. However, much
    /// "wilder" combinations are possible if you need them.
    pub fn binary_op_nested<F1, F2, Trigger>(
        left: &Bdd,
        right: &Bdd,
        trigger: Trigger,
        outer_op: F1,
        inner_op: F2,
    ) -> Bdd
    where
        F1: Fn(Option<bool>, Option<bool>) -> Option<bool>,
        F2: Fn(Option<bool>, Option<bool>) -> Option<bool>,
        Trigger: Fn(BddVariable) -> bool,
    {
        nested_apply(left, right, trigger, outer_op, inner_op)
    }
}

/// **(internal)** An "inner" apply algorithm works in the same way as standard apply algorithm,
/// but it operates on two nodes of the same BDD. It also creates the resulting nodes in this BDD.
///
/// Note that using this algorithm leaves the BDD in a "misaligned" state where the root pointer
/// is not necessarily the last node. As such, you have to "re-align" the BDD before returning
/// it to the user.
fn inner_apply<F>(
    bdd: &mut Bdd,
    left: BddPointer,
    right: BddPointer,
    node_cache: &mut HashMap<BddNode, BddPointer, FxBuildHasher>,
    task_cache: &mut HashMap<Task, BddPointer, FxBuildHasher>,
    op: F,
) -> BddPointer
where
    F: Fn(Option<bool>, Option<bool>) -> Option<bool>,
{
    // Every tasks saves its result here. The last task will thus give us the proper "result".
    let mut output: BddPointer = BddPointer::zero();

    let mut stack: Vec<Task> = Vec::with_capacity(usize::from(bdd.num_vars()));
    stack.push(Task { left, right });

    while let Some(on_stack) = stack.last() {
        if let Some(saved) = task_cache.get(on_stack) {
            output = *saved;
            stack.pop();
        } else {
            let (l, r) = (on_stack.left, on_stack.right);

            // Determine which variable we are conditioning on, moving from smallest to largest.
            let (l_v, r_v) = (bdd.var_of(l), bdd.var_of(r));
            let decision_var = min(l_v, r_v);

            // If the variable is the same as in the left/right decision node,
            // advance the exploration there. Otherwise, keep the pointers the same.
            let (l_low, l_high) = if l_v != decision_var {
                (l, l)
            } else {
                (bdd.low_link_of(l), bdd.high_link_of(l))
            };
            let (r_low, r_high) = if r_v != decision_var {
                (r, r)
            } else {
                (bdd.low_link_of(r), bdd.high_link_of(r))
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
            let new_low = op(l_low.as_bool(), r_low.as_bool())
                .map(BddPointer::from_bool)
                .or_else(|| task_cache.get(&comp_low).cloned());
            let new_high = op(l_high.as_bool(), r_high.as_bool())
                .map(BddPointer::from_bool)
                .or_else(|| task_cache.get(&comp_high).cloned());

            // If both values are computed, mark this task as resolved.
            if let (Some(new_low), Some(new_high)) = (new_low, new_high) {
                output = if new_low == new_high {
                    // There is no decision, just skip this node and point to either child.
                    task_cache.insert(*on_stack, new_low);
                    new_low
                } else {
                    // There is a decision here.
                    let node = BddNode::mk_node(decision_var, new_low, new_high);
                    if let Some(index) = node_cache.get(&node) {
                        // Node already exists, just make it a result of this computation.
                        task_cache.insert(*on_stack, *index);
                        *index
                    } else {
                        // Node does not exist, it needs to be created.
                        bdd.push_node(node);
                        let id = bdd.root_pointer();
                        node_cache.insert(node, id);
                        task_cache.insert(*on_stack, id);
                        id
                    }
                };
                stack.pop(); // Mark as resolved.
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

    output
}

/// **(internal)** Takes a misaligned BDD and the desired root pointer and re-creates the BDD in
/// a new array in the correct order.
///
/// The method assumes that the BDD is already "reduced". It only fixes the node post-order
/// and filters away any nodes that are not reachable from the new root.
fn fix_bdd_alignment(bdd: &Bdd, root: BddPointer) -> Bdd {
    if root.is_zero() {
        return Bdd::mk_false(bdd.num_vars());
    }
    if root.is_one() {
        return Bdd::mk_true(bdd.num_vars());
    }

    // The new BDD where only relevant nodes are re-created.
    let mut result = Bdd::mk_true(bdd.num_vars());

    // For each pointer of the *old* BDD stores the pointer to an equivalent node in the *new* BDD.
    let mut pointer_map: Vec<Option<BddPointer>> = vec![None; bdd.0.len()];
    pointer_map[0] = Some(BddPointer::zero());
    pointer_map[1] = Some(BddPointer::one());

    let mut stack = Vec::with_capacity(usize::from(bdd.num_vars()));
    stack.push(root);

    while let Some(top) = stack.last() {
        if pointer_map[top.to_index()].is_some() {
            // This node already has a known translation.
            // This can happen if we rediscovered the node further down in the DFS stack and processed it,
            // but it was already pushed on to the stack before by another parent higher in the BDD.
            stack.pop();
            continue;
        }
        let old_low = bdd.low_link_of(*top);
        let old_high = bdd.high_link_of(*top);

        let old_low_index = old_low.to_index();
        let old_high_index = old_high.to_index();
        let new_low: &Option<BddPointer> = &pointer_map[old_low_index];
        let new_high: &Option<BddPointer> = &pointer_map[old_high_index];

        if let (Some(new_low), Some(new_high)) = (new_low, new_high) {
            result.push_node(BddNode {
                var: bdd.var_of(*top),
                low_link: *new_low,
                high_link: *new_high,
            });
            pointer_map[top.to_index()] = Some(result.root_pointer());
            stack.pop();
        } else {
            if new_low.is_none() {
                stack.push(old_low);
            }
            if new_high.is_none() {
                stack.push(old_high);
            }
        }
    }

    result
}

/// **(internal)** See `Bdd::nested_apply`
fn nested_apply<F1, F2, Trigger>(
    left: &Bdd,
    right: &Bdd,
    trigger: Trigger,
    outer_op: F1,
    inner_op: F2,
) -> Bdd
where
    F1: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    F2: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    // TODO:
    //  In future implementations, we need a better API where we can actually give
    //  the user some other info about the BDD node. Now we can't because we don't have a notion
    //  of "BDD slice" and BDD pointers are private (and probably should stay that way).
    Trigger: Fn(BddVariable) -> bool,
{
    let num_vars = left.num_vars();
    if right.num_vars() != num_vars {
        panic!(
            "Var count mismatch: BDDs are not compatible. {} != {}",
            num_vars,
            right.num_vars()
        );
    }

    let mut result: Bdd = Bdd::mk_true(num_vars);

    // Every tasks saves its result here. The last task will thus give us the proper "result".
    let mut output: BddPointer = BddPointer::zero();

    // Every node in `result` is inserted into `node_cache` - this ensures we have no duplicates.
    let mut node_cache: HashMap<BddNode, BddPointer, FxBuildHasher> =
        HashMap::with_capacity_and_hasher(max(left.size(), right.size()), FxBuildHasher::default());
    node_cache.insert(BddNode::mk_zero(num_vars), BddPointer::zero());
    node_cache.insert(BddNode::mk_one(num_vars), BddPointer::one());

    // Outer cache tracks the task results for `op_outer` operating on the input BDDs.
    // Inner cache tracks the task results for `op_inner` operating on the result BDD.
    // Inner cache is shared across all invocations of the inner tasks because they all implement
    // the same BDD operation.
    let mut outer_cache: HashMap<Task, BddPointer, FxBuildHasher> =
        HashMap::with_capacity_and_hasher(max(left.size(), right.size()), FxBuildHasher::default());
    let mut inner_cache: HashMap<Task, BddPointer, FxBuildHasher> =
        HashMap::with_capacity_and_hasher(max(left.size(), right.size()), FxBuildHasher::default());

    // `stack` is used to explore the two BDDs "side by side" in DFS-like manner. Each task
    // on the stack is a pair of nodes that needs to be fully processed before we are finished.
    let mut outer_stack: Vec<Task> = Vec::with_capacity(max(left.size(), right.size()));
    outer_stack.push(Task {
        left: left.root_pointer(),
        right: right.root_pointer(),
    });

    while let Some(on_stack) = outer_stack.last() {
        if let Some(saved) = outer_cache.get(on_stack) {
            output = *saved;
            outer_stack.pop();
        } else {
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
            let new_low = outer_op(l_low.as_bool(), r_low.as_bool())
                .map(BddPointer::from_bool)
                .or_else(|| outer_cache.get(&comp_low).cloned());
            let new_high = outer_op(l_high.as_bool(), r_high.as_bool())
                .map(BddPointer::from_bool)
                .or_else(|| outer_cache.get(&comp_high).cloned());

            // If both values are computed, mark this task as resolved.
            if let (Some(new_low), Some(new_high)) = (new_low, new_high) {
                output = if new_low == new_high {
                    // There is no decision, just skip this node and point to either child.
                    outer_cache.insert(*on_stack, new_low);
                    new_low
                } else {
                    // There is a decision here. If the decision passes the `trigger`, we
                    // should merge the results using an inner task. Otherwise, create a normal node.
                    if trigger(decision_var) {
                        // Merge the two child nodes as an "inner task".
                        let inner_result = inner_apply(
                            &mut result,
                            new_low,
                            new_high,
                            &mut node_cache,
                            &mut inner_cache,
                            &inner_op,
                        );
                        outer_cache.insert(*on_stack, inner_result);
                        inner_result
                    } else {
                        let node = BddNode::mk_node(decision_var, new_low, new_high);
                        if let Some(index) = node_cache.get(&node) {
                            // Node already exists, just make it a result of this computation.
                            outer_cache.insert(*on_stack, *index);
                            *index
                        } else {
                            // Node does not exist, it needs to be pushed to result.
                            result.push_node(node);
                            let id = result.root_pointer();
                            node_cache.insert(node, id);
                            outer_cache.insert(*on_stack, id);
                            id
                        }
                    }
                };
                outer_stack.pop(); // Mark as resolved.
            } else {
                if new_low.is_none() {
                    outer_stack.push(comp_low);
                }
                if new_high.is_none() {
                    outer_stack.push(comp_high);
                }
            }
        }
    }

    // Finally, clean up the BDD.
    fix_bdd_alignment(&result, output)
}

#[cfg(test)]
mod tests {
    use crate::_impl_bdd::_impl_nested_ops::{fix_bdd_alignment, inner_apply};
    use crate::{Bdd, BddNode, BddPointer, BddVariable, BddVariableSet, bdd};
    use fxhash::FxBuildHasher;
    use std::collections::HashMap;

    #[test]
    fn test_bdd_alignment_fix() {
        let v1 = BddVariable(0);
        let v2 = BddVariable(1);
        let v3 = BddVariable(2);

        // Build a BDD for (v1 & !v2 & v3) with one extra node and a messed up ordering.
        let nodes = vec![
            BddNode::mk_zero(3),
            BddNode::mk_one(3),
            BddNode::mk_node(v1, BddPointer::zero(), BddPointer(3)),
            BddNode::mk_node(v2, BddPointer(4), BddPointer::zero()),
            BddNode::mk_node(v3, BddPointer::zero(), BddPointer::one()),
            BddNode::mk_node(v1, BddPointer::one(), BddPointer::zero()),
        ];
        let bdd = Bdd(nodes);
        let bdd = fix_bdd_alignment(&bdd, BddPointer(2));

        let expected_bdd = Bdd::mk_literal(3, v1, true);
        let expected_bdd = expected_bdd.and(&Bdd::mk_literal(3, v2, false));
        let expected_bdd = expected_bdd.and(&Bdd::mk_literal(3, v3, true));

        assert_eq!(bdd.0, expected_bdd.0);
    }

    #[test]
    fn test_bdd_alignment_fix_2() {
        // This reproduces a bug we had previously with bad DFS search routine in alignment fix.
        let v1 = BddVariable(0);
        let v2 = BddVariable(1);
        let v3 = BddVariable(2);
        let nodes = vec![
            BddNode::mk_zero(3),
            BddNode::mk_one(3),
            BddNode::mk_node(v1, BddPointer(4), BddPointer(3)),
            BddNode::mk_node(v2, BddPointer(4), BddPointer::one()),
            BddNode::mk_node(v3, BddPointer::zero(), BddPointer::one()),
        ];

        let bdd = Bdd(nodes);
        let bdd = fix_bdd_alignment(&bdd, BddPointer(2));

        assert_eq!(bdd.0, bdd.and(&Bdd::mk_true(3)).0);
    }

    #[test]
    fn test_inner_apply() {
        let set = BddVariableSet::new_anonymous(5);
        let bdd = bdd![set, (("x_0" & "x_1") | ("x_1" & "x_2")) | ("x_3" <=> "x_4")];
        assert!(bdd.size() > 3);

        let low = bdd.low_link_of(bdd.root_pointer());
        let high = bdd.high_link_of(bdd.root_pointer());

        let mut test_bdd = bdd.clone();
        // Technically this is not correct because inner_apply will expect the node cache to
        // already be populated. But in this case it will only result in the creation of extra
        // nodes and the test should still pass if everything is in order.
        let mut node_cache = HashMap::with_hasher(FxBuildHasher::default());
        let mut task_cache = HashMap::with_hasher(FxBuildHasher::default());
        // This should be the same as projection on the first variable.
        let new_root = inner_apply(
            &mut test_bdd,
            low,
            high,
            &mut node_cache,
            &mut task_cache,
            crate::op_function::or,
        );
        // But we need to re-align the BDD afterward.
        let test_bdd = fix_bdd_alignment(&test_bdd, new_root);

        let expected_bdd = bdd.var_exists(BddVariable(0));

        assert!(expected_bdd.size() > 3);
        assert_eq!(test_bdd.0, expected_bdd.0);
    }
}
