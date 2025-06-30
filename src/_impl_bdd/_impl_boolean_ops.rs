use crate::_impl_bdd::Task;
use crate::*;
use fxhash::FxBuildHasher;
use std::cmp::{max, min};

/// Basic boolean logical operations for `Bdd`s:
/// $\neg, \land, \lor, \Rightarrow, \Leftrightarrow, \oplus$.
impl Bdd {
    /// Create a `Bdd` corresponding to the $\neg \phi$ formula, where $\phi$ is this `Bdd`.
    pub fn not(&self) -> Bdd {
        if self.is_true() {
            Bdd::mk_false(self.num_vars())
        } else if self.is_false() {
            Bdd::mk_true(self.num_vars())
        } else {
            // Note that this does not break DFS order of the graph because
            // we are only flipping terminals, which already have special positions.
            let mut result_vector = self.0.clone();
            for node in result_vector.iter_mut().skip(2) {
                // skip terminals
                node.high_link.flip_if_terminal();
                node.low_link.flip_if_terminal();
            }
            Bdd(result_vector)
        }
    }

    /// Create a `Bdd` corresponding to the $\phi \land \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn and(&self, right: &Bdd) -> Bdd {
        apply(self, right, op_function::and)
    }

    /// Create a `Bdd` corresponding to the $\phi \lor \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn or(&self, right: &Bdd) -> Bdd {
        apply(self, right, op_function::or)
    }

    /// Create a `Bdd` corresponding to the $\phi \Rightarrow \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn imp(&self, right: &Bdd) -> Bdd {
        apply(self, right, op_function::imp)
    }

    /// Create a `Bdd` corresponding to the $\phi \Leftrightarrow \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn iff(&self, right: &Bdd) -> Bdd {
        apply(self, right, op_function::iff)
    }

    /// Create a `Bdd` corresponding to the $\phi \oplus \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn xor(&self, right: &Bdd) -> Bdd {
        apply(self, right, op_function::xor)
    }

    /// Create a `Bdd` corresponding to the $\phi \land \neg \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn and_not(&self, right: &Bdd) -> Bdd {
        apply(self, right, op_function::and_not)
    }

    /// A standard "if-then-else" ternary operation. It is equivalent to
    /// $(a \land b) \lor (\neg a \land c)$.
    ///
    /// Additional non-standard ternary operators are available through `Bdd::ternary_op`.
    pub fn if_then_else(a: &Bdd, b: &Bdd, c: &Bdd) -> Bdd {
        fn ite_function(a: Option<bool>, b: Option<bool>, c: Option<bool>) -> Option<bool> {
            match (a, b, c) {
                // If "a" is known, we can just "implement" ITE and return "b"/"c".
                (Some(true), _, _) => b,
                (Some(false), _, _) => c,
                // The next two cases are not strictly necessary, but
                // can cause the operation to finish sooner if the result
                // is already determined, even when "a" is still unknown.
                (None, Some(false), Some(false)) => Some(false),
                (None, Some(true), Some(true)) => Some(true),
                // Otherwise, we return None until "a" is known.
                (None, _, _) => None,
            }
        }
        Bdd::ternary_op(a, b, c, ite_function)
    }

    /// Apply a general binary operation to two given `Bdd` objects.
    ///
    /// The `op_function` specifies the actual logical operation that will be performed. See
    /// `crate::op_function` module for examples.
    ///
    /// In general, this function can be used to slightly speed up less common Boolean operations
    /// or to fuse together several operations (like negation and binary operation).
    pub fn binary_op<T>(left: &Bdd, right: &Bdd, op_function: T) -> Bdd
    where
        T: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    {
        apply(left, right, op_function)
    }

    /// Same as `binary_op`, but the result of the operation is `None` if the size of the `Bdd`
    /// exceeds the given `limit`.
    pub fn binary_op_with_limit<T>(
        limit: usize,
        left: &Bdd,
        right: &Bdd,
        op_function: T,
    ) -> Option<Bdd>
    where
        T: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    {
        apply_with_flip_and_limit(limit, left, right, None, None, None, op_function)
    }

    /// Apply a general binary operation together with up-to three Bdd variable flips. See also `binary_op`.
    ///
    /// A flip exchanges the edges of all decision nodes with the specified variable `x`.
    /// As a result, the set of bitvectors represented by this Bdd has the value of `x` negated.
    ///
    /// With this operation, you can apply such flip to both input operands and the output
    /// Bdd. This can greatly simplify implementation of state space generators for asynchronous
    /// systems.
    pub fn fused_binary_flip_op<T>(
        left: (&Bdd, Option<BddVariable>),
        right: (&Bdd, Option<BddVariable>),
        flip_output: Option<BddVariable>,
        op_function: T,
    ) -> Bdd
    where
        T: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    {
        apply_with_flip(left.0, right.0, left.1, right.1, flip_output, op_function)
    }

    /// Same as `Self::fused_binary_flip_op`, but the result of the operation is `None` if the
    /// size of the `Bdd` exceeds the given `limit`.
    pub fn fused_binary_flip_op_with_limit<T>(
        limit: usize,
        left: (&Bdd, Option<BddVariable>),
        right: (&Bdd, Option<BddVariable>),
        flip_output: Option<BddVariable>,
        op_function: T,
    ) -> Option<Bdd>
    where
        T: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    {
        apply_with_flip_and_limit(
            limit,
            left.0,
            right.0,
            left.1,
            right.1,
            flip_output,
            op_function,
        )
    }

    /// Performs a "dry run" of the supplied operation. This computes two useful results:
    ///
    /// 1. A true value indicating that the resulting BDD will *not* be "empty" (i.e.
    ///    not a contradiction).
    ///
    /// 2. A number of low-level BDD tasks that need to be completed to resolve the
    ///    operation.
    ///
    /// You can also limit the enumeration up to a specific number of tasks using the `limit`
    /// parameter. If this limit is exceeded, the result is `None`. Note that this `limit`
    /// parameter does not correspond to the number of nodes in the (hypothetical)
    /// resulting `Bdd`, but rather the number of steps needed to create it.
    ///
    /// Generally, the method requires much less space and time than `binary_op`, but does not
    /// produce the actual BDD. As such, it is useful for operations where the result would be
    /// likely discarded anyway, like subset checks or size comparisons.
    ///
    /// Nevertheless, note that the number of low-level task is *not* the size of the resulting
    /// BDD (it is an upper bound on its size though).
    pub fn check_binary_op<T>(
        limit: usize,
        left: &Bdd,
        right: &Bdd,
        op_function: T,
    ) -> Option<(bool, usize)>
    where
        T: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    {
        estimated_apply_complexity(limit, left, right, None, None, None, op_function)
    }

    /// The same as `Bdd::check_binary_op`, but it takes into account variable flips.
    pub fn check_fused_binary_flip_op<T>(
        limit: usize,
        left: (&Bdd, Option<BddVariable>),
        right: (&Bdd, Option<BddVariable>),
        flip_output: Option<BddVariable>,
        op_function: T,
    ) -> Option<(bool, usize)>
    where
        T: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    {
        estimated_apply_complexity(
            limit,
            left.0,
            right.0,
            left.1,
            right.1,
            flip_output,
            op_function,
        )
    }
}

/// **(internal)** Shorthand for the more advanced apply which includes variable flipping
fn apply<T>(left: &Bdd, right: &Bdd, terminal_lookup: T) -> Bdd
where
    T: Fn(Option<bool>, Option<bool>) -> Option<bool>,
{
    apply_with_flip(left, right, None, None, None, terminal_lookup)
}

/// **(internal)** Universal function to implement standard logical operators.
///
/// The `terminal_lookup` function takes the two currently considered terminal BDD nodes (none
/// if the node is not terminal) and returns a boolean if these two nodes can be evaluated
/// by the function being implemented. For example, if one of the nodes is `false` and we are
/// implementing `and`, we can immediately evaluate to `false`.
///
/// Additionally, you can provide `flip_left_if`, `flip_right_if` and `flip_out_if` `BddVariables`
/// which will, given the corresponding node has the given decision variable, flip the low/high
/// link of the node. This is used to implement faster state-space generators for asynchronous
/// systems.
///
/// The reason why we allow this behaviour in apply, is that flipping the pointers in a BDD is cheap,
/// but breaks the DFS order, which may result in unexpected behaviour. Furthermore, since the
/// function is generic, in most performance intensive paths, it should be optimized anyway.
fn apply_with_flip<T>(
    left: &Bdd,
    right: &Bdd,
    flip_left_if: Option<BddVariable>,
    flip_right_if: Option<BddVariable>,
    flip_out_if: Option<BddVariable>,
    terminal_lookup: T,
) -> Bdd
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
    check_flip_bounds(num_vars, flip_left_if);
    check_flip_bounds(num_vars, flip_right_if);
    check_flip_bounds(num_vars, flip_out_if);
    // Result holds the new BDD we are computing. Initially, `0` and `1` nodes are present. We
    // remember if the result is `false` or not (`is_not_empty`). If it is, we just provide
    // a `false` BDD instead of the result. This is easier than explicitly adding `1` later.
    let mut result: Bdd = Bdd::mk_true(num_vars);
    let mut is_not_empty = false;

    // Every node in `result` is inserted into `existing` - this ensures we have no duplicates.
    let mut existing: HashMap<BddNode, BddPointer, FxBuildHasher> =
        HashMap::with_capacity_and_hasher(max(left.size(), right.size()), FxBuildHasher::default());
    existing.insert(BddNode::mk_zero(num_vars), BddPointer::zero());
    existing.insert(BddNode::mk_one(num_vars), BddPointer::one());

    // `stack` is used to explore the two BDDs "side by side" in DFS-like manner. Each task
    // on the stack is a pair of nodes that needs to be fully processed before we are finished.
    let mut stack: Vec<Task> = Vec::with_capacity(max(left.size(), right.size()));
    stack.push(Task {
        left: left.root_pointer(),
        right: right.root_pointer(),
    });

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
            panic!("Cannot flip variable {var} in Bdd with {num_vars} variables.");
        }
    }
}

/// Compute the expected number of BDD operations that needs to be performed during a binary
/// BDD operation. At the same time, we also check if the result is empty.
fn estimated_apply_complexity<T>(
    limit: usize,
    left: &Bdd,
    right: &Bdd,
    flip_left_if: Option<BddVariable>,
    flip_right_if: Option<BddVariable>,
    flip_out_if: Option<BddVariable>,
    terminal_lookup: T,
) -> Option<(bool, usize)>
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
    check_flip_bounds(num_vars, flip_left_if);
    check_flip_bounds(num_vars, flip_right_if);
    check_flip_bounds(num_vars, flip_out_if);

    let mut is_not_empty = false;

    // `stack` is used to explore the two BDDs "side by side" in DFS-like manner. Each task
    // on the stack is a pair of nodes that needs to be fully processed before we are finished.
    let mut stack: Vec<Task> = Vec::with_capacity(max(left.size(), right.size()));
    stack.push(Task {
        left: left.root_pointer(),
        right: right.root_pointer(),
    });

    // `finished` is a memoization cache of tasks which are already completed, since the same
    // combination of nodes can be often explored multiple times.
    let mut finished: HashSet<Task, FxBuildHasher> =
        HashSet::with_capacity_and_hasher(max(left.size(), right.size()), FxBuildHasher::default());

    while let Some(on_stack) = stack.pop() {
        let lookup = terminal_lookup(on_stack.left.as_bool(), on_stack.right.as_bool());
        if lookup.is_some() {
            // Terminal task, just check for emptiness and continue.
            is_not_empty = is_not_empty || (lookup == Some(true));
            continue;
        } else if finished.contains(&on_stack) {
            // This task was already visited... continue.
            continue;
        } else {
            // Otherwise, add task to cache and expand it.

            // Mark the task as finished. We don't need to re-visit tasks in this method (as is
            // the case for normal binary operations).
            finished.insert(on_stack);
            if finished.len() > limit {
                // If limit is exceeded, return.
                return None;
            }

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

            if flip_out_if == Some(decision_var) {
                // If we are flipping output, we have to compute subtasks in the right order.
                stack.push(comp_high);
                stack.push(comp_low);
            } else {
                stack.push(comp_low);
                stack.push(comp_high);
            }
        }
    }

    Some((is_not_empty, finished.len()))
}

/// Extends the normal apply operation with the option to return `None` once the result size
/// exceeds the given `limit`.
///
/// This is a new method because adding the `limit` parameter to existing methods could
/// break some existing APIs (and performance metrics).
fn apply_with_flip_and_limit<T>(
    limit: usize,
    left: &Bdd,
    right: &Bdd,
    flip_left_if: Option<BddVariable>,
    flip_right_if: Option<BddVariable>,
    flip_out_if: Option<BddVariable>,
    terminal_lookup: T,
) -> Option<Bdd>
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
    check_flip_bounds(num_vars, flip_left_if);
    check_flip_bounds(num_vars, flip_right_if);
    check_flip_bounds(num_vars, flip_out_if);

    // Nothing can be done with limit zero.
    if limit == 0 {
        return None;
    }

    // Result holds the new BDD we are computing. Initially, `0` and `1` nodes are present. We
    // remember if the result is `false` or not (`is_not_empty`). If it is, we just provide
    // a `false` BDD instead of the result. This is easier than explicitly adding `1` later.
    let mut result: Bdd = Bdd::mk_true(num_vars);
    let mut is_not_empty = false;

    // Every node in `result` is inserted into `existing` - this ensures we have no duplicates.
    let mut existing: HashMap<BddNode, BddPointer, FxBuildHasher> =
        HashMap::with_capacity_and_hasher(max(left.size(), right.size()), FxBuildHasher::default());
    existing.insert(BddNode::mk_zero(num_vars), BddPointer::zero());
    existing.insert(BddNode::mk_one(num_vars), BddPointer::one());

    // `stack` is used to explore the two BDDs "side by side" in DFS-like manner. Each task
    // on the stack is a pair of nodes that needs to be fully processed before we are finished.
    let mut stack: Vec<Task> = Vec::with_capacity(max(left.size(), right.size()));
    stack.push(Task {
        left: left.root_pointer(),
        right: right.root_pointer(),
    });

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
                        if result.size() > limit {
                            return None;
                        }
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
        if result.size() > limit {
            // This resolves the edge case when limit is one, but the BDD has two nodes
            // (this is not handled by the main loop, as there the condition is checked
            // only when a new node is created, which won't happen for a `true` BDD)
            None
        } else {
            Some(result)
        }
    } else {
        // Here, we know that limit >= 1, so this is ok.
        Some(Bdd::mk_false(num_vars))
    }
}
