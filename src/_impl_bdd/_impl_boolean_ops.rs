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
        apply(self, right, crate::op_function::and)
    }

    /// Create a `Bdd` corresponding to the $\phi \lor \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn or(&self, right: &Bdd) -> Bdd {
        apply(self, right, crate::op_function::or)
    }

    /// Create a `Bdd` corresponding to the $\phi \Rightarrow \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn imp(&self, right: &Bdd) -> Bdd {
        apply(self, right, crate::op_function::imp)
    }

    /// Create a `Bdd` corresponding to the $\phi \Leftrightarrow \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn iff(&self, right: &Bdd) -> Bdd {
        apply(self, right, crate::op_function::iff)
    }

    /// Create a `Bdd` corresponding to the $\phi \oplus \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn xor(&self, right: &Bdd) -> Bdd {
        apply(self, right, crate::op_function::xor)
    }

    /// Create a `Bdd` corresponding to the $\phi \land \neg \psi$ formula, where $\phi$ and $\psi$
    /// are the two given `Bdd`s.
    pub fn and_not(&self, right: &Bdd) -> Bdd {
        apply(self, right, crate::op_function::and_not)
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

    /// Apply a general binary operation together with up-to three Bdd variable flips. See also `binary_op`.
    ///
    /// A flip exchanges the edges of all decision nodes with the specified variable `x`.
    /// As a result, the set of bitvectors represented by this Bdd has the value of `x` negated.
    ///
    /// With this operation, you can apply such flip to both input operands as well as the output
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

    // Task is a pair of pointers into the `left` and `right` BDDs.
    #[derive(Eq, PartialEq, Hash, Copy, Clone)]
    struct Task {
        left: BddPointer,
        right: BddPointer,
    }

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
            panic!(
                "Cannot flip variable {} in Bdd with {} variables.",
                var, num_vars
            );
        }
    }
}
