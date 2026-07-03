use crate::_impl_bdd::_impl_nested_ops::fix_bdd_alignment;
use crate::*;
use std::cmp::min;

/// A pair of BDD pointers representing one apply task `(f, g)`.
///
/// `Ord` is derived: lexicographic on `(left, right)`, same order as sorting by `BddPointer`
/// fields individually.
#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Debug)]
struct Task {
    left: BddPointer,
    right: BddPointer,
}

/// A child of an apply task: either a resolved terminal or a pending sub-task.
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
enum Child {
    Terminal(bool),
    Pair(Task),
}

/// Basic boolean logical operations for `Bdd`s using a BFS/level-by-level apply algorithm.
impl Bdd {
    /// Create a `Bdd` corresponding to the `f & g` formula using a BFS-based apply algorithm.
    ///
    /// This is an alternative to [`Bdd::and`] intended for experimentation with GPU-friendly
    /// bulk operations (sort, unique, scan). It should produce the same result as [`Bdd::and`].
    pub fn and_bfs(&self, right: &Bdd) -> Bdd {
        Self::binary_op_bfs(self, right, op_function::and)
    }

    /// Create a `Bdd` corresponding to the `f | g` formula using a BFS-based apply algorithm.
    ///
    /// This is an alternative to [`Bdd::or`]. It should produce the same result as [`Bdd::or`].
    pub fn or_bfs(&self, right: &Bdd) -> Bdd {
        Self::binary_op_bfs(self, right, op_function::or)
    }

    /// Create a `Bdd` corresponding to the `f => g` formula using a BFS-based apply algorithm.
    ///
    /// This is an alternative to [`Bdd::imp`]. It should produce the same result as [`Bdd::imp`].
    pub fn imp_bfs(&self, right: &Bdd) -> Bdd {
        Self::binary_op_bfs(self, right, op_function::imp)
    }

    /// Create a `Bdd` corresponding to the `f <=> g` formula using a BFS-based apply algorithm.
    ///
    /// This is an alternative to [`Bdd::iff`]. It should produce the same result as [`Bdd::iff`].
    pub fn iff_bfs(&self, right: &Bdd) -> Bdd {
        Self::binary_op_bfs(self, right, op_function::iff)
    }

    /// Create a `Bdd` corresponding to the `f ^ g` formula using a BFS-based apply algorithm.
    ///
    /// This is an alternative to [`Bdd::xor`]. It should produce the same result as [`Bdd::xor`].
    pub fn xor_bfs(&self, right: &Bdd) -> Bdd {
        Self::binary_op_bfs(self, right, op_function::xor)
    }

    /// Create a `Bdd` corresponding to the `f & !g` formula using a BFS-based apply algorithm.
    ///
    /// This is an alternative to [`Bdd::and_not`]. It should produce the same result as
    /// [`Bdd::and_not`].
    pub fn and_not_bfs(&self, right: &Bdd) -> Bdd {
        Self::binary_op_bfs(self, right, op_function::and_not)
    }

    /// Apply a general binary operation to two given `Bdd` objects using a BFS-based apply
    /// algorithm.
    ///
    /// The `op_function` specifies the actual logical operation that will be performed. See
    /// the [`crate::op_function`] module for examples. This is the BFS counterpart of
    /// [`Bdd::binary_op`].
    pub fn binary_op_bfs<T>(left: &Bdd, right: &Bdd, op_function: T) -> Bdd
    where
        T: Fn(Option<bool>, Option<bool>) -> Option<bool>,
    {
        apply_bfs(left, right, op_function)
    }
}

/// **(internal)** BFS level-by-level binary apply.
fn apply_bfs<T>(left: &Bdd, right: &Bdd, terminal_lookup: T) -> Bdd
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

    let root_task = Task {
        left: left.root_pointer(),
        right: right.root_pointer(),
    };

    if let Some(value) = terminal_lookup(root_task.left.as_bool(), root_task.right.as_bool()) {
        return if value {
            Bdd::mk_true(num_vars)
        } else {
            Bdd::mk_false(num_vars)
        };
    }

    let root_level = decision_var(left, right, root_task);
    let num_vars_usize = num_vars as usize;

    let mut pending: Vec<Vec<Task>> = vec![Vec::new(); num_vars_usize];
    pending[root_level.to_index()].push(root_task);

    let mut unique: Vec<Vec<Task>> = vec![Vec::new(); num_vars_usize];
    let mut children: Vec<Vec<(Child, Child)>> = vec![Vec::new(); num_vars_usize];

    // Phase 1: Top-down expansion (replaces memoization table).
    for v in 0..num_vars_usize {
        if pending[v].is_empty() {
            continue;
        }

        pending[v].sort_unstable();
        pending[v].dedup();
        unique[v] = std::mem::take(&mut pending[v]);

        let var = BddVariable(v as u16);
        for task in &unique[v] {
            let (f_low, f_high) = cofactor(left, task.left, var);
            let (g_low, g_high) = cofactor(right, task.right, var);

            let low_task = Task {
                left: f_low,
                right: g_low,
            };
            let high_task = Task {
                left: f_high,
                right: g_high,
            };

            let low_child =
                expand_child(left, right, low_task, var, &terminal_lookup, &mut pending);
            let high_child =
                expand_child(left, right, high_task, var, &terminal_lookup, &mut pending);
            children[v].push((low_child, high_child));
        }
    }

    // Phase 2: Bottom-up reduce (replaces unique table).
    let mut result = Bdd::mk_true(num_vars);
    let mut result_ids: Vec<Vec<BddPointer>> = vec![Vec::new(); num_vars_usize];
    let mut is_not_empty = false;

    for v in (0..num_vars_usize).rev() {
        if unique[v].is_empty() {
            continue;
        }

        result_ids[v] = vec![BddPointer::zero(); unique[v].len()];
        let mut to_materialize: Vec<(usize, BddPointer, BddPointer)> = Vec::new();

        for (k, task_children) in children[v].iter().enumerate() {
            let low_id = resolve_child(left, right, task_children.0, &unique, &result_ids);
            let high_id = resolve_child(left, right, task_children.1, &unique, &result_ids);

            if low_id.is_one() || high_id.is_one() {
                is_not_empty = true;
            }

            if low_id == high_id {
                result_ids[v][k] = low_id;
            } else {
                to_materialize.push((k, low_id, high_id));
            }
        }

        to_materialize
            .sort_unstable_by(|a, b| (a.1, a.2).cmp(&(b.1, b.2)).then_with(|| a.0.cmp(&b.0)));

        let mut i = 0;
        while i < to_materialize.len() {
            let (_k, low_id, high_id) = to_materialize[i];
            let mut j = i + 1;
            while j < to_materialize.len()
                && to_materialize[j].1 == low_id
                && to_materialize[j].2 == high_id
            {
                j += 1;
            }

            let node = BddNode::mk_node(BddVariable(v as u16), low_id, high_id);
            result.push_node(node);
            let new_id = result.root_pointer();

            for entry in &to_materialize[i..j] {
                result_ids[v][entry.0] = new_id;
            }

            i = j;
        }
    }

    if !is_not_empty {
        return Bdd::mk_false(num_vars);
    }

    let root_idx = unique[root_level.to_index()]
        .binary_search(&root_task)
        .expect("Root task must exist at root level.");
    let root_id = result_ids[root_level.to_index()][root_idx];

    if root_id.is_zero() {
        Bdd::mk_false(num_vars)
    } else if root_id.is_one() {
        Bdd::mk_true(num_vars)
    } else {
        fix_bdd_alignment(&result, root_id)
    }
}

fn expand_child<T>(
    left: &Bdd,
    right: &Bdd,
    task: Task,
    current_var: BddVariable,
    terminal_lookup: &T,
    pending: &mut [Vec<Task>],
) -> Child
where
    T: Fn(Option<bool>, Option<bool>) -> Option<bool>,
{
    if let Some(value) = terminal_lookup(task.left.as_bool(), task.right.as_bool()) {
        Child::Terminal(value)
    } else {
        let level = decision_var(left, right, task);
        debug_assert!(level > current_var);
        pending[level.to_index()].push(task);
        Child::Pair(task)
    }
}

fn resolve_child(
    left: &Bdd,
    right: &Bdd,
    child: Child,
    unique: &[Vec<Task>],
    result_ids: &[Vec<BddPointer>],
) -> BddPointer {
    match child {
        Child::Terminal(value) => BddPointer::from_bool(value),
        Child::Pair(task) => {
            let level = decision_var(left, right, task);
            let idx = unique[level.to_index()]
                .binary_search(&task)
                .expect("Child task must exist at its decision level.");
            result_ids[level.to_index()][idx]
        }
    }
}

/// Decision variable for a task: smallest variable among the two operands.
fn decision_var(left: &Bdd, right: &Bdd, task: Task) -> BddVariable {
    min(left.var_of(task.left), right.var_of(task.right))
}

/// Cofactor a pointer on variable `var`: follow low/high links if the node tests on `var`.
fn cofactor(bdd: &Bdd, pointer: BddPointer, var: BddVariable) -> (BddPointer, BddPointer) {
    if bdd.var_of(pointer) != var {
        (pointer, pointer)
    } else {
        (bdd.low_link_of(pointer), bdd.high_link_of(pointer))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::_test_util::mk_small_test_bdd;
    use rand::prelude::StdRng;
    use rand::{RngCore, SeedableRng};

    fn assert_bfs_matches_dfs(
        left: &Bdd,
        right: &Bdd,
        op: fn(Option<bool>, Option<bool>) -> Option<bool>,
    ) {
        let dfs = Bdd::binary_op(left, right, op);
        let bfs = Bdd::binary_op_bfs(left, right, op);
        assert_eq!(bfs, dfs, "Structural mismatch.");
        assert!(bfs.iff(&dfs).is_true());
        assert!(bfs.validate().is_ok());
    }

    #[test]
    fn and_bfs_constants() {
        let vars = BddVariableSet::new_anonymous(3);
        let tt = vars.mk_true();
        let ff = vars.mk_false();
        let x = vars.mk_var(BddVariable(0));

        assert_eq!(ff.and_bfs(&x), ff);
        assert_eq!(x.and_bfs(&ff), ff);
        assert_eq!(tt.and_bfs(&tt), tt);
        assert_eq!(tt.and_bfs(&x), x);
        assert_eq!(x.and_bfs(&tt), x);
        assert_eq!(x.and_bfs(&x), x);
    }

    #[test]
    fn and_bfs_small_test_bdd() {
        let left = mk_small_test_bdd();
        let right = mk_small_test_bdd();
        assert_eq!(left.and_bfs(&right), left.and(&right));
        assert!(left.and_bfs(&right).validate().is_ok());
    }

    #[test]
    fn and_bfs_hand_written() {
        let vars = BddVariableSet::new_anonymous(5);
        let a = vars.eval_expression_string("x_0 & x_1");
        let b = vars.eval_expression_string("x_2 | x_3");
        assert_bfs_matches_dfs(&a, &b, op_function::and);
    }

    #[test]
    fn binary_op_bfs_all_standard_ops() {
        let vars = BddVariableSet::new_anonymous(4);
        let formulas = [
            vars.eval_expression_string("x_0 & x_1"),
            vars.eval_expression_string("x_0 | x_1"),
            vars.eval_expression_string("x_0 ^ x_2"),
            vars.eval_expression_string("!x_0 & x_3"),
            vars.eval_expression_string("x_1 => x_2"),
            vars.mk_true(),
            vars.mk_false(),
        ];
        let ops = [
            op_function::and,
            op_function::or,
            op_function::imp,
            op_function::iff,
            op_function::xor,
            op_function::and_not,
        ];

        for left in &formulas {
            for right in &formulas {
                for op in ops {
                    assert_bfs_matches_dfs(left, right, op);
                }
            }
        }
    }

    fn random_formula(vars: &BddVariableSet, num_vars: u16, seed: u64) -> Bdd {
        let mut rand = StdRng::seed_from_u64(seed);
        let mut parts = Vec::new();
        for i in 0..num_vars {
            let var = BddVariable(i);
            if rand.next_u32() % 2 == 0 {
                parts.push(vars.mk_var(var));
            } else {
                parts.push(vars.mk_literal(var, rand.next_u32() % 2 == 0));
            }
        }
        let mut acc = parts[0].clone();
        for part in parts.into_iter().skip(1) {
            acc = if rand.next_u32() % 2 == 0 {
                acc.or(&part)
            } else {
                acc.and(&part)
            };
        }
        acc
    }

    #[test]
    fn binary_op_bfs_fuzz_cross_check() {
        let seeds = [1_u64, 12, 123, 1234, 12345];
        let ops = [op_function::and, op_function::or, op_function::xor];
        for num_vars in 2..=6 {
            let vars = BddVariableSet::new_anonymous(num_vars);
            for seed in seeds {
                let left = random_formula(&vars, num_vars, seed);
                let right = random_formula(&vars, num_vars, seed.wrapping_mul(31));
                for op in ops {
                    assert_bfs_matches_dfs(&left, &right, op);
                }
            }
        }
    }

    #[test]
    #[should_panic(expected = "Var count mismatch")]
    fn and_bfs_var_count_mismatch() {
        let a = Bdd::mk_true(2);
        let b = Bdd::mk_true(3);
        let _ = a.and_bfs(&b);
    }
}
