//!
//! Here, we have a small toolbox for fuzzing out BDD framework.
//! It allows us to create an evaluable binary tree of operations, where
//! each leaf is a random BDD variable and each tree node represents one
//! binary boolean operation, possibly negated.
//!
//! Hence, each tree is just a Boolean formula. We can produce a BDD for this
//! formula and exhaustively check whether all valuations actually match the
//! result expected by the op tree. To get predictable test cases, we use
//! a predefined set of randomness seeds.
//!
//! Of course, this gets pretty slow quite fast, so we usually test only up
//! to 12 variables. However, the process can be easily configured for much
//! larger universes if needed. It can be actually a good source for a benchmark.
//! Although, for a benchmark, it might be better to generate the tree on the
//! fly, since getting a reasonably complex BDD might require large number of
//! leaves which need to be allocated and will dominate the memory usage of
//! the benchmark.

use crate::*;
use rand::prelude::StdRng;
use rand::{RngCore, SeedableRng};

#[derive(Debug)]
enum BddOp {
    AND,
    OR,
    XOR,
    IMP,
    IFF,
}

#[derive(Debug)]
struct Op {
    op: BddOp,
    negate: bool,
}

#[derive(Debug)]
struct BddOpTree {
    leaves: Vec<BddVariable>,
    ops: Vec<Vec<Op>>,
}

impl BddOpTree {
    /// Create a new random tree. The `tree_height` is the number of levels in the tree
    /// (so the number of leaves will be `2^tree_height`).
    fn new_random(tree_height: u8, num_vars: u16, seed: u64) -> BddOpTree {
        let mut rand = StdRng::seed_from_u64(seed);
        let num_leafs = 1 << (tree_height as usize);
        let mut levels: Vec<Vec<Op>> = Vec::new();

        let leaves: Vec<BddVariable> = (0..num_leafs)
            .map(|_| {
                let id = rand.next_u32() % num_vars as u32;
                BddVariable(id as u16)
            })
            .collect();

        let mut level_width = num_leafs / 2;
        for _ in 0..tree_height {
            let level: Vec<Op> = (0..level_width)
                .map(|_| {
                    let negate = rand.next_u32() % 2 == 0;
                    let op = match rand.next_u32() % 5 {
                        0 => BddOp::AND,
                        1 => BddOp::OR,
                        2 => BddOp::XOR,
                        3 => BddOp::IMP,
                        _ => BddOp::IFF,
                    };
                    Op { op, negate }
                })
                .collect();
            levels.push(level);
            level_width /= 2;
        }

        BddOpTree {
            leaves,
            ops: levels,
        }
    }

    /// Evaluate this op tree to `Bdd` using the given `BddVariableSet`.
    fn eval_in(&self, variables: &BddVariableSet) -> Bdd {
        let mut formulas: Vec<Bdd> = self.leaves.iter().map(|v| variables.mk_var(*v)).collect();

        for level in self.ops.iter() {
            let mut i = 0;
            let mut new_formulas = Vec::new();
            while i < formulas.len() {
                let a = &formulas[i];
                let b = &formulas[i + 1];
                let op = &level[i / 2];
                let result = match op.op {
                    BddOp::AND => a.and(b),
                    BddOp::OR => a.or(b),
                    BddOp::XOR => a.xor(b),
                    BddOp::IMP => a.imp(b),
                    BddOp::IFF => a.iff(b),
                };
                if op.negate {
                    new_formulas.push(result.not())
                } else {
                    new_formulas.push(result);
                }
                i += 2;
            }
            formulas = new_formulas;
        }

        formulas[0].clone()
    }

    /// Evaluate this op tree with the specified `BddValuation`.
    fn eval_in_valuation(&self, valuation: &BddValuation) -> bool {
        let mut values: Vec<bool> = self.leaves.iter().map(|v| valuation.value(*v)).collect();

        for level in self.ops.iter() {
            let mut i = 0;
            let mut new_values = Vec::new();
            while i < values.len() {
                let a = values[i];
                let b = values[i + 1];
                let op = &level[i / 2];
                let result = match op.op {
                    BddOp::AND => a && b,
                    BddOp::OR => a || b,
                    BddOp::XOR => a ^ b,
                    BddOp::IMP => (!a) || b,
                    BddOp::IFF => a == b,
                };
                if op.negate {
                    new_values.push(!result)
                } else {
                    new_values.push(result);
                }
                i += 2;
            }
            values = new_values;
        }

        values[0]
    }
}

const FUZZ_SEEDS: [u64; 10] = [
    1, 12, 123, 1234, 12345, 123456, 1234567, 12345678, 123456789, 1234567890,
];

fn fuzz_test(num_vars: u16, tree_height: u8, seed: u64) -> bool {
    let universe = BddVariableSet::new_anonymous(num_vars);
    let op_tree = BddOpTree::new_random(tree_height, num_vars, seed);
    let eval = op_tree.eval_in(&universe);

    if eval.is_true() || eval.is_false() {
        return false;
    }

    for valuation in ValuationsOfClauseIterator::new_unconstrained(num_vars) {
        assert_eq!(
            op_tree.eval_in_valuation(&valuation),
            eval.eval_in(&valuation),
            "Error in valuation {valuation:?}"
        );
    }

    let dnf = eval.to_dnf();
    let cnf = eval.to_cnf();
    let dnf_o = eval.to_optimized_dnf();

    assert!(universe.mk_dnf(&dnf).iff(&eval).is_true());
    assert!(universe.mk_dnf(&dnf_o).iff(&eval).is_true());
    assert!(universe.mk_cnf(&cnf).iff(&eval).is_true());

    true
}

#[test]
fn fuzz_var_2() {
    let mut non_trivial = 0;

    for height in 1..10 {
        for seed in FUZZ_SEEDS.iter() {
            if fuzz_test(2, height, *seed) {
                non_trivial += 1;
            }
        }
    }

    println!(
        "Check {}/{} non-trivial BDDs.",
        non_trivial,
        9 * FUZZ_SEEDS.len()
    );
}

#[test]
fn fuzz_var_4() {
    let mut non_trivial = 0;

    for height in 1..10 {
        for seed in FUZZ_SEEDS.iter() {
            if fuzz_test(4, height, *seed) {
                non_trivial += 1;
            }
        }
    }

    println!(
        "Check {}/{} non-trivial BDDs.",
        non_trivial,
        9 * FUZZ_SEEDS.len()
    );
}

#[test]
fn fuzz_var_8() {
    let mut non_trivial = 0;

    for height in 1..10 {
        for seed in FUZZ_SEEDS.iter() {
            if fuzz_test(8, height, *seed) {
                non_trivial += 1;
            }
        }
    }

    println!(
        "Check {}/{} non-trivial BDDs.",
        non_trivial,
        9 * FUZZ_SEEDS.len()
    );
}

#[test]
fn fuzz_var_12() {
    let mut non_trivial = 0;

    for height in 1..10 {
        for seed in FUZZ_SEEDS.iter() {
            if fuzz_test(12, height, *seed) {
                non_trivial += 1;
            }
        }
    }

    println!(
        "Check {}/{} non-trivial BDDs.",
        non_trivial,
        9 * FUZZ_SEEDS.len()
    );
}
