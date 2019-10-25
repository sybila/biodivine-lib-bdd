
//extern crate test;

use super::*;
use rand::prelude::StdRng;
use rand::{RngCore, SeedableRng};
//use test::Bencher;


enum BddOp {
    AND, OR, XOR, IMP, IFF
}

struct Op {
    op: BddOp, negate: bool
}

struct BddOpTree {
    leaves: Vec<BddVariable>,
    ops: Vec<Vec<Op>>
}

impl BddOpTree {

    fn new_random(tree_height: u8, num_vars: u16, seed: u64) -> BddOpTree {
        let mut rand = StdRng::seed_from_u64(seed);
        let num_leafs = 1 << (tree_height as usize);
        let mut levels: Vec<Vec<Op>> = Vec::new();

        let leaves: Vec<BddVariable> = (0..num_leafs).map(|i| {
            let id = rand.next_u32() % num_vars as u32;
            BddVariable(id as u16)
        }).collect();

        let mut level_width= num_leafs / 2;
        for l in 0..tree_height {
            let level: Vec<Op> = (0..level_width).map(|_| {
                let negate = rand.next_u32() % 2 == 0;
                let op = match rand.next_u32() % 5 {
                    0 => BddOp::AND, 1 => BddOp::OR, 2 => BddOp::XOR, 3 => BddOp::IMP,
                    _ => BddOp::IFF
                };
                Op { op, negate }
            }).collect();
            levels.push(level);
        }

        return BddOpTree {
            leaves, ops: levels
        }
    }

    fn eval_in(&self, universe: BddUniverse) -> Bdd {
        let mut formulas: Vec<Bdd> = self.leaves.iter()
            .map(|v| universe.mk_var(&v))
            .collect();

        for level in self.ops.iter() {
            let mut i = 0;
            let mut new_formulas = Vec::new();
            while i < formulas.len() {
                let a = &formulas[i];
                let b = &formulas[i+1];
                let op = &level[i/2];
                let result = match op.op {
                    BddOp::AND => universe.mk_and(&a, &b),
                    BddOp::OR => universe.mk_or(&a, &b),
                    BddOp::XOR => universe.mk_xor(&a, &b),
                    BddOp::IMP => universe.mk_imp(&a, &b),
                    BddOp::IFF => universe.mk_iff(&a, &b),
                };
                if op.negate {
                    new_formulas.push(universe.mk_not(&result))
                } else {
                    new_formulas.push(result);
                }
                i += 2;
            }
            formulas = new_formulas;
        }

        return formulas[0].clone();
    }

}

#[test]
fn fuzz() {
    let universe = BddUniverse::new_anonymous(32);
    let op_tree = BddOpTree::new_random(4, 32, 1234567);
    let eval = op_tree.eval_in(universe);
    println!("Eval size: {}", eval.size());
    //panic!("");
    // TODO: Test that eval is actually correct!
}
/* TODO: Benchmarks need a separate crate because they can only be built with nightly compiler.
//#![feature(test)] - add to root file

#[bench]
fn fuzz_bench(b: &mut Bencher) {
    b.iter(|| {
        let universe = BddUniverse::new_anonymous(32);
        let op_tree = BddOpTree::new_random(4, 32, 1234567);
        op_tree.eval_in(universe);
    });

}*/