use test::Bencher;
use crate::{BddUniverse, BddVariable};
use crate::bdd;

fn ripple_carry_adder(b: &mut Bencher, num_vars: u16) {
    let universe = BddUniverse::new_anonymous(num_vars);
    b.iter(|| {
        let mut result = universe.mk_false();
        for x in 0..(num_vars / 2) {
            let x1 = universe.mk_var(&BddVariable(x));
            let x2 = universe.mk_var(&BddVariable(x + num_vars / 2));
            result = bdd!(universe, result | (x1 & x2));
        }
        result
    });
}

#[bench]
fn ripple_carry_adder_4(bencher: &mut Bencher) {
    ripple_carry_adder(bencher, 4);
}

#[bench]
fn ripple_carry_adder_8(bencher: &mut Bencher) {
    ripple_carry_adder(bencher, 8);
}

#[bench]
fn ripple_carry_adder_16(bencher: &mut Bencher) {
    ripple_carry_adder(bencher, 16);
}

#[bench]
#[cfg(feature = "large_benchmarks")]
fn ripple_carry_adder_32(bencher: &mut Bencher) {
    ripple_carry_adder(bencher, 32);
}