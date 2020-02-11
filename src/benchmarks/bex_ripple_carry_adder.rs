use test::Bencher;
use bex::bdd::{BDDBase, O, NID, nv};

fn ripple_carry_adder(b: &mut Bencher, num_vars: u16) {
    b.iter(|| {
        // We cannot reuse base because it stores all BDDs and hence only the first benchmark would
        // actually compute something...
        let mut base = BDDBase::new(num_vars as usize);
        let mut result: NID = O;
        for x in 0..(num_vars / 2) {
            let x1 = nv(x as u32);
            let x2 = nv((x + num_vars / 2) as u32);
            let x1_and_x2 = base.and(x1, x2);
            result = base.or(result, x1_and_x2);
        }
        result
    });
}

#[bench]
fn bex_ripple_carry_adder_4(bencher: &mut Bencher) {
    ripple_carry_adder(bencher, 4);
}

#[bench]
fn bex_ripple_carry_adder_8(bencher: &mut Bencher) {
    ripple_carry_adder(bencher, 8);
}

#[bench]
fn bex_ripple_carry_adder_16(bencher: &mut Bencher) {
    ripple_carry_adder(bencher, 16);
}

#[bench]
#[cfg(feature = "large_benchmarks")]
fn bex_ripple_carry_adder_32(bencher: &mut Bencher) {
    ripple_carry_adder(bencher, 32);
}
