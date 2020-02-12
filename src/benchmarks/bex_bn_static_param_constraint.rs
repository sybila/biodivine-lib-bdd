use bex::bdd::{not, nv, BDDBase, I, NID, O};
use test::Bencher;

fn bn_parametrised_observability(b: &mut Bencher, num_regulators: u16) {
    let num_vars: u16 = 1 << num_regulators;
    b.iter(|| {
        let mut base = BDDBase::new(num_vars as usize);
        let mut result: NID = I;
        for input in 0..num_regulators {
            let block_size = 1 << (input + 1);
            let half_block = block_size / 2;
            let mut regulator_formula = O;
            for block in 0..(num_vars / block_size) {
                for block_item in 0..half_block {
                    let x1 = nv((block_size * block + block_item) as u32);
                    let x2 = nv((block_size * block + block_item + half_block) as u32);
                    // !(x1 <=> x2) = !((x1 => x2) && (x2 => x1)) = !(!x1 | x2) || !(!x2 => x1)
                    // (x1 & !x2) | (x2 & !x1) =
                    let x1_and_not_x2 = base.and(x1, not(x2));
                    let x2_and_not_x1 = base.and(x2, not(x1));
                    let x1_iff_x2 = base.or(x1_and_not_x2, x2_and_not_x1);
                    regulator_formula = base.or(regulator_formula, x1_iff_x2);
                }
            }
            result = base.and(result, regulator_formula);
        }
        result
    });
}

fn bn_parametrised_activation(b: &mut Bencher, num_regulators: u16) {
    let num_vars: u16 = 1 << num_regulators;
    b.iter(|| {
        let mut base = BDDBase::new(num_vars as usize);
        let mut result: NID = I;
        for input in 0..num_regulators {
            let block_size = 1 << (input + 1);
            let half_block = block_size / 2;
            let mut regulator_formula = I;
            for block in 0..(num_vars / block_size) {
                for block_item in 0..half_block {
                    let x1 = nv((block_size * block + block_item) as u32);
                    let x2 = nv((block_size * block + block_item + half_block) as u32);
                    let x1_implies_x2 = base.or(not(x1), x2);
                    regulator_formula = base.and(regulator_formula, x1_implies_x2);
                }
            }
            result = base.and(result, regulator_formula);
        }
        result
    });
}

#[bench]
fn bex_bn_parametrised_observability_4(b: &mut Bencher) {
    bn_parametrised_observability(b, 4);
}

#[bench]
#[cfg(feature = "large_benchmarks")]
fn bex_bn_parametrised_observability_5(b: &mut Bencher) {
    bn_parametrised_observability(b, 5);
}

#[bench]
fn bex_bn_parametrised_activation_4(b: &mut Bencher) {
    bn_parametrised_activation(b, 4);
}

#[bench]
#[cfg(feature = "large_benchmarks")]
fn bex_bn_parametrised_activation_5(b: &mut Bencher) {
    bn_parametrised_activation(b, 5);
}
