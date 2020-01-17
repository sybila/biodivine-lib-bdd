use crate::{bdd, BddVariable, BddVariableSet};
use test::Bencher;

fn bn_parametrised_observability(b: &mut Bencher, num_regulators: u16) {
    let num_vars: u16 = 1 << num_regulators;
    let vars = BddVariableSet::new_anonymous(num_vars);
    b.iter(|| {
        let mut result = vars.mk_true();
        for input in 0..num_regulators {
            let block_size = 1 << (input + 1);
            let half_block = block_size / 2;
            let mut regulator_formula = vars.mk_false();
            for block in 0..(num_vars / block_size) {
                for block_item in 0..half_block {
                    let var1 = BddVariable(block_size * block + block_item);
                    let var2 = BddVariable(block_size * block + block_item + half_block);
                    let x1 = vars.mk_var(var1);
                    let x2 = vars.mk_var(var2);
                    regulator_formula = bdd!(regulator_formula | (!(x1 <=> x2)));
                }
            }
            result = bdd!(result & regulator_formula);
        }
        result
    });
}

fn bn_parametrised_activation(b: &mut Bencher, num_regulators: u16) {
    let num_vars: u16 = 1 << num_regulators;
    let vars = BddVariableSet::new_anonymous(num_vars);
    b.iter(|| {
        let mut result = vars.mk_true();
        for input in 0..num_regulators {
            let block_size = 1 << (input + 1);
            let half_block = block_size / 2;
            let mut regulator_formula = vars.mk_true();
            for block in 0..(num_vars / block_size) {
                for block_item in 0..half_block {
                    let var1 = BddVariable(block_size * block + block_item);
                    let var2 = BddVariable(block_size * block + block_item + half_block);
                    let x1 = vars.mk_var(var1);
                    let x2 = vars.mk_var(var2);
                    regulator_formula = bdd!(regulator_formula & (x1 => x2));
                }
            }
            result = bdd!(result & regulator_formula);
        }
        result
    });
}

#[bench]
fn bn_parametrised_observability_4(b: &mut Bencher) {
    bn_parametrised_observability(b, 4);
}

#[bench]
#[cfg(feature = "large_benchmarks")]
fn bn_parametrised_observability_5(b: &mut Bencher) {
    bn_parametrised_observability(b, 5);
}

#[bench]
fn bn_parametrised_activation_4(b: &mut Bencher) {
    bn_parametrised_activation(b, 4);
}

#[bench]
#[cfg(feature = "large_benchmarks")]
fn bn_parametrised_activation_5(b: &mut Bencher) {
    bn_parametrised_activation(b, 5);
}
