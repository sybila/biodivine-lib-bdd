//! You can use this target for profiling your benchmarks. Either call your benchmark function
//! from the main here, or just copy paste it. Don't forget to compile in --release for
//! optimisations.

use biodivine_lib_bdd::{bdd, BddVariableSet, CACHE_READ, CACHE_READ_TRIVIAL, CACHE_MISS, CACHE_READ_SAME_VAR, BddVariable};

fn main() {
    /*let num_vars = 32;
    let vars = BddVariableSet::new_anonymous(num_vars);
    let mut result = vars.mk_false();
    for x in 0..(num_vars / 2) {
        let x1 = vars.mk_var(BddVariable(x));
        let x2 = vars.mk_var(BddVariable(x + num_vars / 2));
        result = bdd!(result | (x1 & x2));
    }*/
    let num_regulators = 5;
    let num_vars: u16 = 1 << num_regulators;
    let vars = BddVariableSet::new_anonymous(num_vars);
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
    println!("Cache read: {}", unsafe { CACHE_READ });
    println!("Cache read trivial: {}", unsafe { CACHE_READ_TRIVIAL });
    println!("Cache read same var: {}", unsafe { CACHE_READ_SAME_VAR });
    println!("Cache miss: {}", unsafe { CACHE_MISS });

}
