use criterion::{black_box, criterion_group, criterion_main, Criterion, Bencher};
use biodivine_lib_bdd::{bdd, BddVariableSet};

fn ripple_carry_adder(b: &mut Bencher, num_vars: u16) {
    let vars = BddVariableSet::new_anonymous(num_vars);
    let variables = vars.variables();
    b.iter(|| {
        let mut result = vars.mk_false();
        for x in 0..(num_vars / 2) {
            let x1 = vars.mk_var(variables[x as usize]);
            let x2 = vars.mk_var(variables[(x + num_vars / 2) as usize]);
            result = bdd!(result | (x1 & x2));
        }
        result
    });
}

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("ripple-carry-adder 4", |b| {
        ripple_carry_adder(b, 4);
    });
    c.bench_function("ripple-carry-adder 8", |b| {
        ripple_carry_adder(b, 8);
    });
    c.bench_function("ripple-carry-adder 16", |b| {
        ripple_carry_adder(b, 16);
    });
    c.bench_function("ripple-carry-adder 32", |b| {
        ripple_carry_adder(b, 32);
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);