use biodivine_lib_bdd::{BddVariableSet, bdd};
use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;

fn ripple_carry_adder(vars: &BddVariableSet, num_vars: u16) {
    let variables = vars.variables();
    let mut result = vars.mk_false();
    for x in 0..(num_vars / 2) {
        let x1 = vars.mk_var(variables[x as usize]);
        let x2 = vars.mk_var(variables[(x + num_vars / 2) as usize]);
        result = bdd!(result | (x1 & x2));
    }
    black_box(result);
}

fn ripple_carry_adder_bfs(vars: &BddVariableSet, num_vars: u16) {
    let variables = vars.variables();
    let mut result = vars.mk_false();
    for x in 0..(num_vars / 2) {
        let x1 = vars.mk_var(variables[x as usize]);
        let x2 = vars.mk_var(variables[(x + num_vars / 2) as usize]);
        result = result.or_bfs(&x1.and_bfs(&x2));
    }
    black_box(result);
}

fn bench_ripple_carry_adder(c: &mut Criterion) {
    let mut group = c.benchmark_group("ripple_carry_adder");
    group.sample_size(10);

    /*for num_vars in [4u16, 8, 16] {
        let vars = BddVariableSet::new_anonymous(num_vars);
        group.bench_function(format!("{num_vars}"), |b| {
            b.iter(|| ripple_carry_adder(&vars, num_vars))
        });
    }*/

    #[cfg(feature = "large_benchmarks")]
    {
        let num_vars = 40u16;
        let vars = BddVariableSet::new_anonymous(num_vars);
        group.bench_function(format!("{num_vars}"), |b| {
            b.iter(|| ripple_carry_adder(&vars, num_vars))
        });
    }

    group.finish();
}

fn bench_ripple_carry_adder_bfs(c: &mut Criterion) {
    let mut group = c.benchmark_group("ripple_carry_adder_bfs");
    group.sample_size(10);

    /*for num_vars in [4u16, 8, 16] {
        let vars = BddVariableSet::new_anonymous(num_vars);
        group.bench_function(format!("{num_vars}"), |b| {
            b.iter(|| ripple_carry_adder_bfs(&vars, num_vars))
        });
    }*/

    #[cfg(feature = "large_benchmarks")]
    {
        let num_vars = 40u16;
        let vars = BddVariableSet::new_anonymous(num_vars);
        group.bench_function(format!("{num_vars}"), |b| {
            b.iter(|| ripple_carry_adder_bfs(&vars, num_vars))
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_ripple_carry_adder,
    bench_ripple_carry_adder_bfs
);
criterion_main!(benches);
