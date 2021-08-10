use biodivine_lib_bdd::Bdd;
use biodivine_lib_bdd::BddVariableSet;
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn criterion_benchmark(c: &mut Criterion) {
    let bddvariableset = BddVariableSet::new_anonymous(30);
    let mut vv = vec![];
    for i in 0..30000 {
        let mut v = vec![];
        for j in 0..30 {
            if (i & (1 << j)) > 0 {
                v.push(true);
            } else {
                v.push(false);
            }
        }
        vv.push(v);
    }
    let variables: Vec<Bdd> = bddvariableset
        .variables()
        .into_iter()
        .map(|x| bddvariableset.mk_var(x))
        .collect();

    c.bench_function("new", |b| {
        b.iter(|| Bdd::dnf(&bddvariableset, bddvariableset.variables(), vv.clone()))
    });
    c.bench_function("old", |b| {
        b.iter(|| {
            let mut res = bddvariableset.mk_false();
            for v in vv.clone() {
                let mut temp = bddvariableset.mk_true();
                for (v, b) in variables.iter().zip(v.into_iter()) {
                    if b {
                        temp = temp.and(v);
                    } else {
                        temp = temp.and(&v.not());
                    }
                }
                res = res.or(&temp);
            }
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
