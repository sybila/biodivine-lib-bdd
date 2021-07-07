use criterion::{criterion_group, criterion_main, Criterion, SamplingMode};
use biodivine_lib_bdd::Bdd;

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut benchmarks = Vec::new();
    for file in std::fs::read_dir("./bench_inputs/itgr").unwrap() {
        let file = file.unwrap();
        let path = file.path();
        let file_name = path.file_name().unwrap().to_str().unwrap();
        if file_name.ends_with(".and_not.left.bdd") {
            let bench_name = &file_name[..(file_name.len() - 17)];
            benchmarks.push(bench_name.to_string());
        }
    }
    // Actually do the benchmarks in some sensible order.
    benchmarks.sort_by_cached_key(|name| {
        let mut split = name.split(".");
        split.next();
        let size = split.next().unwrap();
        size.parse::<usize>().unwrap()
    });

    let mut group = c.benchmark_group("itgr");
    // Some of the benchmarks will run for a long time, so this setting is recommended.
    group.sampling_mode(SamplingMode::Flat);
    for benchmark in &benchmarks {
        let left_path = format!("./bench_inputs/itgr/{}.and_not.left.bdd", benchmark);
        let left = Bdd::from_string(std::fs::read_to_string(&left_path).unwrap().as_str());
        let right_path = format!("./bench_inputs/itgr/{}.and_not.right.bdd", benchmark);
        let right = Bdd::from_string(std::fs::read_to_string(right_path).unwrap().as_str());
        group.bench_function(benchmark, |b| {
            b.iter(|| {
                left.and_not(&right)
            });
        });
    }
    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);