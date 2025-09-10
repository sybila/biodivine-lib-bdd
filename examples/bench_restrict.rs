use biodivine_lib_bdd::{Bdd, BddPartialValuation};
use rand::prelude::{SliceRandom, StdRng};
use rand::{Rng, SeedableRng};
use std::time::Instant;

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let mut file = std::fs::File::open(args[1].as_str()).unwrap();
    let bdd = Bdd::read_as_bytes(&mut file).unwrap();
    println!("Loaded: {} as Bdd({})", args[1].as_str(), bdd.size());

    let mut support = Vec::from_iter(bdd.support_set());

    for k in 1..5 {
        // Fix variables randomly.
        let mut reduction = BddPartialValuation::empty();
        let mut rng = StdRng::seed_from_u64(0);
        support.sort(); // Don't leak previous shuffled state.
        support.shuffle(&mut rng);

        for var in &support[0..k] {
            reduction[*var] = Some(rng.gen_bool(0.5));
        }

        // Run restriction.
        for _ in 0..5 {
            let start = Instant::now();
            let result = bdd.restrict(&reduction.to_values());
            println!(
                "Result: Bdd({}) in {}ms",
                result.size(),
                (Instant::now() - start).as_millis()
            );
        }
    }
}
