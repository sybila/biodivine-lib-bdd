# Benchmarks

Hello, this is a benchmark branch of the BioDivine BDD library. Here, we maintain a set of non-trivial
examples to compare performance across releases (and potentially other BDD libraries). Since benchmark
tests in Rust are currently still a little unstable, we keep benchmarks in a separate branch which 
requires a nightly compiler.

Each benchmark should have a separate file in the benchmarks module. We provide a special feature flag 
`large_benchmarks` which you can use to annotate benchmarks that you expect to take a long time. This
way, one can quickly test optimisations with `large_benchmarks` disabled and then run a full test with
larger instances. To benchmark everything, run `cargo bench --features "large_benchmarks"`.  

### Few quick resources on optimisation and profiling

Before optimizing anything, it is best to first profile your application to ensure you are truly 
optimizing the hot spots in your code. For a nice Rust profiling helper utility on MacOS, see
[Cargo Instruments](https://crates.io/crates/cargo-instruments).

Another nice crate (multi platform even!) for visualising hot spots is 
[Flame Graph](https://github.com/ferrous-systems/flamegraph).

Sometimes when doing micro-optimisations, it is also beneficial to see the actual assembly your 
code will compile to (however, this typically requires some well isolated instances of code).
To quickly explore compiled code, see [Compiler Explorer](https://godbolt.org). However, remember
to add the optimization flag `-O` to the compiler and make sure you consume the output values to
ensure the whole benchmark is not just evaluated by the compiler.

For profiling, it seems to be a little finicky to use rust benchmarks in these tools directly, so there
is a special binary target added in this branch, `bench_profile`, where you can copy your benchmark
code in order to make it easier to debug and visualise by instruments or flame graph.   

### List of benchmarks

Please, if you add a benchmark, add it to this list so that we know where the benchmarks are coming
from and how to interpret them:

#### Ripple carry adder

This is an example of a worst case BDD that has always exponential size with respect to the number of 
variables. Given variables `x_1...x_2n`, the formula is `(x_1 & x_n) + (x_2 & x_{n+1}) ...` (the trick
is that this ordering of variables for this particular formula is extremely inefficient).

#### Boolean Network static parameter constraints

In parametrized Boolean networks, the regulation table of a specific specie has `2^n` parameters.
These parameters are subject to a set of static constraints which are of the form `a => b` or `a != b`.
The pairs of `a` and `b` are the pairs of parameters where only one regulator (bit of the parameter 
index) is different (variable IDs with Hamming distance one). Sadly, this also seems to be a problem with no straightforward optimal ordering.
(We can slightly improve performance of the whole thing by reordering the operations a little smarter,
but we don't care about that for benchmark purposes)

Also, experiments suggest there might better orderings for these types of formulas, but its not clear
whether these are also exponential or not.  

### Result history

For reference, we keep a history of benchmark runs on our server (`psyche07`). The server has a 32-core
AMD processor (2990WX) with 64GB of memory at the moment. For each log, please include at least a commit 
hash of the last merged state from master and a date when the benchmarks were performed. Ideally, please
also include a small commentary about changes since the last run to explain differences in results. 