# Benchmarks

Hello, this is a benchmark branch of the BioDivine BDD library. Here, we maintain a set of non-trivial
examples to compare performance across releases (and potentially other BDD libraries). Since benchmark
tests in Rust are currently still a little unstable, we keep benchmarks in a separate branch which 
requires a nightly compiler.

Each benchmark should have a separate file in the benchmarks module. We provide a special feature flag 
`large_benchmarks` which you can use to annotate benchmarks that you expect to take a long time. This
way, one can quickly test optimisations with `large_benchmarks` disabled and then run a full test with
larger instances. To benchmark everything, run `cargo bench --features "large_benchmarks"`.  

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

#### Asynchronous Boolean Network semantics

The dynamics of a Boolean network are governed by its update functions. Given a variable `A`, an update
function is a standard Boolean function `f_A(A, B, C)` of some regulating variables `A, B, C`. The dynamics
of the network can be then described as a relation in `A, B, C, ..., A', B', C', ...` such that for every 
variable, we have an update formula `A' = f_A(A, B, C, ...) & B' = B & C' = C ...`.  The complete dynamics
is then a disjunction of these update formulas. The dynamics is called asynchronous since every update
formula can change only one variable and any of the variables can be changed at any time. 

### Result history

For reference, we keep a history of benchmark runs on our server (`psyche07`). The server has a 32-core
AMD processor (2990WX) with 64GB of memory at the moment. For each log, please include at least a commit 
hash of the last merged state from master and a date when the benchmarks were performed. Ideally, please
also include a small commentary about changes since the last run to explain differences in results.

#### 17.01.2019
Change log: Switched hash function to FxHash and add table pre-allocation.
 
Last commit in master: `72803b35667e0da9882bf5310bd085b31a9c119f`. Results:
```
bn_parametrised_activation_4    ... bench:     142,082 ns/iter (+/- 2,607)
bn_parametrised_activation_5    ... bench:  28,053,511 ns/iter (+/- 124,039)
bn_parametrised_observability_4 ... bench:     257,180 ns/iter (+/- 4,480)
bn_parametrised_observability_5 ... bench:  61,559,665 ns/iter (+/- 791,229)
ripple_carry_adder_16           ... bench:      76,269 ns/iter (+/- 1,234)
ripple_carry_adder_32           ... bench:  26,639,188 ns/iter (+/- 243,766)
ripple_carry_adder_4            ... bench:       1,479 ns/iter (+/- 32)
ripple_carry_adder_8            ... bench:       5,798 ns/iter (+/- 118)
```

#### 28.10.2019
Last commit in master: `a04bd8a65773a71ff538b4b56921e314d15e4118`. Results:
```
bn_parametrised_activation_4    ... bench:     519,160 ns/iter (+/- 1,715)
bn_parametrised_activation_5    ... bench:  80,931,003 ns/iter (+/- 270,550)
bn_parametrised_observability_4 ... bench:     912,666 ns/iter (+/- 3,933)
bn_parametrised_observability_5 ... bench: 164,160,922 ns/iter (+/- 454,922)
ripple_carry_adder_16           ... bench:     281,110 ns/iter (+/- 1,311)
ripple_carry_adder_32           ... bench:  77,281,287 ns/iter (+/- 194,793)
ripple_carry_adder_4            ... bench:       4,504 ns/iter (+/- 32)
ripple_carry_adder_8            ... bench:      19,818 ns/iter (+/- 68)
``` 