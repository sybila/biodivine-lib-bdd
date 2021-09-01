[![Crates.io](https://img.shields.io/crates/v/biodivine-lib-bdd?style=flat-square)](https://crates.io/crates/biodivine-lib-bdd)
[![Api Docs](https://img.shields.io/badge/docs-api-yellowgreen?style=flat-square)](https://docs.rs/biodivine-lib-bdd/)
[![Continuous integration](https://img.shields.io/github/workflow/status/sybila/biodivine-lib-bdd/build?style=flat-square)](https://github.com/sybila/biodivine-lib-bdd/actions?query=workflow%3Abuild)
[![Codecov](https://img.shields.io/codecov/c/github/sybila/biodivine-lib-bdd?style=flat-square)](https://codecov.io/gh/sybila/biodivine-lib-bdd)
[![GitHub issues](https://img.shields.io/github/issues/sybila/biodivine-lib-bdd?style=flat-square)](https://github.com/sybila/biodivine-lib-bdd/issues)
[![Dev Docs](https://img.shields.io/badge/docs-dev-orange?style=flat-square)](https://biodivine.fi.muni.cz/docs/biodivine-lib-bdd/latest/)
[![GitHub last commit](https://img.shields.io/github/last-commit/sybila/biodivine-lib-bdd?style=flat-square)](https://github.com/sybila/biodivine-lib-bdd/commits/master)
[![Crates.io](https://img.shields.io/crates/l/biodivine-lib-bdd?style=flat-square)](https://github.com/sybila/biodivine-lib-bdd/blob/master/LICENSE)

# Biodivine/LibBDD

This crate provides a basic implementation of [binary decision diagrams](https://en.wikipedia.org/wiki/Binary_decision_diagram) (BDDs) in Rust — a symbolic data
structure for representing Boolean functions or other equivalent objects (such as bit-vector
sets).

Compared to other popular implementations, every BDD owns its memory. It is thus trivial to
serialise, but also to share between threads. This makes it useful for applications that
process high number of BDDs concurrently, but is also generally more idiomatic in Rust.

At the moment, we support many standard operations on BDDs:

 - Any binary logical operation (`and`, `or`, `iff`, ...), and of course negation.
 - Evaluation of Boolean expressions parsed from a string.
 - A `bdd!` macro for a more idiomatic specification of operation chains.
 - Simplified methods for CNF/DNF formula construction.
 - Binary and text serialization/deserialization.
 - Valuation/path iterators and other `Bdd` introspection methods (`random_valuation`, `most_fixed_clause`, ...).
 - Export of `Bdd` back into a Boolean expression.
 - "Relational" operations: projection (existential quantification), selection (restriction) and unique subset picking (see tutorials for more info).
 - A "variable flip" operation fused with custom logical binary operators.
 - Export to `.dot` graphs.

More detailed description of all features can be found in our [tutorial module](https://docs.rs/biodivine-lib-bdd/latest/biodivine_lib_bdd/tutorial/index.html), and of course in the [API documentation](https://docs.rs/biodivine-lib-bdd/latest/).

```rust
use biodivine_lib_bdd::*;

fn main() {
    let mut builder = BddVariableSetBuilder::new();
    let [a, b, c] = builder.make(&["a", "b", "c"]);
    let variables: BddVariableSet = builder.build();
    
    // String expressions:
    let x = variables.eval_expression_string("(a <=> !b) | c ^ a");
    // Macro:
    let y = bdd!(variables, (a <=> (!b)) | (c ^ a));
    // Logical operators:
    let z = variables.mk_literal(a, true)
        .iff(&variables.mk_literal(b, false))
        .or(&variables.mk_literal(c, true).xor(&variables.mk_literal(a, true)));

    assert!(!x.is_false());
    assert_eq!(6.0, x.cardinality());
    assert_eq!(x, y);
    assert_eq!(y, z);
    assert_eq!(z, x);

    for valuation in x.sat_valuations() {
        assert!(x.eval_in(&valuation));
    }   
}
```

**Correctness:** At the moment, the project has a quite good test coverage (including a simple formula fuzzer) and is used in multiple applications. However, in case of any unexpected behaviour, please submit an issue here. There are many edge cases which we may have not considered.

**Completeness:** Even though the library can support a wide range of applications, its API is still missing some features provided by other BDD libraries. Additionally, some methods may have more performant implementations which we haven't experimented with yet, simply because they were not a bottleneck in our applications. If you find that something is either missing from the library or unexpectedly slow/impractical to implement, feel free to create an issue with a feature request, or send us a pull request! 

### Performance

Critical part of every BDD implementation is performance. Currently, the repository contains a 
`benchmark` branch with several benchmark problems evaluable using this crate as well as other 
state-of-the-art BDD libraries (`bex`, `cudd` and `buddy`). In our experience, 
`biodivine-lib-bdd` performs comparably to these libraries for complex problem instances:

![Performance stats](https://docs.google.com/spreadsheets/d/e/2PACX-1vThU2ahv1f3PcLVheM09iFUYUemCa9uzd8-r9erc610n7YP-soTfclYnpooyXVPCDGEhLvTzW0c11wG/pubchart?oid=933758842&format=image)

The benchmarks typically consist of incrementally constructing one large BDD of exponential size.
For some applications where node reuse is critically important (very similar formulas appear
repeatedly, or very small modifications to a single BDD are performed), `lib-bdd` would probably be slower. However, in our experience, these types of problems do not appear in verification/formal methods very often outside of serialization-deserialization. 

Also note that even though `buddy` is winning, the setting of initial cache size was critical when achieving this level of performance (each benchmark has a specifically tuned cache size to avoid garbage collection and overallocation). If the size of the problem is not known beforehand, `buddy` may perform significantly worse.
