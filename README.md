[![Crates.io](https://img.shields.io/crates/v/biodivine-lib-bdd?style=flat-square)](https://crates.io/crates/biodivine-lib-bdd)
[![Api Docs](https://img.shields.io/badge/docs-api-yellowgreen?style=flat-square)](https://docs.rs/biodivine-lib-bdd/)
[![Travis (.org)](https://img.shields.io/travis/sybila/biodivine-lib-bdd?style=flat-square)](https://travis-ci.org/sybila/biodivine-lib-bdd)
[![Codecov](https://img.shields.io/codecov/c/github/sybila/biodivine-lib-bdd?style=flat-square)](https://codecov.io/gh/sybila/biodivine-lib-bdd)
[![GitHub issues](https://img.shields.io/github/issues/sybila/biodivine-lib-bdd?style=flat-square)](https://github.com/sybila/biodivine-lib-bdd/issues)
[![Dev Docs](https://img.shields.io/badge/docs-dev-orange?style=flat-square)](https://biodivine.fi.muni.cz/docs/biodivine-lib-bdd/v0.2.0/)
[![GitHub last commit](https://img.shields.io/github/last-commit/sybila/biodivine-lib-bdd?style=flat-square)](https://github.com/sybila/biodivine-lib-bdd/commits/master)
[![Crates.io](https://img.shields.io/crates/l/biodivine-lib-bdd?style=flat-square)](https://github.com/sybila/biodivine-lib-bdd/blob/master/LICENSE)
[![GitHub top language](https://img.shields.io/github/languages/top/sybila/biodivine-lib-bdd?style=flat-square)](https://github.com/sybila/biodivine-lib-bdd)

## Profile Capture

This branch contains a modified version of the library which automatically produces "profile data" from all executed operations. Profile consists of all binary operations performed by the library and depends on the size of the larger operand. Specifically, we say that a profile is `big-big-big` if all operands and result are roughly the same size (up to 0.5x) and then we distinguish `big-big-small` (operands equal, result small), up to `big-small-empty`. Here `small` means the second operand is `<0.5` of the larger one, and result is `empty`.

The information is stored in the folder `/perf` and files are named as `profile-type.size.op.left/right.bdd` where `profile-type` is explained above, `size` is the number of nodes in the larger BDD and `A/B` is `left/right` operand.

The collector will keep track of max size of BDD in each category and output a new benchmark instance if a BDD with at least +10% nodes is encountered. The capture only happens for BDD with 100 or more nodes. We don't capture bit flips, as these don't really change the size of the BDD.

To enable collection of performance data, compile with `--features capture_profile`.

# Biodivine/LibBDD

This crate provides a basic implementation of binary decision diagrams (BDDs) — a symbolic data
structure for representing boolean functions or other equivalent objects (such as bit-vector
sets).

Compared to other popular implementations, every BDD owns its memory. It is thus trivial to
serialise, but also to share between threads. This makes it useful for applications that
process high number of BDDs concurrently.

We currently provide support for explicit operations as well as evaluation of basic boolean
expressions and a custom `bdd` macro for hybrid usage:

```rust
use biodivine_lib_bdd::*;

fn demo() {
    let vars = BddVariableSet::new(vec!["a", "b", "c"]);
    let a = vars.mk_var_by_name("a");
    let b = vars.mk_var_by_name("b");
    let c = vars.mk_var_by_name("c");
    
    let f1 = a.iff(&b.not()).or(&c.xor(&a));
    let f2 = vars.eval_expression_string("(a <=> !b) | c ^ a");
    let f3 = bdd!((a <=> (!b)) | (c ^ a));
    
    assert!(!f1.is_false());
    assert_eq!(f1.cardinality(), 6.0);
    assert_eq!(f1, f2);
    assert_eq!(f2, f3);
    assert!(f1.iff(&f2).is_true());
    assert!(f1.iff(&f3).is_true());
}
```

Additionally, we provide serialisation into a custom string and binary formats as well as `.dot`.
For a more detailed description, see the [tutorial module](https://docs.rs/biodivine-lib-bdd/0.1.0/biodivine_lib_bdd/tutorial/index.html) documentation.
There is also an experimental support for converting BDDs back into boolean expressions.

### Performance

Critical part of every BDD implementation is performance. Currently, the repository contains a 
`benchmark` branch with several benchmark problems evaluable using this crate as well as other 
state-of-the-art BDD libraries (`bex`, `cudd` and `buddy`). In our experience, 
`biodivine-lib-bdd` performs comparably to these libraries for large problem instances:

![Performance stats](https://docs.google.com/spreadsheets/d/e/2PACX-1vThU2ahv1f3PcLVheM09iFUYUemCa9uzd8-r9erc610n7YP-soTfclYnpooyXVPCDGEhLvTzW0c11wG/pubchart?oid=933758842&format=image)

The benchmarks typically consist of incrementally constructing one large BDD of exponential size.
For some applications where node reuse is more important (very similar formulas appear
repeatedly), `lib-bdd` would probably be slower. Also note that even though `buddy` is winning,
the setting of initial cache size was critical when achieving this level of performance
(each benchmark has a specifically tuned cache size to avoid garbage collection and overallocation). 
If the size of the problem is not known beforehand, `buddy` may perform significantly worse.
