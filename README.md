![Travis (.org)](https://img.shields.io/travis/sybila/biodivine-lib-bdd?style=flat-square)
![Codecov](https://img.shields.io/codecov/c/github/sybila/biodivine-lib-bdd?style=flat-square)
![GitHub issues](https://img.shields.io/github/issues/sybila/biodivine-lib-bdd?style=flat-square)
![Crates.io](https://img.shields.io/crates/v/biodivine-lib-bdd?style=flat-square)
![GitHub last commit](https://img.shields.io/github/last-commit/sybila/biodivine-lib-bdd?style=flat-square)
![GitHub top language](https://img.shields.io/github/languages/top/sybila/biodivine-lib-bdd?style=flat-square)
![Crates.io](https://img.shields.io/crates/l/biodivine-lib-bdd?style=flat-square)

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
For a more detailed description, see the tutorial module in documentation.

