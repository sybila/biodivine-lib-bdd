//! # Serialising and visualising `Bdd`s
//!
//! We currently provide three ways to inspect `Bdd`s. Human-friendly way is to export the
//! `Bdd` as a **`.dot` graph file** which can be then rendered into an SVG using tools like
//! [graph-viz](http://www.webgraphviz.com/). Aside from `.dot`, we have two very basic
//! formats for serialising `Bdd`s. They both essentially just dump the corresponding node
//! array. However, the difference is that one format is **string-based**, which means it
//! can be easily used inside things like JSON or XML. The second format uses the same
//! layout, but is fully **binary**, hence it takes up much less space compared to the
//! string-based format (and is faster).
//!
//! ## `String` serialisation
//!
//! Given a `Bdd`, we can create a string where each node is serialized as three
//! numbers, `variable,low_link,high_link` and nodes are written as present in the `Bdd`
//! array, separated by `|`:
//!
//! ```rust
//! use biodivine_lib_bdd::{Bdd, BddVariableSet};
//! let variables = BddVariableSet::new(&["a", "b"]);
//! let bdd = variables.eval_expression_string("a & !b");
//! let bdd_string = bdd.to_string();
//!
//! assert_eq!("|2,0,0|2,1,1|1,1,0|0,0,2|", bdd_string);
//! assert_eq!(bdd, Bdd::from_string(&bdd_string));
//! ```
//!
//! Both serialisation and deserialization methods have a "streaming" variant where
//! you can provide your own custom `Read`/`Write` implementations.
//!
//! ## `u8` serialisation
//!
//! A `Bdd` can be also written to a byte array. This is much more compact for large `Bdd`s
//! and has the advantage of predictable size:
//!
//! ```rust
//! use biodivine_lib_bdd::{Bdd, BddVariableSet};
//! let variables = BddVariableSet::new(&["a", "b"]);
//! let bdd = variables.eval_expression_string("a & !b");
//! let bdd_bytes: Vec<u8> = bdd.to_bytes();
//!
//! assert_eq!(bdd_bytes.len(), bdd.size() * 10);
//! assert_eq!(bdd, Bdd::from_bytes(&mut &bdd_bytes[..]))
//! ```
//!
//! As in the case of `String` serialisation, each method can be also used with a
//! custom `Read`/`Write` object.
//!
//! ## `.dot` visualisation
//!
//! In order to output `Bdd` as a `.dot` graph, we have to specify a `BddVariableSet` as it provides
//! specific variable names used in the graph:
//!
//! ```rust
//! use biodivine_lib_bdd::BddVariableSet;
//!
//! let variables = BddVariableSet::new(&["a", "b", "c"]);
//! let bdd = variables.eval_expression_string("a & !(b | c)");
//! let dot = bdd.to_dot_string(&variables, true);
//! ```
//!
//! The method takes an extra boolean parameter, `pruned`. If set to `true`, edges leading to the
//! zero terminal are not included in the graph. This makes it much more readable, since these
//! edges can be inferred from context anyway.
//!
//!
