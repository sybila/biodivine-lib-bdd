//! # Serialising and visualising `Bdd`-s
//!
//! We currently provide tree ways to inspect BDDs. Human-friendly way is to export the
//! BDD as a **`.dot` graph file** which can be then rendered into an SVG using things like
//! [graph-viz](http://www.webgraphviz.com/). Asides from .dot, we have two very basic
//! formats for exporting BDDs. They both essentially just dump the corresponding node
//! array. However, the difference is that one format is **string-based**, which means it
//! can be easily used inside things like JSON or XML. The second format uses the same
//! layout, but is fully **binary**, hence it takes up much less space compared to the
//! string-based format (and is faster).
//!
//! ## `String` serialisation
//!
//! Given a BDD, we can create a string where each node is serialized as three
//! numbers, `variable,low_link,high_link` and nodes are written as present in the BDD
//! array, separated by `|`:
//!
//! ```rust
//! use biodivine_lib_bdd::{Bdd, BddUniverse};
//! let universe = BddUniverse::new(vec!["a", "b"]);
//! let bdd = universe.eval_expression("a & !b");
//! let bdd_string = bdd.to_string();
//!
//! assert_eq!("|2,0,0|2,1,1|1,1,0|0,0,2|", bdd_string);
//! assert_eq!(bdd, Bdd::from_string(&bdd_string));
//! ```
//!
//! Both serialisation and deserialisation methods have a "streaming" variant where
//! you can provide your own custom `Read`/`Write` objects.
//!
//! ## `u8` serialisation
//!
//! A BDD can be also written to a byte array. This is much more compact for large BDDs
//! and has the advantage of predictable size:
//!
//! ```rust
//! use biodivine_lib_bdd::{Bdd, BddUniverse};
//! let universe = BddUniverse::new(vec!["a", "b"]);
//! let bdd = universe.eval_expression("a & !b");
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
//! In order to output BDD as a `.dot` graph, we have to use a BDD universe as it provides
//! specific variable names used in the graph:
//!
//! ```rust
//! use biodivine_lib_bdd::BddUniverse;
//!
//! let universe = BddUniverse::new(vec!["a", "b", "c"]);
//! let bdd = universe.eval_expression("a & !(b | c)");
//! let dot = universe.bdd_to_dot_string(&bdd, true);
//! ```
//!
//! The method takes an extra boolean parameter, `pruned`. If set to true, only positive
//! edges will be included in the graph. This makes it much more readable, since the
//! negative edges can be inferred anyway.
//!
//!
