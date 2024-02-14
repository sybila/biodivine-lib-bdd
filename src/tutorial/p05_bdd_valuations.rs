//! # `Bdd` clauses and valuations
//!
//! In many cases, we need to inspect the "contents" of a `Bdd`. That is, the valuations or clauses
//! that are stored in the graph.
//!
//! ## Iterators
//!
//! Most straightforward way is to list all valuations directly. Of course, this operation
//! can be very time-consuming for a large `Bdd`. But if `Bdd.cardinality()` is sufficiently small,
//! it is possible to enumerate all valuations of a `Bdd`:
//!
//! ```rust
//! use biodivine_lib_bdd::{Bdd, ValuationsOfClauseIterator, BddVariableSet};
//! use std::collections::HashSet;
//! let variables = BddVariableSet::new(&["v1", "v2", "v3", "v4"]);
//! let bdd = variables.eval_expression_string("(v4 => (v1 & v2)) & (!v4 => (!v1 & v3))");
//!
//! bdd.sat_valuations().for_each(|valuation| {
//!     // Assuming the valuation has the right number of variables, every `Bdd` evaluates
//!     // to true/false in a valuation.
//!     assert!(bdd.eval_in(&valuation));
//! });
//!
//! let sat = bdd.sat_valuations().collect::<HashSet<_>>();
//!
//! // You can also create an iterator over *every* valuation. This is effectively the same as
//! // calling variables.mk_true().sat_valuations().
//! let all_valuations = ValuationsOfClauseIterator::new_unconstrained(bdd.num_vars());
//! all_valuations.for_each(|valuation| {
//!     assert_eq!(bdd.eval_in(&valuation), sat.contains(&valuation));
//! });
//!
//! // Of course, you can convert a valuation back to a `Bdd`:
//! let first = Bdd::from(bdd.sat_valuations().next().unwrap());
//! assert!(!first.and(&bdd).is_false());
//! assert!(first.is_valuation());  // Tests that a `Bdd` represents exactly one valuation.
//! ```
//!
//! If the number of valuations is too big, you can often still examine all *clauses* of a `Bdd`
//! (i.e. paths leading to `1`):
//!
//! ```rust
//! use biodivine_lib_bdd::{Bdd, ValuationsOfClauseIterator, BddVariableSet};
//! use std::collections::HashSet;
//! let variables = BddVariableSet::new(&["v1", "v2", "v3", "v4"]);
//! let bdd = variables.eval_expression_string("(v4 => (v1 & v2)) & (!v4 => (!v1 & v3))");
//!
//! let mut total = 0;
//! bdd.sat_clauses().for_each(|clause| {
//!     // To convert a path back into a `Bdd`, we need to interpret it as a conjunctive clause.
//!     let clause_bdd = variables.mk_conjunctive_clause(&clause);
//!     assert!(!clause_bdd.and(&bdd).is_false());
//!     // And we can also test whether the `Bdd` is a single path.
//!     assert!(clause_bdd.is_clause());
//!
//!     // Keep in mind that you can still iterate over valuations that match a specific path:
//!     for valuation in ValuationsOfClauseIterator::new(clause, bdd.num_vars()) {
//!         total += 1;
//!     }
//! });
//!
//! assert_eq!(total, bdd.sat_valuations().count());
//! ```
//!
//! ## Path/valuation selectors
//!
//! If the `Bdd` is very big, even iterating paths can be a problem. However, you can still use
//! some of the following methods to obtain some insight into the structure of the `Bdd`:
//!
//!  - `Bdd.first_valuation` and `Bdd.last_valuation` will give you the (lexicographically) first
//! and last valuation.
//!  - Similarly, `Bdd.first_clause` and `Bdd.last_clause` will give you the first and last path
//! satisfying path.
//!  - `Bdd.most_positive_valuation` and `Bdd.most_negative_valuation` return the valuations
//! with the highest amount of positive/negative literals.
//!  - `Bdd.most_fixed_clause` and `Bdd.most_free_clause` wil give you satisfying paths with
//! greatest and least amount of fixed variables respectively.
//!  - `Bdd.random_valuation` and `Bdd.random_clause` allow selecting valuation/clause using
//! a random number generator.
//!
//!
