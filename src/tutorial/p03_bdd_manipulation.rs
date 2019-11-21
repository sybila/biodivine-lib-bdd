//! # Manipulating `Bdd`-s idiomatically
//!
//! Creating BDDs using the explicit fuctions provided by the `BddUniverse` can be quite
//! cumbersome. Fortunately, there are two ways to simplify this process significantly.
//!
//! ## Boolean expressions
//!
//! Once you have a `BddUniverse` ready, the most basic way to quickly create complex BDDs
//! is to use our custom Boolean expression language:
//!
//! ```rust
//! use biodivine_lib_bdd::{BooleanFormula, BddUniverse};
//! use std::convert::TryFrom;
//!
//! let universe = BddUniverse::new(vec!["a", "b", "c"]);
//!
//! let foo = universe.eval_expression("a & (!b => c ^ a)");
//!
//! let formula = BooleanFormula::try_from("(b | a ^ c) & a").unwrap();
//! let goo = universe.eval_formula(&formula);
//!
//! assert_eq!(foo, goo);
//! ```
//!
//! In these expressions, you can use all common logical operators (in the order of precedence:
//! `<=>`, `=>`, `|`, `&`, `^`, `!`), parentheses, and any variable which is valid in your
//! universe.
//!
//! Notice that if something goes wrong, `eval_expression` panics. If you want to use
//! the same expression repeatedly or allow the user to enter their own expressions, you can parse
//! the expression safely using `BooleanFormula::try_from`. This will give you a human readable
//! error when the parsing fails. However, `eval_formula` can still fail if there are some
//! unknown variables in the formula.
//!
//! ## `bdd` macro
//!
//! When using expressions, you can't reuse existing BDDs - secifically, expressions are
//! awesome when creating small, self contained examples but don't work very well if you need
//! to pass BDDs around and manipulate them.
//!
//! For this, you can use the `bdd` macro. Unfortunately, rust macro system is a bit more strict,
//! hence macros are not as permissive as expressions, but they still allow a fair amount of
//! succintness.
//!
//! The main difference compared to expressions is that in a macro, every operator (even `!`) must
//! be properly parenthesised (except the very top of the expression). On the other hand,
//! you are no longer limited to variable names as atoms,
//! you can use any `Bdd` object in the current scope:
//!
//! ```rust
//! use biodivine_lib_bdd::{BddUniverse, bdd};
//!
//! let universe = BddUniverse::new(vec!["a", "b", "c"]);
//!
//! let a = universe.mk_var_by_name("a");
//! let b = universe.mk_var_by_name("b");
//! let c = universe.mk_var_by_name("c");
//!
//! let foo = bdd!(universe, a & ((!b) => (c ^ a)));
//! let goo = bdd!(universe, (b | (a ^ c)) & a);
//! let eq = bdd!(universe, foo <=> goo);
//!
//! assert_eq!(universe.mk_true(), eq);
//! ```
//!
//!
