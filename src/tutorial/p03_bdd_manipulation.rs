//! # Manipulating `Bdd`s idiomatically
//!
//! There are multiple ways of creating `Bdd`s representing complex boolean formulas, each
//! useful in different situations.
//!
//! ## Direct method calls
//!
//! Once you have created the basic formulas, you can combine them using the methods of
//! the `Bdd` struct into more complex formulas:
//!
//! ```rust
//! use biodivine_lib_bdd::BddVariableSet;
//!
//! let vars = BddVariableSet::new(vec!["a", "b", "c"]);
//! let a = vars.mk_var_by_name("a");
//! let b = vars.mk_var_by_name("b");
//! let c = vars.mk_var_by_name("c");
//!
//! let a_and_b = a.and(&b);
//! let b_or_c = b.or(&c);
//! let a_and_b_not_eq_b_or_c = a_and_b.iff(&b_or_c).not();
//! ```
//!
//! Sadly, this can be quite cumbersome for large formulas. Thankfully, there are easier
//! ways to manipulate `Bdd`s.
//!
//! ## Boolean expressions
//!
//! Once you have a `BddVariableSet` ready, the most basic way to quickly create complex `Bdd`s
//! is to use our custom Boolean expression language:
//!
//! ```rust
//! use biodivine_lib_bdd::BddVariableSet;
//! use std::convert::TryFrom;
//! use biodivine_lib_bdd::boolean_expression::BooleanExpression;
//!
//! let variables = BddVariableSet::new(vec!["a", "b", "c"]);
//!
//! let f1 = variables.eval_expression_string("a & (!b => c ^ a)");
//!
//! let expression = BooleanExpression::try_from("(b | a ^ c) & a").unwrap();
//! let f2 = variables.eval_expression(&expression);
//!
//! assert_eq!(f1, f2);
//! ```
//!
//! In these expressions, you can use all common logical operators (in the order of precedence:
//! `<=>`, `=>`, `|`, `&`, `^`, `!`), parentheses, and any variable name which is valid in your
//! set.
//!
//! Notice that if something goes wrong, `eval_expression_string` panics. If you want to use
//! the same expression repeatedly or allow the user to enter their own expressions, you can parse
//! the expression safely using `BooleanExpression::try_from` and then use `safe_eval_expression`.
//! This will give you a human readable error when the parsing fails or there are invalid variables
//! in the expression.
//!
//! ## `bdd` macro
//!
//! When using expressions, you can't reuse existing `Bdd`s - secifically, expressions are
//! awesome when creating small, self contained examples but don't work very well if you need
//! to pass `Bdd`s around and manipulate them.
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
//! use biodivine_lib_bdd::{BddVariableSet, bdd};
//!
//! let variables = BddVariableSet::new(vec!["a", "b", "c"]);
//!
//! let a = variables.mk_var_by_name("a");
//! let b = variables.mk_var_by_name("b");
//! let c = variables.mk_var_by_name("c");
//!
//! let f1 = bdd!(a & ((!b) => (c ^ a)));
//! let f2 = bdd!((b | (a ^ c)) & a);
//! let eq = bdd!(f1 <=> f2);
//!
//! assert_eq!(variables.mk_true(), eq);
//! ```
//!
//!
