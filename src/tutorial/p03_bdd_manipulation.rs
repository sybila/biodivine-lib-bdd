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
//! let vars = BddVariableSet::new(&["a", "b", "c"]);
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
//! let variables = BddVariableSet::new(&["a", "b", "c"]);
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
//! When using expressions, you can't reuse existing `Bdd`s - specifically, expressions are
//! awesome when creating small, self contained examples but don't work very well if you need
//! to pass `Bdd`s around and manipulate them.
//!
//! For this, you can use the `bdd` macro. Unfortunately, rust macro system is a bit more strict,
//! hence macros are not as permissive as expressions, but they still allow a fair amount of
//! succinctness.
//!
//! The main difference compared to expressions is that in a macro, every operator (even `!`) must
//! be properly parenthesised (except for the root of the expression). On the other hand,
//! you are no longer limited to variable names as atoms,
//! you can use any `Bdd` object in the current scope. Furthermore, if you specify
//! a `BddVariableSet`, you can also use ony `BddVariable`, or even `&str` (which will be
//! interpreted as a variable name).
//!
//! ```rust
//! use biodivine_lib_bdd::{BddVariableSet, bdd, BddVariableSetBuilder};
//!
//! let mut builder = BddVariableSetBuilder::new();
//! let [a, b, c] = builder.make(&["a", "b", "c"]);
//! let variables = builder.build();
//!
//! // Mixed usage of `BddVariable` and `&str` to create literals.
//! let f1 = bdd!(variables, a & ((!"b") => ("c" ^ a)));
//! let f2 = bdd!(variables, (b | ("a" ^ c)) & "a");
//! // If all literals are `Bdd` objects, you can omit the `BddVariableSet`.
//! let eq = bdd!(f1 <=> f2);
//!
//! assert_eq!(variables.mk_true(), eq);
//! ```
//!
//! ## Conjunctive/Disjunctive clauses and normal forms
//!
//! Various tools often output logical formulas in either conjunctive or disjunctive normal form
//! (CNF or DNF). To better support this type of format, you can rely on `BddPartialValuation`
//! to create clauses (either disjunctive or conjunctive) and then full CNF/DNF formulas.
//!
//! One advantage of this approach is relative conciseness and machine-friendliness. Another reason
//! why this API is available is that creating clauses explicitly (via `and`/`or` methods) can
//! be resource intensive for formulas with a large amount of variables and clauses. In these cases,
//! each literal in such a formula requires creation of a new `Bdd` object which is
//! quite costly when there are, say, 10.000+ literals. These special methods partially avoid
//! this problem.
//!
//! ```rust
//! use biodivine_lib_bdd::{BddVariableSet, BddPartialValuation, BddVariableSetBuilder};
//!
//! let mut builder = BddVariableSetBuilder::new();
//! let [a, b, c] = builder.make(&["a", "b", "c"]);
//! let variables = builder.build();
//!
//! // A partial assignment of variables: a=true, c=false, b remains unspecified.
//! let clause_one = BddPartialValuation::from_values(&[(a, true), (c, false)]);
//! // Order of variables can be arbitrary. Duplicates resolve to the last provided value.
//! let clause_two = BddPartialValuation::from_values(&[(b, true), (a, false), (b, false)]);
//!
//! // Building a single clause:
//! assert_eq!(
//!     variables.mk_disjunctive_clause(&clause_one),
//!     variables.eval_expression_string("a | !c")
//! );
//! assert_eq!(
//!     variables.mk_conjunctive_clause(&clause_one),
//!     variables.eval_expression_string("a & !c")
//! );
//!
//! // Or a full CNF/DNF formula:
//! let cnf_formula = variables.eval_expression_string("(a | !c) & (!b | !a)");
//! let dnf_formula = variables.eval_expression_string("(a & !c) | (!b & !a)");
//!
//! let formula = [clause_one, clause_two];
//! assert_eq!(variables.mk_dnf(&formula), dnf_formula);
//! assert_eq!(variables.mk_cnf(&formula), cnf_formula);
//! ```
//!
//! To learn more about how to work with individual valuations of a `Bdd`, you can also look
//! at the fourth chapter of this tutorial.
