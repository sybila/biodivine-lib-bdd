//!
//! # Advanced BDD operations
//!
//! So far, we have seen how to perform standard logical operations on BDDs, create formulas
//! from CNF/DNF representations and inspect individual valuations/clauses of a BDD. However,
//! sometimes (especially when a BDD is used to represent a relation), we also need other,
//! more specialised operations.
//!
//! ## Selection
//!
//! Selection is the simplest of operations discussed here. Essentially, selection restricts
//! a `Bdd` to valuations which have values of specific variables fixed to specific constants:
//!
//! ```rust
//! use biodivine_lib_bdd::BddVariableSet;
//! let vars = BddVariableSet::new_anonymous(5);
//! let variables = vars.variables();
//! let bdd = vars.eval_expression_string("(x_0 & !x_1) | (!x_0 & x_3)");
//!
//! let select_x0_true = bdd.var_select(variables[0], true);
//! let select_x0_false = bdd.var_select(variables[0], false);
//!
//! assert_eq!(vars.eval_expression_string("x_0 & !x_1"), select_x0_true);
//! assert_eq!(vars.eval_expression_string("!x_0 & x_3"), select_x0_false);
//! ```
//!
//! This is essentially the same as executing `Bdd.and` with an appropriate
//! `BddVariableSet.mk_literal` as argument. However, aside from `Bdd.var_select`,
//! there is also `Bdd.select` which accepts multiple variables and executes as a single
//! symbolic operation. Hence it is more efficient than calling `Bdd.and` repeatedly
//! for multiple variables.
//!
//! Note that (contrary to how selection usually works in relational algebras), the selected
//! variables remain in the `Bdd`. In a relational algebra, a selection on `x` typically results
//! in a set of vectors that do not contain `x` any more (since the value is fixed). Here, the
//! resulting `Bdd` still conditions on variable `x`, but it always requires `x` to have
//! the value specified during selection.
//!
//! ## Projection
//!
//! Projection is one of the most fundamental BDD operations. There are two "ways" of explaining
//! projection -- depending on your background, one may seem more intuitive than the other.
//!
//! > For simplicity, we are going to project using only a single variable (`Bdd.var_project`),
//! > but as in the case of selection, there is also a multi-variable projection operation
//! > available (`Bdd.project`).
//!
//! First, a "logical" approach says that a projection of a BDD through variable `x` is equivalent
//! to existential quantification in first order logic. So, if `B` is a BDD, and $\varphi$ is
//! a formula that is represented by `B`, then `B' = B.var_project(x)` represents a formula
//! $\varphi' = \exists x. \varphi$. Consequently `B'` does not depend on variable `x` in any
//! way. Which leads us to the second explanation.
//!
//! A "relational" approach says that projection is elimination. If we see the BDD `B` as
//! a collection of valuations that satisfy $\varphi$, then projection *eliminates* `x` from
//! each valuation. For example, if `B` is satisfied for `(x=true, y=true, z=false)`, then
//! `B.var_project(x)` is satisfied for `(y=true, z=false)`, regardless of `x`. However, since
//! the variable is *not* removed from the overall `BddVariableSet`, the satisfying valuations
//! will still contain `x`, the satisfiability of the `Bdd` will simply never depend on it.
//! That is, if `(x=true, y=true, z=false)` is a satisfying valuation, then
//! `(x=false, y=true, z=false)` must be as well.
//!
//! ```rust
//! use biodivine_lib_bdd::BddVariableSet;
//! let vars = BddVariableSet::new_anonymous(5);
//! let variables = vars.variables();
//! let bdd = vars.eval_expression_string("(x_0 & !x_1) | (!x_0 & x_3)");
//!
//! let projected = bdd.var_project(variables[0]);
//! assert_eq!(vars.eval_expression_string("!x_1 | x_3"), projected);
//!
//! let projected = bdd.project(&[variables[0], variables[1]]);
//! assert_eq!(vars.mk_true(), projected);
//! ```
//!
//! ## Pick
//!
//! Finally, the most "specialised" operation is `Bdd.pick` (or, again `Bdd.var_pick` when
//! only one variable is involved). Picking is similar to selection in that it fixes the
//! value of a variable. However, the outcome is slightly different:
//!
//! Say that `V` and `V'` are both satisfying valuations of a BDD `B`, and they are equivalent
//! except that `V(x) = true` and `V(x) = false`. Then, if `B' = B.var_pick(x)`, `V'` will be
//! a satisfying valuation of `B'`, but not `V`. That is, `B'` just *picked* one of the two
//! valuations. If only one of `V` and `V'` satisfies `B`, the operation will retain the one
//! satisfying valuation (i.e. again, *picks* the appropriate satisfying valuation out of the two).
//!
//! However, for pick operation, there is an important distinction. Whereas
//! `B.var_select(x, true).var_select(y, false) = B.select(&[(x, true), (y, false)])` and
//! `B.var_project(x).var_project(y) = B.project(&[x,y])`, this **does not hold** for picking.
//!
//! If we call `B.var_pick(x).var_pick(y)`, we are saying that we pick one value of `x` for each
//! valuation of remaining variables, and *then* similarly pick one value of `y`, meaning that picking
//! a value of `x` is independent of `y` and vice versa. Meanwhile, `B.pick(&[x,y])` denotes that
//! one valuation of both `x` and `y` should be picked for each valuation of the remaining variables.
//! That is, `x` and `y` are tied together in the pick operation.
//!
//! Using `pick`, we can implement various interesting relational operations. For example, say that
//! a BDD represents a relation where `i_1` and `i_2` are some "inputs" of the relation and `o_1, o_2`
//! are some "outputs". Then we can use `pick(i_1, i_2)` to select one *unique* input for each output
//! value in the relation. This effectively picks an injective relation which is a subset of the original
//! relation. Similarly, using `pick(o_1, o_2)`, we can get a sub-relation which is a valid
//! partial function (each input valuation has at most one output).
//!
//! ```rust
//! use biodivine_lib_bdd::BddVariableSet;
//! let vars = BddVariableSet::new_anonymous(5);
//! let variables = vars.variables();
//! let bdd = vars.eval_expression_string("(x_0 => (x_1 & x_2)) & (!x_0 => x_3)");
//!
//! // In the first branch, x_0 = true, x_1 is fixed to true, so there is already at most one
//! // valuation. In the second branch (x_0 = false), the operation will fix x_1 to false in order
//! // to pick one of the two available values.
//! let picked = bdd.var_pick(variables[1]);
//! let expected = vars.eval_expression_string("(x_0 => (x_1 & x_2)) & (!x_0 => (!x_1 & x_3))");
//! assert_eq!(expected, picked);
//! ```
//!
//! Finally, note that `pick` and `var_pick` prioritise picking valuations where the variables are
//! fixed to `false`. If you want to pick randomly, you can use `pick_random` and `var_pick_random`.
//! Just keep in mind that this operation will not pick a new random value for each possible valuation
//! of the remaining variables, it will just pick a random "basal value" a variable will prefer,
//! instead of defaulting to `false`.
//!
