//! # Creating a `BddVariableSet` and `BddVariable`s
//!
//! In order to create and manipulate `Bdd`s, you have to first create a `BddVariableSet`.
//! The set maintains knowledge about individual Boolean variables and their ordering.
//! Once the set is created, it is immutable.
//!
//! ## Using `BddVariableSetBuilder`
//!
//! There are multiple ways to create a `BddVariableSet`. First is to initialize the set with
//! explicitly named variables using a safe builder:
//! ```rust
//! use biodivine_lib_bdd::BddVariableSetBuilder;
//!
//! let mut var = BddVariableSetBuilder::new();
//! let v1 = var.make_variable("v1");                   // a new individual variable
//! let vars = var.make_variables(vec!["v2", "v3"]);    // new batch of variables
//! let var_set = var.build();
//!
//! assert_eq!(Some(v1), var_set.var_by_name("v1"));
//! assert_eq!(None, var_set.var_by_name("unknown"));
//! ```
//!
//! Here, each `BddVariable` (`v1` and elements of `vars`) can be later used to create
//! `Bdd`s conditioning on these variables. The purpose of the set builder is to check for
//! duplicate or invalid variable names (some special characters are also not allowed because
//! it would break export to `.dot`). Once the set is created, you can use `var_by_name` to
//! obtain a specific variable based on the names you used.
//!
//! ## Creating the set directly
//!
//! If you don't need the `BddVariable` objects right away and all variables are known beforehand
//! (this may sound trivial, but sometimes different parts of your application can have different
//! requirements regarding the variables and it is just simpler to let them manipulate the builder
//! directly instead of collecting all the variable names in one place),
//! you can also skip the builder and just provide the names explicitly:
//!
//! ```rust
//! use biodivine_lib_bdd::BddVariableSet;
//!
//! let variables = BddVariableSet::new(vec!["v1", "v2", "v3"]);
//! assert_eq!(3, variables.num_vars());
//! ```
//!
//! ## Anonymous sets
//!
//! Finally, another option is to create an anonymous variable set, where the
//! variables have default names:
//!
//! ```rust
//! use biodivine_lib_bdd::BddVariableSet;
//!
//! let variables = BddVariableSet::new_anonymous(4);   // new set with 4 variables
//!
//! let vars = variables.variables();
//! assert_eq!(4, vars.len());
//! assert_eq!("x_3", variables.name_of(vars[3]));   // default name is always x_{var index}
//! ```
//!
//! By default, anonymous variables are named `x_{index}`, but you can use `name_of` to
//! obtain the name of any variable at runtime. You can also use the `variables` function to get
//! a vector of all available variables.
//!
//! ## Working with variable sets
//!
//! Once we have a variable set, we can use it to create basic `Bdd` objects:
//!
//! ```rust
//! use biodivine_lib_bdd::BddVariableSet;
//!
//! let set = BddVariableSet::new_anonymous(4);
//! let v = set.variables();
//!
//! let tt = set.mk_true();     // constant true formula
//! let v0 = set.mk_var(v[0]);  // bdd for formula (v0)
//! let not_v1 = set.mk_not_var_by_name("x_1"); // bdd for formula (!v1)
//! ```
//!
//! In order to create complex boolean combinations of these basic `Bdd`s, we can use different
//! techniques which are described in the next section of this tutorial.
//!
//! **Notice that `BddVariableSet` can be cloned.** This creates a new set with the exact same
//! variables. The `BddVariable` and `Bdd` objects can be then used with both the original
//! and cloned set interchangably. `Bdd` objects are also clonable (since they are just
//! vectors of BDD nodes) and can be used with any compatible `BddVariableSet`. This way, you can
//! quickly and easily share BDDs between different threads (each thread has its own clone of
//! the `BddVariableSet`).
//!
