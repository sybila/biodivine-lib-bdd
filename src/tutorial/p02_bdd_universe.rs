//! ### Creating a `BddUniverse` and `BddVariable`-s
//!
//! In order to create and manipulate BDDs, you have to first create a **BDD universe**.
//! The universe maintains knowledge about individual Boolean variables and their ordering.
//! Once the universe is created, the set of variables is immutable.
//!
//! There are multiple ways to create a BDD universe. First is to initialize the universe with
//! explicitly named variables using a safe builder:
//! ```rust
//! use biodivine_lib_bdd::BddUniverseBuilder;
//!
//! let mut universe = BddUniverseBuilder::new();
//! let v1 = universe.make_variable("v1");   // a new individual variable
//! let vars = universe.make_variables(vec!["v2", "v3"]);    // new batch of variables
//! let universe = universe.build();
//!
//! assert_eq!(Some(v1), universe.var_by_name("v1"));
//! assert_eq!(None, universe.var_by_name("unknown"));
//! ```
//!
//! Here, each `BddVariable` (`v1` and elements of `vars`) can be later used to create
//! BDDs conditioning on these variables. The purpose of the universe builder is to check for
//! duplicate or invalid variable names (some special characters are not allowed because
//! it would break export to .dot). Once the universe is created, you can use `var_by_name` to
//! obtain a specific variable based on the names you used.
//!
//! If you don't need the `BddVariable` objects right away and all variables are known beforehand
//! (this may sound trivial, but sometimes different parts of your application can have different
//! requirements regarding the variables and it is just simpler to let them manipulate the builder
//! directly instead of collecting all the variable names in one place),
//! you can also skip the builder and just provide the names explicitly:
//!
//! ```rust
//! use biodivine_lib_bdd::BddUniverse;
//!
//! let universe = BddUniverse::new(vec!["v1", "v2", "v3"]);
//! assert_eq!(3, universe.num_vars());
//! ```
//!
//! Finally, another option is to create an anonymous universe where the
//! variables have default names:
//!
//! ```rust
//! use biodivine_lib_bdd::BddUniverse;
//!
//! let universe = BddUniverse::new_anonymous(4);   // new universe with 4 variables
//!
//! let vars = universe.variables();
//! assert_eq!("x_3", universe.name_of(vars[3]));   // default name is always x_{var index}
//! ```
//!
//! By default, anonymous variables are named `x_{index}`, but you can use `name_of` to
//! obtain the name of any variable at runtime. You can also use the `variables` function to get
//! a vector of all available variables.
//!
//! Once we have a universe, we can use it to create basic `Bdd` objects:
//!
//! ```rust
//! use biodivine_lib_bdd::BddUniverse;
//!
//! let universe = BddUniverse::new_anonymous(4);
//! let vars = universe.variables();
//!
//! let v0 = universe.mk_var(vars[0]);  // bdd for formula (v0)
//! let not_v1 = universe.mk_not_var_by_name("x_1"); // bdd for formula (!v1)
//! let v0_and_not_v1 = universe.mk_and(&v0, &not_v1); // bdd for formula (v0 & !v1)
//! ```
//!
//! However, manipulating BDDs in this way can be quite cumbersome and verbose. In next section,
//! we show how to combine BDDs in a more idiomatic way using standard logical operators.
//!
//! Notice that `BddUniverse` can be cloned. This creates a new universe with the exact same set
//! of variables. The `BddVariable` and `Bdd` objects can be then used with both the original
//! and cloned universe interchangably. `Bdd` objects are also clonable (since they are just
//! vectors of BDD nodes) and can be used with any compatible BDD universe. This way, you can
//! quickly and easily share BDDs between different threads (each thread has its own clone of
//! the `BddUniverse`).
//!
