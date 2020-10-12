/// **(internal)** Explicitly test different logical identities and properties.
mod _test_bdd_logic_basic;

/// **(internal)** Generate pseudo-random expression trees, evaluate them and exhaustively
/// verify that the `Bdd` represents the tree correctly.
mod _test_bdd_logic_fuzzing;

/// **(internal)** Basic tests for advanced relation operations on `Bdd`s.
mod _test_bdd_relation_ops;
