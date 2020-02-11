/// **(internal)** Explicitly test different logical identities and properties.
mod _test_bdd_logic_basic;

/// **(internal)** Generate pseudo-random expression trees, evaluate them and exhaustively
/// verify that the `Bdd` represents the tree correctly.
mod _test_bdd_logic_fuzzing;
