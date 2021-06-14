/// **(internal)** Implementation of basic logical operators for `Bdd`s using the `apply` function.
pub mod _impl_boolean_ops;

/// **(internal)** Implementation of extra operations which enable relation-like treatment of BDDs
/// (quantification, selection, projection, partial element picking)
pub mod _impl_relation_ops;

/// **(internal)** Simple export functions for printing `Bdd`s as `.dot` files.
pub mod _impl_export_dot;

/// **(internal)** Implementation of the string and byte serialisation procedures for `Bdd`s.
pub mod _impl_serialisation;

/// **(internal)** Implementation of some basic internal utility methods for `Bdd`s.
pub mod _impl_util;

/// **(internal)** Provides operations for extracting cubes from `Bdds`.
pub mod _impl_cube_ops;
