use crate::BddPointer;

/// **(internal)** Implementation of basic logical operators for `Bdd`s using the `apply` function.
pub mod _impl_boolean_ops;

/// **(internal)** Implementation of a generic ternary operations. These may be faster for certain
/// special cases, e.g. when the intermediate result is expected to be large, but the final
/// result is typically small or empty.
pub mod _impl_ternary_ops;

/// **(internal)** Implementation of generic nested operations. These combine two logical
/// operators: First operation is applied on the two BDD arguments, second operation is applied
/// on BDD nodes of the resulting BDD based on used provided trigger function. This is mainly
/// used to implement existential/universal projection, but who knows what else can be
/// built with it.
pub mod _impl_nested_ops;

/// **(internal)** Implementation of extra operations which enable relation-like treatment of BDDs
/// (quantification, selection, projection, partial element picking)
pub mod _impl_relation_ops;

/// **(internal)** Simple export functions for printing `Bdd`s as `.dot` files.
pub mod _impl_export_dot;

/// **(internal)** Implementation of the string and byte serialisation procedures for `Bdd`s.
pub mod _impl_serialisation;

/// **(internal)** Implementation of some basic internal utility methods for `Bdd`s.
pub mod _impl_util;

/// **(internal)** Implementation of some utility methods for extracting interesting
/// valuations and paths from a `Bdd`.
pub mod _impl_valuation_utils;

/// **(internal)** An optimized implementation for creating BDD from DNF.
pub mod _impl_dnf;

/// **(internal)** An optimized implementation for creating BDD from CNF.
pub mod _impl_cnf;

/// **(internal)** Implements various sorting criteria for BDD objects.
pub mod _impl_sort;

pub mod _impl_approximation;

/// **(internal)** Task is a pair of BDD pointers. These are usually pointers from two distinct
/// BDDs (standard apply algorithm), but it can also be two pointers from the same BDD ("inner"
/// apply in nested apply algorithm).
///
/// This is not public because it is just a utility structure for the apply algorithms.
#[derive(Eq, PartialEq, Hash, Copy, Clone)]
struct Task {
    left: BddPointer,
    right: BddPointer,
}
