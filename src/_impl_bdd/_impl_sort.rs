use crate::Bdd;
use std::cmp::Ordering;

impl Bdd {
    /// A comparator which orders [Bdd] objects by [Bdd::size].
    ///
    /// Also accepts BDDs with different variable counts.
    pub fn cmp_size(a: &Bdd, b: &Bdd) -> Ordering {
        a.size().cmp(&b.size())
    }

    /// A comparator which orders [Bdd] objects by [Bdd::cardinality].
    ///
    /// Also accepts BDDs with different variable counts. Just keep in mind that the maximum
    /// cardinality does depend on the number of variables.
    pub fn cmp_cardinality(a: &Bdd, b: &Bdd) -> Ordering {
        a.exact_cardinality().cmp(&b.exact_cardinality())
    }

    /// A comparator which orders [Bdd] objects by [Bdd::cardinality], but only if the two
    /// BDDs admit the same number of variables, otherwise returns `None`.
    pub fn cmp_cardinality_strict(a: &Bdd, b: &Bdd) -> Option<Ordering> {
        if a.num_vars() == b.num_vars() {
            Some(a.exact_cardinality().cmp(&b.exact_cardinality()))
        } else {
            None
        }
    }

    /// A comparator which orders [Bdd] objects based on their logical validity, meaning
    /// that `A <= B` if `A` implies `B` (The set of valid inputs for `A` is a subset of `B`).
    ///
    /// Two BDDs are only comparable if they share the same number of variables, otherwise the
    /// method returns `None`. However, two BDDs using the same variables can also be incomparable.
    /// For example, consider `a ^ b` (xor) and `a & b`. Neither `(a ^ b) => (a & b)`, nor
    /// `(a & b) => (a ^ b)` holds, hence these two functions are incomparable.
    pub fn cmp_implies(a: &Bdd, b: &Bdd) -> Option<Ordering> {
        if a.num_vars() == b.num_vars() {
            let a_implies_b = Bdd::binary_op_with_limit(2, a, b, crate::op_function::imp)
                .unwrap_or_else(|| Bdd::mk_false(a.num_vars()));
            let b_implies_a = Bdd::binary_op_with_limit(2, b, a, crate::op_function::imp)
                .unwrap_or_else(|| Bdd::mk_false(a.num_vars()));

            if a_implies_b.is_true() && b_implies_a.is_true() {
                Some(Ordering::Equal)
            } else if a_implies_b.is_true() {
                Some(Ordering::Less)
            } else if b_implies_a.is_true() {
                Some(Ordering::Greater)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// A comparator which orders [Bdd] objects based on their structure, i.e. the underlying
    /// vector of BDD nodes. It interprets each BDD as an iterator of BDD nodes, and each node
    /// as a triple of integers `(var, low, high)`. It then applies the default ordering
    /// for such data type.
    ///
    /// Note that even though all BDDs produced by this library should be stored in DFS post-order,
    /// this is technically not a formal requirement and other representations of the same BDD
    /// can be created through custom operations. In that case, logically equal BDDs would not be
    /// equal in this ordering. Furthermore, note that DFS sorting is not a very good proxy for
    /// "logical closeness".
    pub fn cmp_structural(a: &Bdd, b: &Bdd) -> Ordering {
        let a_iter = a.0.iter().map(|it| (it.var, it.low_link, it.high_link));
        let b_iter = b.0.iter().map(|it| (it.var, it.low_link, it.high_link));
        a_iter.cmp(b_iter)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Bdd, BddVariable};
    use std::cmp::Ordering;

    #[test]
    pub fn test_sort_size() {
        let tt = Bdd::mk_true(10);
        let ff = Bdd::mk_false(10);

        assert_eq!(Bdd::cmp_size(&tt, &ff), Ordering::Greater);
        assert_eq!(Bdd::cmp_size(&ff, &tt), Ordering::Less);
        assert_eq!(Bdd::cmp_size(&tt, &tt), Ordering::Equal);
    }

    #[test]
    pub fn test_sort_cardinality() {
        let tt = Bdd::mk_true(10);
        let tt_2 = Bdd::mk_true(8);
        let ff = Bdd::mk_false(10);

        assert_eq!(Bdd::cmp_cardinality(&tt, &ff), Ordering::Greater);
        assert_eq!(Bdd::cmp_cardinality(&ff, &tt), Ordering::Less);
        assert_eq!(Bdd::cmp_cardinality(&tt, &tt), Ordering::Equal);
        assert_eq!(Bdd::cmp_cardinality_strict(&tt, &tt), Some(Ordering::Equal));
        assert_eq!(Bdd::cmp_cardinality_strict(&tt, &tt_2), None);
    }

    #[test]
    pub fn test_sort_implies() {
        let tt = Bdd::mk_true(10);
        let ff = Bdd::mk_false(10);
        let var_1 = Bdd::mk_var(10, BddVariable(5));
        let var_2 = Bdd::mk_var(10, BddVariable(8));

        assert_eq!(Bdd::cmp_implies(&tt, &ff), Some(Ordering::Greater));
        assert_eq!(Bdd::cmp_implies(&ff, &tt), Some(Ordering::Less));
        assert_eq!(Bdd::cmp_implies(&tt, &tt), Some(Ordering::Equal));
        assert_eq!(
            Bdd::cmp_implies(&var_1, &(var_1.or(&var_2))),
            Some(Ordering::Less)
        );
        assert_eq!(
            Bdd::cmp_implies(&(var_1.or(&var_2)), &var_2),
            Some(Ordering::Greater)
        );
        assert_eq!(Bdd::cmp_implies(&var_1, &(var_1.xor(&var_2))), None);
        assert_eq!(Bdd::cmp_implies(&var_1, &var_1), Some(Ordering::Equal));
    }

    #[test]
    pub fn test_sort_structural() {
        let tt = Bdd::mk_true(10);
        let ff = Bdd::mk_false(10);
        let var_1 = Bdd::mk_var(10, BddVariable(5));
        let var_2 = Bdd::mk_var(10, BddVariable(8));

        assert_eq!(Bdd::cmp_structural(&ff, &tt), Ordering::Less);
        assert_eq!(Bdd::cmp_structural(&tt, &ff), Ordering::Greater);
        assert_eq!(Bdd::cmp_structural(&tt, &var_1), Ordering::Less);
        assert_eq!(Bdd::cmp_structural(&var_1, &var_2), Ordering::Less);
    }
}
