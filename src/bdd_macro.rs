//! A macro for simplifying BDD operations.

/// A macro for simplifying BDD operations. As first argument, you provide
/// a BDD universe. Second argument is an expression over BDDs where you can use
/// standard boolean operators `!`, `&`, `|`, `^`, `=>` and `<=>`. Sadly, except for
/// the very top expression, every level needs to be enclosed in parentheses since
/// rust macros cannot parse complex expressions with potential ambiguities.
///
/// Sadly, you can't write x & y & z, you have to use (x & y) & z. Also !x & z is not
/// permitted, you have to use (!x) & z.
///
/// TODO: Usage example.
#[macro_export]
macro_rules! bdd {
    ($b:ident, ( $($e:tt)* ) ) => { bdd!($b, $($e)*) };
    ($b:ident, $bdd:ident ) => { $bdd };
    ($b:ident, !$e:tt) => { $b.mk_not(&bdd!($b, $e)) };
    ($b:ident, $l:tt & $r:tt) => { $b.mk_and(&bdd!($b, $l), &bdd!($b, $r)) };
    ($b:ident, $l:tt | $r:tt) => { $b.mk_or(&bdd!($b, $l), &bdd!($b, $r)) };
    ($b:ident, $l:tt <=> $r:tt) => { $b.mk_iff(&bdd!($b, $l), &bdd!($b, $r)) };
    ($b:ident, $l:tt => $r:tt) => { $b.mk_imp(&bdd!($b, $l), &bdd!($b, $r)) };
    ($b:ident, $l:tt ^ $r:tt) => { $b.mk_xor(&bdd!($b, $l), &bdd!($b, $r)) };
}

#[cfg(test)]
mod tests {
    use crate::{BddUniverse, BddVariable};

    #[test]
    fn bdd_macro_test() {
        let universe = BddUniverse::new_anonymous(5);
        let v1 = universe.mk_var(&BddVariable(0));
        let v2 = universe.mk_var(&BddVariable(1));
        assert_eq!(universe.mk_not(&v1), bdd!(universe, !v1));
        assert_eq!(universe.mk_and(&v1, &v2), bdd!(universe, v1 & v2));
        assert_eq!(universe.mk_or(&v1, &v2), bdd!(universe, v1 | v2));
        assert_eq!(universe.mk_xor(&v1, &v2), bdd!(universe, v1 ^ v2));
        assert_eq!(universe.mk_imp(&v1, &v2), bdd!(universe, v1 => v2));
        assert_eq!(universe.mk_iff(&v1, &v2), bdd!(universe, v1 <=> v2));
    }

}
