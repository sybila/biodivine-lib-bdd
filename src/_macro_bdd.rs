/// A macro for simplifying `Bdd` operations. It evaluates given expression over `Bdd`s where
/// you can use standard boolean operators `!`, `&`, `|`, `^`, `=>` and `<=>`.
///
/// Sadly, except for the very top expression, every level needs to be enclosed
/// in parentheses since rust macros cannot parse complex expressions with
/// potential ambiguities. You can't write `x & y & z`, you have to use `(x & y) & z`.
/// Also `!x & z` is not permitted, you have to use `(!x) & z`.
///
/// See tutorial for usage examples.
#[macro_export]
macro_rules! bdd {
    ( ( $($e:tt)* ) ) => { bdd!($($e)*) };
    ( $bdd:ident ) => { $bdd };
    (!$e:tt) => { bdd!($e).not() };
    ($l:tt & $r:tt) => { bdd!($l).and(&bdd!($r)) };
    ($l:tt | $r:tt) => { bdd!($l).or(&bdd!($r)) };
    ($l:tt <=> $r:tt) => { bdd!($l).iff(&bdd!($r)) };
    ($l:tt => $r:tt) => { bdd!($l).imp(&bdd!($r)) };
    ($l:tt ^ $r:tt) => { bdd!($l).xor(&bdd!($r)) };
}

#[cfg(test)]
mod tests {
    use super::super::*;

    #[test]
    fn bdd_macro_test() {
        let variables = BddVariableSet::new_anonymous(5);
        let v1 = variables.mk_var(BddVariable(0));
        let v2 = variables.mk_var(BddVariable(1));
        assert_eq!(v1.not(), bdd!(!v1));
        assert_eq!(v1.and(&v2), bdd!(v1 & v2));
        assert_eq!(v1.or(&v2), bdd!(v1 | v2));
        assert_eq!(v1.xor(&v2), bdd!(v1 ^ v2));
        assert_eq!(v1.imp(&v2), bdd!(v1 => v2));
        assert_eq!(v1.iff(&v2), bdd!(v1 <=> v2));
    }
}
