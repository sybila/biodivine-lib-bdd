use crate::{Bdd, BddVariable, BddVariableSet, IntoBdd};
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
    // Parenthesis elimination:
    ($vars:ident, ($($e:tt)*)) => { bdd!($vars, $($e)*) };
    ( ( $($e:tt)* ) ) => { bdd!($($e)*) };
    // Literal resolution:
    ($vars:ident, $bdd:literal) => { $crate::IntoBdd::into_bdd($bdd, &$vars) };
    ($vars:ident, $bdd:ident) => { $crate::IntoBdd::into_bdd($bdd, &$vars) };
    ($bdd:ident) => { $bdd };
    // Boolean operations:
    ($vars:ident, !$e:tt) => { bdd!($vars, $e).not() };
    ($vars:ident, $l:tt & $r:tt) => { bdd!($vars, $l).and(&bdd!($vars, $r)) };
    ($vars:ident, $l:tt | $r:tt) => { bdd!($vars, $l).or(&bdd!($vars, $r)) };
    ($vars:ident, $l:tt <=> $r:tt) => { bdd!($vars, $l).iff(&bdd!($vars, $r)) };
    ($vars:ident, $l:tt => $r:tt) => { bdd!($vars, $l).imp(&bdd!($vars, $r)) };
    ($vars:ident, $l:tt ^ $r:tt) => { bdd!($vars, $l).xor(&bdd!($vars, $r)) };
    (!$e:tt) => { bdd!($e).not() };
    ($l:tt & $r:tt) => { bdd!($l).and(&bdd!($r)) };
    ($l:tt | $r:tt) => { bdd!($l).or(&bdd!($r)) };
    ($l:tt <=> $r:tt) => { bdd!($l).iff(&bdd!($r)) };
    ($l:tt => $r:tt) => { bdd!($l).imp(&bdd!($r)) };
    ($l:tt ^ $r:tt) => { bdd!($l).xor(&bdd!($r)) };
}

impl IntoBdd for BddVariable {
    fn into_bdd(self, variables: &BddVariableSet) -> Bdd {
        variables.mk_var(self)
    }
}

impl IntoBdd for Bdd {
    fn into_bdd(self, _variables: &BddVariableSet) -> Bdd {
        self
    }
}

impl IntoBdd for &Bdd {
    fn into_bdd(self, _variables: &BddVariableSet) -> Bdd {
        self.clone()
    }
}

impl IntoBdd for &str {
    fn into_bdd(self, variables: &BddVariableSet) -> Bdd {
        variables.mk_var_by_name(self)
    }
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

    #[test]
    fn bdd_macro_advanced() {
        let mut builder = BddVariableSetBuilder::new();
        let [a, b, c] = builder.make(&["a", "b", "c"]);
        let variables = builder.build();
        let bdd_a = variables.mk_var(a);
        let bdd_b = variables.mk_var(b);
        let bdd_c = variables.mk_var(c);

        crate::_macro_bdd::IntoBdd::into_bdd(a, &variables);

        let with_objects = bdd!((bdd_a <=> (!bdd_b)) | (bdd_c ^ bdd_a));
        let with_variables = bdd!(variables, (a <=> (!b)) | (c ^ a));
        let with_literals = bdd!(variables, ("a" <=> (!"b")) | ("c" ^ "a"));

        assert_eq!(with_objects, with_variables);
        assert_eq!(with_variables, with_literals);
        assert_eq!(with_literals, with_objects);
    }
}
