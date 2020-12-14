use crate::_test_util::{mk_5_variable_set, mk_small_test_bdd};
use crate::*;

fn v1() -> BddVariable {
    return BddVariable(0);
}
fn v2() -> BddVariable {
    return BddVariable(1);
}
fn v3() -> BddVariable {
    return BddVariable(2);
}
fn v4() -> BddVariable {
    return BddVariable(3);
}

#[test]
fn bdd_not_preserves_equivalence() {
    let variables = mk_5_variable_set();
    let a = variables.mk_var(v1());
    let not_a = variables.mk_not_var(v1());
    let b = variables.mk_var(v2());
    let not_b = variables.mk_not_var(v2());
    assert_eq!(a.not(), not_a);
    assert_eq!(bdd!(!(a & not_b)), bdd!(not_a | b));
}

#[test]
fn bdd_flip_preserves_equivalence() {
    let variables = mk_5_variable_set();
    let a = variables.mk_var(v1());
    let b = variables.mk_var(v2());
    let c = variables.mk_var(v3());
    let native = bdd!(((!a) => c) & (a => b));
    let left = bdd!((!a) => b);
    let right = bdd!(a => c);
    let inverted = Bdd::fused_binary_flip_op(
        (&left, None),
        (&right, None),
        Some(v1()),
        crate::op_function::and,
    );
    assert!(native.iff(&inverted).is_true());
    assert_eq!(native, inverted);
}

#[test]
fn bdd_mk_not() {
    let variables = mk_5_variable_set();
    let bdd = mk_small_test_bdd();
    let tt = variables.mk_true();
    let ff = variables.mk_false();
    let mut expected = variables.mk_true();
    expected.push_node(BddNode::mk_node(
        BddVariable(3),
        BddPointer::zero(),
        BddPointer::one(),
    ));
    expected.push_node(BddNode::mk_node(
        BddVariable(2),
        BddPointer::one(),
        BddPointer::from_index(2),
    ));
    assert_eq!(expected, bdd!(!bdd));
    assert_eq!(bdd, bdd!(!(!bdd)));
    assert_eq!(tt, bdd!(!ff));
    assert_eq!(ff, bdd!(!tt));
}

#[test]
fn bdd_mk_and() {
    let variables = mk_5_variable_set();
    let bdd = mk_small_test_bdd(); // v3 & !v4
    let v3 = variables.mk_var(v3());
    let v4 = variables.mk_var(v4());
    let tt = variables.mk_true();
    let ff = variables.mk_false();
    assert_eq!(bdd, bdd!(v3 & (!v4)));
    assert_eq!(bdd, bdd!(tt & bdd));
    assert_eq!(bdd, bdd!(bdd & tt));
    assert_eq!(ff, bdd!(ff & bdd));
    assert_eq!(ff, bdd!(bdd & ff));
    assert_eq!(bdd, bdd!(bdd & bdd));
}

#[test]
fn bdd_mk_or() {
    let variables = mk_5_variable_set();
    let bdd = mk_small_test_bdd(); // v3 & !v4
    let v3 = variables.mk_var(v3());
    let v4 = variables.mk_var(v4());
    let tt = variables.mk_true();
    let ff = variables.mk_false();
    assert_eq!(bdd, bdd!(!((!v3) | v4))); // !(!v3 | v4) <=> v3 & !v4
    assert_eq!(tt, bdd!(tt | bdd));
    assert_eq!(tt, bdd!(bdd | tt));
    assert_eq!(bdd, bdd!(ff | bdd));
    assert_eq!(bdd, bdd!(bdd | ff));
    assert_eq!(bdd, bdd!(bdd | bdd));
}

#[test]
fn bdd_mk_xor() {
    let variables = mk_5_variable_set();
    let bdd = mk_small_test_bdd(); // v3 & !v4
    let v3 = variables.mk_var(v3());
    let v4 = variables.mk_var(v4());
    let tt = variables.mk_true();
    let ff = variables.mk_false();

    assert_eq!(bdd!(!bdd), bdd!(tt ^ bdd));
    assert_eq!(bdd!(!bdd), bdd!(bdd ^ tt));
    assert_eq!(ff, bdd!(bdd ^ bdd));
    assert_eq!(bdd, bdd!(ff ^ bdd));
    assert_eq!(bdd, bdd!(bdd ^ ff));
    assert_eq!(bdd, bdd!(v3 & (v3 ^ v4)));
}

#[test]
fn bdd_mk_imp() {
    let variables = mk_5_variable_set();
    let bdd = mk_small_test_bdd(); // v3 & !v4
    let v3 = variables.mk_var(v3());
    let v4 = variables.mk_var(v4());
    let tt = variables.mk_true();
    let ff = variables.mk_false();

    assert_eq!(tt, bdd!(ff => bdd));
    assert_eq!(bdd!(!bdd), bdd!(bdd => ff));
    assert_eq!(bdd, bdd!(tt => bdd));
    assert_eq!(tt, bdd!(bdd => tt));
    assert_eq!(tt, bdd!(bdd => bdd));
    assert_eq!(bdd, bdd!(!(v3 => v4))); // !(v3 => v4) <=> v3 & !v4
}

#[test]
fn bdd_mk_and_not() {
    let variables = mk_5_variable_set();
    let bdd = mk_small_test_bdd();
    let not_bdd = bdd.not();
    let v3 = variables.mk_var(v3());
    let v4 = variables.mk_var(v4());
    let tt = variables.mk_true();
    let ff = variables.mk_false();

    assert_eq!(bdd, v3.and_not(&v4));
    assert_eq!(not_bdd, tt.and_not(&bdd));
    assert_eq!(ff, bdd.and_not(&tt));
    assert_eq!(ff, ff.and_not(&bdd));
    assert_eq!(bdd, bdd.and_not(&ff));
}

#[test]
fn bdd_mk_iff() {
    let variables = mk_5_variable_set();
    let bdd = mk_small_test_bdd(); // v3 & !v4
    let v3 = variables.mk_var(v3());
    let v4 = variables.mk_var(v4());
    let tt = variables.mk_true();
    let ff = variables.mk_false();

    assert_eq!(bdd, bdd!(bdd <=> tt));
    assert_eq!(bdd, bdd!(tt <=> bdd));
    assert_eq!(bdd!(!bdd), bdd!(ff <=> bdd));
    assert_eq!(bdd!(!bdd), bdd!(bdd <=> ff));
    assert_eq!(tt, bdd!(bdd <=> bdd));
    assert_eq!(bdd, bdd!(v3 & (!(v4 <=> v3))));
}

#[test]
fn bdd_constants() {
    let variables = mk_5_variable_set();
    let tt = variables.mk_true();
    let ff = variables.mk_false();
    assert!(tt.is_true());
    assert!(ff.is_false());
    assert_eq!(ff, bdd!((tt & ff)));
    assert_eq!(tt, bdd!((tt | ff)));
    assert_eq!(tt, bdd!((tt ^ ff)));
    assert_eq!(ff, bdd!((tt => ff)));
    assert_eq!(ff, bdd!((tt <=> ff)));
}

#[test]
fn simple_identities_syntactic() {
    let variables = mk_5_variable_set();
    let a = variables.mk_var(v1());
    let tt = variables.mk_true();
    let ff = variables.mk_false();

    assert_eq!(ff, bdd!((ff & a)));
    assert_eq!(a, bdd!((ff | a)));
    assert_eq!(tt, bdd!((ff => a)));
    assert_eq!(bdd!(!a), bdd!((a => ff)));
    assert_eq!(tt, bdd!((a => a)));
}

#[test]
fn bdd_de_morgan() {
    // !(a * b * !c) <=> (!a + !b + c)
    let variables = mk_5_variable_set();
    let v1 = variables.mk_var(v1());
    let v2 = variables.mk_var(v2());
    let v3 = variables.mk_var(v3());

    let left = bdd!(!(v1 & (v2 & (!v3))));
    let right = bdd!(((!v1) | (!v2)) | v3);

    assert_eq!(left, right);
    assert!(bdd!(left <=> right).is_true());
}

#[test]
fn nontrivial_identity_syntactic() {
    // dnf (!a * !b * !c) + (!a * !b * c) + (!a * b * c) + (a * !b * c) + (a * b * !c)
    //                                    <=>
    // cnf            !(!a * b * !c) * !(a * !b * !c) * !(a * b * c)
    let variables = mk_5_variable_set();
    let a = variables.mk_var(v1());
    let b = variables.mk_var(v2());
    let c = variables.mk_var(v3());

    let d1 = bdd!(((!a) & (!b)) & (!c));
    let d2 = bdd!(((!a) & (!b)) & c);
    let d3 = bdd!(((!a) & b) & c);
    let d4 = bdd!((a & (!b)) & c);
    let d5 = bdd!((a & b) & (!c));

    let c1 = bdd!((a | (!b)) | c);
    let c2 = bdd!(((!a) | b) | c);
    let c3 = bdd!(((!a) | (!b)) | (!c));

    let cnf = bdd!(((c1 & c2) & c3));
    let dnf = bdd!(((((d1 | d2) | d3) | d4) | d5));

    assert_eq!(cnf, dnf);
    assert!(bdd!((cnf <=> dnf)).is_true());
    assert_eq!(20.0, cnf.cardinality());
}

#[test]
fn invert_input() {
    let variables = mk_5_variable_set();
    let (var1, var2, var3, var4) = (v1(), v2(), v3(), v4());
    let v1 = variables.mk_var(v1());
    let v2 = variables.mk_var(v2());
    let v3 = variables.mk_var(v3());

    let original: Bdd = bdd!(!(v1 & (v2 & (!v3))));
    let invert_v1: Bdd = bdd!(!((!v1) & (v2 & (!v3))));
    let invert_v2: Bdd = bdd!(!(v1 & ((!v2) & (!v3))));
    let invert_v3: Bdd = bdd!(!(v1 & (v2 & v3)));

    assert!(Bdd::fused_binary_flip_op(
        (&invert_v1, None),
        (&original, Some(var1)),
        None,
        crate::op_function::iff
    )
    .is_true());
    assert!(Bdd::fused_binary_flip_op(
        (&original, Some(var2)),
        (&invert_v2, None),
        None,
        crate::op_function::iff
    )
    .is_true());
    assert!(Bdd::fused_binary_flip_op(
        (&invert_v3, None),
        (&original, Some(var3)),
        None,
        crate::op_function::iff
    )
    .is_true());
    assert!(Bdd::fused_binary_flip_op(
        (&original, Some(var4)),
        (&original, None),
        None,
        crate::op_function::iff
    )
    .is_true());
}
