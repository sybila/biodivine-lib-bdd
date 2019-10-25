use super::*;
use super::super::tests::mk_small_test_bdd;
use super::tests::mk_universe_with_5_variables;
use crate::bdd;

fn v1() -> BddVariable { return BddVariable(0); }
fn v2() -> BddVariable { return BddVariable(1); }
fn v3() -> BddVariable { return BddVariable(2); }
fn v4() -> BddVariable { return BddVariable(3); }

#[test]
fn bdd_universe_mk_not() {
    let universe = mk_universe_with_5_variables();
    let bdd = mk_small_test_bdd();
    let tt = universe.mk_true();
    let ff = universe.mk_false();
    let mut expected = universe.mk_true();
    expected.push_node(BddNode::mk_node(
        BddVariable(3), BddPointer::zero(), BddPointer::one()
    ));
    expected.push_node(BddNode::mk_node(
        BddVariable(2), BddPointer::one(), BddPointer(2)
    ));
    assert_eq!(expected, bdd!(universe, !bdd));
    assert_eq!(bdd, bdd!(universe, !(!bdd)));
    assert_eq!(tt, bdd!(universe, !ff));
    assert_eq!(ff, bdd!(universe, !tt));
}

#[test]
fn bdd_universe_mk_and() {
    let universe = mk_universe_with_5_variables();
    let bdd = mk_small_test_bdd();  // v3 & !v4
    let v3 = universe.mk_var(&v3());
    let v4 = universe.mk_var(&v4());
    let tt = universe.mk_true();
    let ff = universe.mk_false();
    assert_eq!(bdd, bdd!(universe, v3 & (!v4)));
    assert_eq!(bdd, bdd!(universe, tt & bdd));
    assert_eq!(bdd, bdd!(universe, bdd & tt));
    assert_eq!(ff, bdd!(universe, ff & bdd));
    assert_eq!(ff, bdd!(universe, bdd & ff));
    assert_eq!(bdd, bdd!(universe, bdd & bdd));
}

#[test]
fn bdd_universe_mk_or() {
    let universe = mk_universe_with_5_variables();
    let bdd = mk_small_test_bdd();  // v3 & !v4
    let v3 = universe.mk_var(&v3());
    let v4 = universe.mk_var(&v4());
    let tt = universe.mk_true();
    let ff = universe.mk_false();
    assert_eq!(bdd, bdd!(universe, !((!v3) | v4))); // !(!v3 | v4) <=> v3 & !v4
    assert_eq!(tt, bdd!(universe, tt | bdd));
    assert_eq!(tt, bdd!(universe, bdd | tt));
    assert_eq!(bdd, bdd!(universe, ff | bdd));
    assert_eq!(bdd, bdd!(universe, bdd | ff));
    assert_eq!(bdd, bdd!(universe, bdd | bdd));
}

#[test]
fn bdd_universe_mk_xor() {
    let universe = mk_universe_with_5_variables();
    let bdd = mk_small_test_bdd();  // v3 & !v4
    let v3 = universe.mk_var(&v3());
    let v4 = universe.mk_var(&v4());
    let tt = universe.mk_true();
    let ff = universe.mk_false();

    assert_eq!(bdd!(universe, !bdd), bdd!(universe, tt ^ bdd));
    assert_eq!(bdd!(universe, !bdd), bdd!(universe, bdd ^ tt));
    assert_eq!(ff, bdd!(universe, bdd ^ bdd));
    assert_eq!(bdd, bdd!(universe, ff ^ bdd));
    assert_eq!(bdd, bdd!(universe, bdd ^ ff));
    assert_eq!(bdd, bdd!(universe, v3 & (v3 ^ v4)));
}

#[test]
fn bdd_universe_mk_imp() {
    let universe = mk_universe_with_5_variables();
    let bdd = mk_small_test_bdd();  // v3 & !v4
    let v3 = universe.mk_var(&v3());
    let v4 = universe.mk_var(&v4());
    let tt = universe.mk_true();
    let ff = universe.mk_false();

    assert_eq!(tt, bdd!(universe, ff => bdd));
    assert_eq!(bdd!(universe, !bdd), bdd!(universe, bdd => ff));
    assert_eq!(bdd, bdd!(universe, tt => bdd));
    assert_eq!(tt, bdd!(universe, bdd => tt));
    assert_eq!(tt, bdd!(universe, bdd => bdd));
    assert_eq!(bdd, bdd!(universe, !(v3 => v4)));  // !(v3 => v4) <=> v3 & !v4
}

#[test]
fn bdd_universe_mk_iff() {
    let universe = mk_universe_with_5_variables();
    let bdd = mk_small_test_bdd();  // v3 & !v4
    let v3 = universe.mk_var(&v3());
    let v4 = universe.mk_var(&v4());
    let tt = universe.mk_true();
    let ff = universe.mk_false();

    assert_eq!(bdd, bdd!(universe, bdd <=> tt));
    assert_eq!(bdd, bdd!(universe, tt <=> bdd));
    assert_eq!(bdd!(universe, !bdd), bdd!(universe, ff <=> bdd));
    assert_eq!(bdd!(universe, !bdd), bdd!(universe, bdd <=> ff));
    assert_eq!(tt, bdd!(universe, bdd <=> bdd));
    assert_eq!(bdd, bdd!(universe, v3 & (!(v4 <=> v3))));
}

#[test]
fn bdd_universe_constants() {
    let bdd = mk_universe_with_5_variables();
    let tt = bdd.mk_true();
    let ff = bdd.mk_false();
    assert!(tt.is_true());
    assert!(ff.is_false());
    assert_eq!(ff, bdd!(bdd, (tt & ff)));
    assert_eq!(tt, bdd!(bdd, (tt | ff)));
    assert_eq!(tt, bdd!(bdd, (tt ^ ff)));
    assert_eq!(ff, bdd!(bdd, (tt => ff)));
    assert_eq!(ff, bdd!(bdd, (tt <=> ff)));
}

#[test]
fn simple_identities_syntactic() {
    let bdd = mk_universe_with_5_variables();
    let a = bdd.mk_var(&v1());
    let tt = bdd.mk_true();
    let ff = bdd.mk_false();

    assert_eq!(ff, bdd!(bdd, (ff & a)));
    assert_eq!(a, bdd!(bdd, (ff | a)));
    assert_eq!(tt, bdd!(bdd, (ff => a)));
    assert_eq!(bdd!(bdd, !a), bdd!(bdd, (a => ff)));
    assert_eq!(tt, bdd!(bdd, (a => a)));
}

#[test]
fn bdd_universe_de_morgan() {
    // !(a * b * !c) <=> (!a + !b + c)
    let bdd = mk_universe_with_5_variables();
    let v1 = bdd.mk_var(&v1());
    let v2 = bdd.mk_var(&v2());
    let v3 = bdd.mk_var(&v3());

    let left = bdd!(bdd, !(v1 & (v2 & (!v3))));
    let right = bdd!(bdd, ((!v1) | (!v2)) | v3);

    assert_eq!(left, right);
    assert!(bdd!(bdd, left <=> right).is_true());
}

#[test]
fn nontrivial_identity_syntactic() {
    // dnf (!a * !b * !c) + (!a * !b * c) + (!a * b * c) + (a * !b * c) + (a * b * !c)
    //                                    <=>
    // cnf            !(!a * b * !c) * !(a * !b * !c) * !(a * b * c)
    let bdd = mk_universe_with_5_variables();
    let a = bdd.mk_var(&v1());
    let b = bdd.mk_var(&v2());
    let c = bdd.mk_var(&v3());

    let d1 = bdd!(bdd, ((!a) & (!b)) & (!c));
    let d2 = bdd!(bdd, ((!a) & (!b)) & c);
    let d3 = bdd!(bdd, ((!a) & b) & c);
    let d4 = bdd!(bdd, (a & (!b)) & c);
    let d5 = bdd!(bdd, (a & b) & (!c));

    let c1 = bdd!(bdd, (a | (!b)) | c);
    let c2 = bdd!(bdd, ((!a) | b) | c);
    let c3 = bdd!(bdd, ((!a) | (!b)) | (!c));

    let cnf = bdd!(bdd, ((c1 & c2) & c3));
    let dnf = bdd!(bdd, ((((d1 | d2) | d3) | d4) | d5));

    assert_eq!(cnf, dnf);
    assert!(bdd!(bdd, (cnf <=> dnf)).is_true());
}
