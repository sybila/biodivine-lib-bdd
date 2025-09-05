use crate::_test_util::mk_5_variable_set;
use crate::op_function::and;
use crate::{Bdd, BddVariable, bdd};

fn v1() -> BddVariable {
    BddVariable(0)
}
fn v2() -> BddVariable {
    BddVariable(1)
}
fn v3() -> BddVariable {
    BddVariable(2)
}

#[test]
pub fn test_basic_limit_equalities() {
    let variables = mk_5_variable_set();
    let v1 = variables.mk_var(v1());
    let v2 = variables.mk_var(v2());
    let v3 = variables.mk_var(v3());

    let tt = variables.mk_true();
    let ff = variables.mk_false();
    let some_bdd: Bdd = bdd!(!(v1 & (v2 & (!v3))));

    // Limit works (we need at least X nodes to run "identity" on X).
    assert_eq!(None, Bdd::binary_op_with_limit(0, &some_bdd, &tt, and));
    assert_eq!(
        None,
        Bdd::binary_op_with_limit(some_bdd.size() - 1, &some_bdd, &tt, and)
    );
    assert_eq!(
        Some(some_bdd.clone()),
        Bdd::binary_op_with_limit(some_bdd.size(), &some_bdd, &tt, and)
    );

    // 1 & 1 fits into limit 2, but not 1.
    assert_eq!(
        Some(tt.clone()),
        Bdd::binary_op_with_limit(2, &tt, &tt, and)
    );
    assert_eq!(None, Bdd::binary_op_with_limit(1, &tt, &tt, and));
    // 0 & 0 fits into limit 1, but not 0.
    assert_eq!(
        Some(ff.clone()),
        Bdd::binary_op_with_limit(1, &ff, &ff, and)
    );
    assert_eq!(None, Bdd::binary_op_with_limit(0, &ff, &ff, and));
}

#[test]
pub fn test_basic_dry_run_equalities() {
    let variables = mk_5_variable_set();
    let v1 = variables.mk_var(v1());
    let v2 = variables.mk_var(v2());
    let v3 = variables.mk_var(v3());

    let tt = variables.mk_true();
    let ff = variables.mk_false();
    let some_bdd: Bdd = bdd!(!(v1 & (v2 & (!v3))));

    // To check the identity operation, we need as many tasks as is the number of non-terminal
    // BDD nodes.
    assert_eq!(None, Bdd::check_binary_op(0, &some_bdd, &tt, and));
    assert_eq!(
        None,
        Bdd::check_binary_op(some_bdd.size() - 3, &some_bdd, &tt, and)
    );
    assert_eq!(
        Some((true, some_bdd.size() - 2)),
        Bdd::check_binary_op(some_bdd.size() - 2, &some_bdd, &tt, and)
    );
    // This particular contradiction can be even handled without any tasks, because
    // it is immediately resolved by lookup on the root task.
    assert_eq!(
        Some((false, 0)),
        Bdd::check_binary_op(0, &some_bdd, &ff, and)
    );
}
