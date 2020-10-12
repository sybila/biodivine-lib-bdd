use crate::_test_util::{mk_5_variable_set, mk_small_test_bdd};

#[test]
fn bdd_projection_trivial() {
    let variables = mk_5_variable_set();
    let bdd = mk_small_test_bdd(); // v_3 && !v_4
    let tt = variables.mk_true();
    let ff = variables.mk_false();

    for k in 0..10 {
        assert_eq!(ff, ff.projection(k));
        assert_eq!(tt, tt.projection(k));
    }

    assert_eq!(tt, bdd.projection(0));
    assert_eq!(bdd, bdd.projection(10));
}

#[test]
fn bdd_projection_simple() {
    let variables = mk_5_variable_set();
    {
        let bdd = variables.eval_expression_string("(v1 <=> v2) & (v4 <=> v5)");
        let projected = variables.eval_expression_string("(v1 <=> v2)");
        assert_eq!(projected, bdd.projection(2));
        assert_eq!(bdd.projection(2), bdd.projection(3));
    }
    {
        let bdd = variables.eval_expression_string("(v4 => (v1 & v2)) & (!v4 => (!v1 & v3))");
        let projected_3 = variables.eval_expression_string("(v1 & v2) | (!v1 & v3)");
        let projected_2 = variables.eval_expression_string("(v1 & v2) | !v1");
        assert_eq!(bdd, bdd.projection(4));
        assert_eq!(projected_3, bdd.projection(3));
        assert_eq!(projected_2, bdd.projection(2));
        assert_eq!(variables.mk_true(), bdd.projection(1));
    }
}
