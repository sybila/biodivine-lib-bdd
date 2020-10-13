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

#[test]
fn bdd_extended_witness_trivial() {
    let variables = mk_5_variable_set();
    let bdd = mk_small_test_bdd(); // v_3 && !v_4
    let tt = variables.mk_true();
    let ff = variables.mk_false();

    assert_eq!(ff, ff.extended_witness(3));
    assert_eq!(ff, ff.extended_witness(0));

    assert_eq!(tt, tt.extended_witness(5));
    let expected = variables.eval_expression_string("!v1 & !v2 & !v3 & !v4 & !v5");
    assert_eq!(expected, tt.extended_witness(0));
    let expected = variables.eval_expression_string("!v4 & !v5");
    assert_eq!(expected, tt.extended_witness(3));

    assert_eq!(bdd, bdd.extended_witness(5));
    let expected = variables.eval_expression_string("!v1 & !v2 & v3 & !v4 & !v5");
    assert_eq!(expected, bdd.extended_witness(0));
    let expected = variables.eval_expression_string("v3 & !v4 & !v5");
    assert_eq!(expected, bdd.extended_witness(3));
}

#[test]
fn bdd_extended_witness_simple() {
    let variables = mk_5_variable_set();
    let bdd = variables.eval_expression_string("(v1 => (v4 <=> v5)) & (!v1 => !(v4 <=> v5))");
    let expected = variables.eval_expression_string("(v1 => (!v4 & !v5)) & (!v1 => (!v4 & v5))");
    assert_eq!(expected, bdd.extended_witness(3));
    assert_eq!(bdd, bdd.extended_witness(4));

    let bdd = variables.eval_expression_string("(v1 <=> v5) & (v2 => v4) & (v3 ^ v2)");
    //println!("{}", bdd.to_dot_string(&variables, true));
    let expected = variables
        .eval_expression_string("(v1 => (!v2 & v3 & !v4 & v5)) & (!v1 => (!v2 & v3 & !v4 & !v5))");
    assert_eq!(expected, bdd.extended_witness(1));
    let expected = variables.eval_expression_string("((v1 & v2) => (!v3 & v4 & v5)) & ((v1 & !v2) => (v3 & !v4 & v5)) & ((!v1 & v2) => (!v3 & v4 & !v5)) & ((!v1 & !v2) => (v3 & !v4 & !v5))");
    assert_eq!(expected, bdd.extended_witness(2));
    assert_eq!(expected, bdd.extended_witness(3)); // accidentally, this works out
    assert_eq!(bdd, bdd.extended_witness(4));
    assert_eq!(bdd, bdd.extended_witness(5));
}
