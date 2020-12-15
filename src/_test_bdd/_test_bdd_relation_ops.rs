use crate::_test_util::{mk_5_variable_set, mk_small_test_bdd};
use crate::{Bdd, BddVariable};

fn vars() -> (
    BddVariable,
    BddVariable,
    BddVariable,
    BddVariable,
    BddVariable,
) {
    return (
        BddVariable(0),
        BddVariable(1),
        BddVariable(2),
        BddVariable(3),
        BddVariable(4),
    );
}

#[test]
fn bdd_var_projection() {
    let variables = mk_5_variable_set();
    let bdd = variables.eval_expression_string("(v1 => (v2 <=> v3)) & (!v1 => !(v2 <=> v5))");
    let v1 = BddVariable(0);
    assert_eq!(
        bdd.var_project(v1),
        variables.eval_expression_string("(v2 <=> v3) | !(v2 <=> v5)")
    );
}

#[test]
fn bdd_var_pick() {
    let variables = mk_5_variable_set();
    let bdd = variables.eval_expression_string("(v1 => (v2 <=> v3)) & (!v1 => !(v2 <=> v5))");
    let v1 = BddVariable(0);
    assert_eq!(
        bdd.var_pick(v1),
        variables
            .eval_expression_string("(v1 => ((v2 <=> v3) & (v3 <=> v5))) & (!v1 => !(v2 <=> v5))")
    );
}

#[test]
fn bdd_var_select() {
    let variables = mk_5_variable_set();
    let bdd = variables.eval_expression_string("(v1 => (v2 <=> v3)) & (!v1 => !(v2 <=> v5))");
    let v1 = BddVariable(0);
    assert_eq!(
        variables.eval_expression_string("v1 & (v2 <=> v3)"),
        bdd.var_select(v1, true)
    );
    assert_eq!(
        variables.eval_expression_string("!v1 & !(v2 <=> v5)"),
        bdd.var_select(v1, false)
    );
}

#[test]
fn bdd_projection_trivial() {
    let variables = mk_5_variable_set();
    let bdd = mk_small_test_bdd(); // v_3 && !v_4
    let tt = variables.mk_true();
    let ff = variables.mk_false();

    let vars = (0..5).map(BddVariable).collect::<Vec<_>>();
    for k in 0..5 {
        assert_eq!(ff, ff.project(&vars[0..k]));
        assert_eq!(tt, tt.project(&vars[0..k]));
    }

    assert_eq!(bdd, bdd.project(&Vec::new()));
    assert_eq!(tt, bdd.project(&vars));
}

#[test]
fn bdd_projection_simple() {
    let variables = mk_5_variable_set();
    let (_, v2, v3, v4, v5) = vars();
    {
        let bdd = variables.eval_expression_string("(v1 <=> v2) & (v4 <=> v5)");
        let projected = variables.eval_expression_string("(v1 <=> v2)");
        assert_eq!(projected, bdd.project(&vec![v4, v5]));
        assert_eq!(bdd.project(&vec![v3, v4, v5]), bdd.project(&vec![v4, v5]));
    }
    {
        let bdd = variables.eval_expression_string("(v4 => (v1 & v2)) & (!v4 => (!v1 & v3))");
        let projected_3 = variables.eval_expression_string("(v1 & v2) | (!v1 & v3)");
        let projected_2 = variables.eval_expression_string("(v1 & v2) | !v1");
        assert_eq!(bdd, bdd.project(&vec![v5]));
        assert_eq!(projected_3, bdd.project(&vec![v4]));
        assert_eq!(projected_2, bdd.project(&vec![v3, v4]));
        assert_eq!(variables.mk_true(), bdd.project(&vec![v2, v3, v4]));
    }
}

#[test]
fn bdd_pick_trivial() {
    let variables = mk_5_variable_set();
    let bdd = mk_small_test_bdd(); // v_3 && !v_4
    let tt = variables.mk_true();
    let ff = variables.mk_false();
    let (v1, v2, v3, v4, v5) = vars();

    assert_eq!(ff, ff.pick(&vec![v2, v3, v4]));
    assert_eq!(ff, ff.pick(&vec![]));

    assert_eq!(tt, tt.pick(&vec![]));
    let expected = variables.eval_expression_string("!v1 & !v2 & !v3 & !v4 & !v5");
    assert_eq!(expected, tt.pick(&vec![v1, v2, v3, v4, v5]));
    let expected = variables.eval_expression_string("!v4 & !v5");
    assert_eq!(expected, tt.pick(&vec![v4, v5]));

    assert_eq!(bdd, bdd.pick(&vec![]));
    let expected = variables.eval_expression_string("!v1 & !v2 & v3 & !v4 & !v5");
    assert_eq!(expected, bdd.pick(&vec![v1, v2, v3, v4, v5]));
    let expected = variables.eval_expression_string("v3 & !v4 & !v5");
    assert_eq!(expected, bdd.pick(&vec![v4, v5]));
}

#[test]
fn bdd_pick_simple() {
    let variables = mk_5_variable_set();
    let bdd = variables.eval_expression_string("(v1 => (v4 <=> v5)) & (!v1 => !(v4 <=> v5))");
    let expected = variables.eval_expression_string("(v1 => (!v4 & !v5)) & (!v1 => (!v4 & v5))");
    let (v1, v2, v3, v4, v5) = vars();
    assert_eq!(expected, bdd.pick(&vec![v4, v5]));
    assert_eq!(bdd, bdd.pick(&vec![v5]));

    let bdd = variables.eval_expression_string("(v1 <=> v5) & (v2 => v4) & (v3 ^ v2)");
    let witness_bdd: Bdd = variables.eval_expression_string("!v1 & !v2 & v3 & !v4 & !v5");
    assert_eq!(witness_bdd, bdd.pick(&vec![v1, v2, v3, v4, v5]));
    let expected = variables
        .eval_expression_string("(v1 => (!v2 & v3 & !v4 & v5)) & (!v1 => (!v2 & v3 & !v4 & !v5))");
    assert_eq!(expected, bdd.pick(&vec![v2, v3, v4, v5]));
    let expected = variables.eval_expression_string("((v1 & v2) => (!v3 & v4 & v5)) & ((v1 & !v2) => (v3 & !v4 & v5)) & ((!v1 & v2) => (!v3 & v4 & !v5)) & ((!v1 & !v2) => (v3 & !v4 & !v5))");
    assert_eq!(expected, bdd.pick(&vec![v3, v4, v5]));
    assert_eq!(expected, bdd.pick(&vec![v4, v5])); // accidentally, this works out
    assert_eq!(bdd, bdd.pick(&vec![v5]));
    assert_eq!(bdd, bdd.pick(&vec![]));
}

#[test]
fn bdd_select() {
    let variables = mk_5_variable_set();
    let bdd = variables.eval_expression_string("(v1 => (v4 <=> v5)) & (!v1 => !(v4 <=> v5))");
    let expected = variables.eval_expression_string("v1 & !v3 & !v4 & !v5");
    let (v1, _, v3, v4, _) = vars();
    assert_eq!(
        expected,
        bdd.select(&vec![(v1, true), (v4, false), (v3, false)])
    );
}
