use crate::_test_util::{mk_5_variable_set, mk_small_test_bdd};
use crate::{Bdd, BddVariable};
use rand::rngs::StdRng;
use rand::SeedableRng;

fn vars() -> (
    BddVariable,
    BddVariable,
    BddVariable,
    BddVariable,
    BddVariable,
) {
    (
        BddVariable(0),
        BddVariable(1),
        BddVariable(2),
        BddVariable(3),
        BddVariable(4),
    )
}

#[test]
fn bdd_restrict() {
    let variables = mk_5_variable_set();
    let var_a = variables.var_by_name("v1").unwrap();
    let var_b = variables.var_by_name("v2").unwrap();
    let a = variables.mk_var(var_a);
    let b = variables.mk_var(var_b);
    let a_xor_b = variables.eval_expression_string("v1 ^ v2");
    let a_or_b = variables.eval_expression_string("v1 | v2");
    let a_and_b = variables.eval_expression_string("v1 & v2");

    assert_eq!(a.not(), a_xor_b.var_restrict(var_b, true));
    assert_eq!(b, a_xor_b.var_restrict(var_a, false));
    assert_eq!(a, a_or_b.var_restrict(var_b, false));
    assert!(a_or_b.var_restrict(var_b, true).is_true());
    assert_eq!(a, a_and_b.var_restrict(var_b, true));
    assert!(a_and_b.var_restrict(var_b, false).is_false());

    assert!(a_xor_b.restrict(&[(var_a, true), (var_b, false)]).is_true());
    assert!(a_and_b
        .restrict(&[(var_a, true), (var_b, false)])
        .is_false());
    assert!(a_or_b.restrict(&[(var_a, true), (var_b, false)]).is_true());
}

#[test]
fn bdd_var_exists() {
    let variables = mk_5_variable_set();
    let bdd = variables.eval_expression_string("(v1 => (v2 <=> v3)) & (!v1 => !(v2 <=> v5))");
    let v1 = BddVariable(0);
    assert_eq!(
        bdd.var_exists(v1),
        variables.eval_expression_string("(v2 <=> v3) | !(v2 <=> v5)")
    );
    #[allow(deprecated)]
    {
        assert_eq!(
            bdd.var_project(v1),
            variables.eval_expression_string("(v2 <=> v3) | !(v2 <=> v5)")
        );
    }
}

#[test]
fn bdd_var_for_all() {
    let variables = mk_5_variable_set();
    let bdd = variables.eval_expression_string("(v1 => (v2 <=> v3)) & (!v1 => !(v2 <=> v5))");
    let v1 = BddVariable(0);
    assert_eq!(
        bdd.var_for_all(v1),
        variables.eval_expression_string("(v2 <=> v3) & !(v2 <=> v5)")
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
fn bdd_var_pick_random() {
    let variables = mk_5_variable_set();
    let bdd = variables.eval_expression_string("(v1 => (v2 <=> v3)) & (!v1 => !(v2 <=> v5))");
    let v1 = BddVariable(0);
    let mut random = StdRng::seed_from_u64(1234567890);
    for _ in 0..10 {
        let picked = bdd.var_pick_random(v1, &mut random);
        assert_eq!(picked.and(&bdd), picked);
        let v1_true_paths = picked.var_select(v1, true).var_exists(v1);
        let v1_false_paths = picked.var_select(v1, false).var_exists(v1);
        assert!(v1_true_paths.and(&v1_false_paths).is_false());
    }
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
        assert_eq!(ff, ff.exists(&vars[0..k]));
        assert_eq!(tt, tt.exists(&vars[0..k]));
        assert_eq!(ff, ff.for_all(&vars[0..k]));
        assert_eq!(tt, tt.for_all(&vars[0..k]));
    }

    assert_eq!(bdd, bdd.exists(&[]));
    assert_eq!(bdd, bdd.for_all(&[]));
    assert_eq!(tt, bdd.exists(&vars));
    assert_eq!(ff, bdd.for_all(&vars));
}

#[test]
fn bdd_projection_simple() {
    let variables = mk_5_variable_set();
    let (_, v2, v3, v4, v5) = vars();
    {
        let bdd = variables.eval_expression_string("(v1 <=> v2) & (v4 <=> v5)");
        let not_bdd = bdd.not();
        let project_exists = variables.eval_expression_string("(v1 <=> v2)");
        assert_eq!(project_exists, bdd.exists(&[v4, v5]));
        assert_eq!(bdd.exists(&[v3, v4, v5]), bdd.exists(&[v4, v5]));

        #[allow(deprecated)]
        {
            // Test legacy implementation.
            assert_eq!(project_exists, bdd.project(&[v4, v5]));
            assert_eq!(bdd.project(&[v3, v4, v5]), bdd.project(&[v4, v5]));
        }

        // It holds that $(\exists x . \phi)$ is equivalent to $(\neg \for_all x . \neg \phi)$
        assert_eq!(project_exists.not(), not_bdd.for_all(&[v4, v5]));
        assert_eq!(not_bdd.for_all(&[v3, v4, v5]), not_bdd.for_all(&[v3, v4]));
    }
    {
        let bdd = variables.eval_expression_string("(v4 => (v1 & v2)) & (!v4 => (!v1 & v3))");
        let not_bdd = bdd.not();
        let projected_3 = variables.eval_expression_string("(v1 & v2) | (!v1 & v3)");
        let projected_2 = variables.eval_expression_string("(v1 & v2) | !v1");
        assert_eq!(bdd, bdd.exists(&[v5]));
        assert_eq!(not_bdd, not_bdd.for_all(&[v5]));

        assert_eq!(projected_3, bdd.exists(&[v4]));
        assert_eq!(projected_3.not(), not_bdd.for_all(&[v4]));

        assert_eq!(projected_2, bdd.exists(&[v3, v4]));
        assert_eq!(projected_2.not(), not_bdd.for_all(&[v3, v4]));

        assert_eq!(variables.mk_true(), bdd.exists(&[v2, v3, v4]));
        assert_eq!(variables.mk_false(), not_bdd.for_all(&[v2, v3, v4]));
    }
}

#[test]
fn bdd_pick_trivial() {
    let variables = mk_5_variable_set();
    let bdd = mk_small_test_bdd(); // v_3 && !v_4
    let tt = variables.mk_true();
    let ff = variables.mk_false();
    let (v1, v2, v3, v4, v5) = vars();

    assert_eq!(ff, ff.pick(&[v2, v3, v4]));
    assert_eq!(ff, ff.pick(&[]));

    assert_eq!(tt, tt.pick(&[]));
    let expected = variables.eval_expression_string("!v1 & !v2 & !v3 & !v4 & !v5");
    assert_eq!(expected, tt.pick(&[v1, v2, v3, v4, v5]));
    let expected = variables.eval_expression_string("!v4 & !v5");
    assert_eq!(expected, tt.pick(&[v4, v5]));

    assert_eq!(bdd, bdd.pick(&[]));
    let expected = variables.eval_expression_string("!v1 & !v2 & v3 & !v4 & !v5");
    assert_eq!(expected, bdd.pick(&[v1, v2, v3, v4, v5]));
    let expected = variables.eval_expression_string("v3 & !v4 & !v5");
    assert_eq!(expected, bdd.pick(&[v4, v5]));
}

#[test]
fn bdd_pick_simple() {
    let variables = mk_5_variable_set();
    let bdd = variables.eval_expression_string("(v1 => (v4 <=> v5)) & (!v1 => !(v4 <=> v5))");
    let expected = variables.eval_expression_string("(v1 => (!v4 & !v5)) & (!v1 => (!v4 & v5))");
    let (v1, v2, v3, v4, v5) = vars();
    assert_eq!(expected, bdd.pick(&[v4, v5]));
    assert_eq!(bdd, bdd.pick(&[v5]));

    let bdd = variables.eval_expression_string("(v1 <=> v5) & (v2 => v4) & (v3 ^ v2)");
    let witness_bdd: Bdd = variables.eval_expression_string("!v1 & !v2 & v3 & !v4 & !v5");
    assert_eq!(witness_bdd, bdd.pick(&[v1, v2, v3, v4, v5]));
    let expected = variables
        .eval_expression_string("(v1 => (!v2 & v3 & !v4 & v5)) & (!v1 => (!v2 & v3 & !v4 & !v5))");
    assert_eq!(expected, bdd.pick(&[v2, v3, v4, v5]));
    let expected = variables.eval_expression_string("((v1 & v2) => (!v3 & v4 & v5)) & ((v1 & !v2) => (v3 & !v4 & v5)) & ((!v1 & v2) => (!v3 & v4 & !v5)) & ((!v1 & !v2) => (v3 & !v4 & !v5))");
    assert_eq!(expected, bdd.pick(&[v3, v4, v5]));
    assert_eq!(expected, bdd.pick(&[v4, v5])); // accidentally, this works out
    assert_eq!(bdd, bdd.pick(&[v5]));
    assert_eq!(bdd, bdd.pick(&[]));
}

#[test]
fn bdd_pick_random() {
    let variables = mk_5_variable_set();
    let bdd = variables.eval_expression_string("(v1 => (v4 <=> v5)) & (!v1 => !(v4 <=> v5))");
    let (_, v2, v3, _, _) = vars();

    let mut random = StdRng::seed_from_u64(1234567890);

    for _ in 0..100 {
        let picked = bdd.pick_random(&[v2, v3], &mut random);
        assert_eq!(picked.and(&bdd), picked);

        let picked_00 = picked.select(&[(v2, false), (v3, false)]).exists(&[v2, v3]);
        let picked_01 = picked.select(&[(v2, false), (v3, true)]).exists(&[v2, v3]);
        let picked_10 = picked.select(&[(v2, true), (v3, false)]).exists(&[v2, v3]);
        let picked_11 = picked.select(&[(v2, true), (v3, true)]).exists(&[v2, v3]);

        assert!(picked_00.and(&picked_01).is_false());
        assert!(picked_00.and(&picked_10).is_false());
        assert!(picked_00.and(&picked_11).is_false());
        assert!(picked_01.and(&picked_10).is_false());
        assert!(picked_01.and(&picked_11).is_false());
        assert!(picked_10.and(&picked_11).is_false());
    }
}

#[test]
fn bdd_select() {
    let variables = mk_5_variable_set();
    let bdd = variables.eval_expression_string("(v1 => (v4 <=> v5)) & (!v1 => !(v4 <=> v5))");
    let expected = variables.eval_expression_string("v1 & !v3 & !v4 & !v5");
    let (v1, _, v3, v4, _) = vars();
    assert_eq!(
        expected,
        bdd.select(&[(v1, true), (v4, false), (v3, false)])
    );
}
