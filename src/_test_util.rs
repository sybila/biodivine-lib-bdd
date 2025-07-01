use super::*;

/// A small BDD over variables $v_1, v_2, v_3, v_4, v_5$ corresponding to the formula $(v_3 \land \neg v_4)$
pub fn mk_small_test_bdd() -> Bdd {
    let mut bdd = Bdd::mk_true(5);
    bdd.push_node(BddNode::mk_node(
        BddVariable(3), // !v4
        BddPointer::one(),
        BddPointer::zero(),
    ));
    bdd.push_node(BddNode::mk_node(
        BddVariable(2), // v3
        BddPointer::zero(),
        bdd.root_pointer(),
    ));
    bdd
}

/// Make a new `BddVariableSet` with variables $v_1, v_2, v_3, v_4, v_5$.
pub fn mk_5_variable_set() -> BddVariableSet {
    BddVariableSet::new(&["v1", "v2", "v3", "v4", "v5"])
}

pub fn load_expected_results(test_name: &str) -> String {
    std::fs::read_to_string(format!("res/test_results/{test_name}"))
        .expect("Cannot open result file.")
}
