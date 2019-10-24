//! **(internal)** Simple export functions for printing BDDs as .dot files.

use std::io::Write;
use crate::Bdd;

/// Write given BDD into the output buffer as .dot graph. Use `var_names` to specify
/// custom names for individual variables. If `pruned` is true, the output will only
/// contain edges leading to the `1` terminal node (this is often much easier to read
/// than the full graph while preserving all the information).
pub fn bdd_as_dot(
    output: &mut dyn Write,
    bdd: &Bdd,
    var_names: &Vec<String>,
    zero_pruned: bool
) -> Result<(), std::io::Error> {
    output.write_all(b"digraph G {\n")?;
    output.write_all(b"init__ [label=\"\", style=invis, height=0, width=0];\n")?;
    output.write_all(format!("init__ -> {};\n", bdd.root_pointer().0).as_bytes())?;
    /*
        Fortunately, it seem that .dot does not care about ordering of graph elements,
        so we can just go through the BDD and print it as is.

        Note that for BDD slices, this can output unused nodes, but we don't support slices yet anyway.
     */
    // terminal nodes
    if !zero_pruned {
        output.write_all(b"0 [shape=box, label=\"0\", style=filled, shape=box, height=0.3, width=0.3];\n")?;
    }
    output.write_all(b"1 [shape=box, label=\"1\", style=filled, shape=box, height=0.3, width=0.3];\n")?;
    // decision nodes
    for node_pointer in bdd.pointers().skip(2) {
        // write the node itself
        let var_name = &var_names[bdd.var_of(&node_pointer).0 as usize];
        output.write_all(format!("{}[label=\"{}\"];\n", node_pointer.0, var_name).as_bytes())?;
        let high_link = bdd.high_link_of(&node_pointer);
        if !zero_pruned || !high_link.is_zero() { // write "high" link
            output.write_all(format!("{} -> {} [style=filled];\n", node_pointer.0, high_link.0).as_bytes())?;
        }
        let low_link = bdd.low_link_of(&node_pointer);
        if !zero_pruned || !low_link.is_zero() { // write "low" link
            output.write_all(format!("{} -> {} [style=dotted];\n", node_pointer.0, low_link.0).as_bytes())?;
        }
    }
    output.write_all(b"}\n")?;
    return Result::Ok(());
}

/// Converts the given BDD to a .dot graph string using given variable names.
///
/// See also: [bdd_as_dot](fn.bdd_as_dot.html)
pub fn bdd_as_dot_string(bdd: &Bdd, var_names: &Vec<String>, zero_pruned: bool) -> String {
    let mut buffer: Vec<u8> = Vec::new();
    bdd_as_dot(&mut buffer, bdd, var_names, zero_pruned)
        .expect("Cannot write BDD to .dot string.");
    return String::from_utf8(buffer)
        .expect("Invalid UTF formatting in .dot string.");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::mk_small_test_bdd;
    use crate::BddUniverseBuilder;
    use crate::bdd;

    fn load_expected_results(test_name: &str) -> String {
        return std::fs::read_to_string(format!("test_results/{}", test_name))
            .expect("Cannot open result file.")
    }

    #[test]
    fn bdd_to_dot() {
        let bdd = mk_small_test_bdd();
        let names = vec![
            "a".to_string(), "b".to_string(), "c".to_string(), "d".to_string(), "e".to_string()
        ];
        let dot = bdd_as_dot_string(&bdd, &names, false);
        assert_eq!(load_expected_results("bdd_to_dot.dot"), dot);
    }

    #[test]
    fn bdd_to_dot_pruned() {
        let bdd = mk_small_test_bdd();
        let names = vec![
            "a".to_string(), "b".to_string(), "c".to_string(), "d".to_string(), "e".to_string()
        ];
        let dot = bdd_as_dot_string(&bdd, &names, true);
        assert_eq!(load_expected_results("bdd_to_dot_pruned.dot"), dot);
    }

    #[test]
    fn bdd_universe_bdd_to_dot() {
        let mut builder = BddUniverseBuilder::new();
        builder.make_variables(vec!["a", "b", "c", "d", "e"]);
        let universe = builder.build();
        let c = universe.mk_var(&universe.var_by_name("c").unwrap());
        let d = universe.mk_var(&universe.var_by_name("d").unwrap());
        let bdd = bdd!(universe, c & (!d));
        let dot = universe.bdd_as_dot_string(&bdd, false);
        assert_eq!(load_expected_results("bdd_to_dot.dot"), dot);
    }

    #[test]
    fn bdd_universe_bdd_to_dot_pruned() {
        let mut builder = BddUniverseBuilder::new();
        builder.make_variables(vec!["a", "b", "c", "d", "e"]);
        let universe = builder.build();
        let c = universe.mk_var(&universe.var_by_name("c").unwrap());
        let d = universe.mk_var(&universe.var_by_name("d").unwrap());
        let bdd = bdd!(universe, c & (!d));
        let dot = universe.bdd_as_dot_string(&bdd, true);
        assert_eq!(load_expected_results("bdd_to_dot_pruned.dot"), dot);
    }

}