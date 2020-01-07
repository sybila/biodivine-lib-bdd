//! **(internal)** Simple export functions for printing BDDs as .dot files.

use crate::Bdd;
use std::io::Write;

/// Write given BDD into the output buffer as .dot graph. Use `var_names` to specify
/// custom names for individual variables. If `pruned` is true, the output will only
/// contain edges leading to the `1` terminal node (this is often much easier to read
/// than the full graph while preserving all the information).
pub fn write_bdd_as_dot(
    output: &mut dyn Write,
    bdd: &Bdd,
    var_names: &Vec<String>,
    zero_pruned: bool,
) -> Result<(), std::io::Error> {
    write!(output, "digraph G {{\n")?;
    write!(
        output,
        "init__ [label=\"\", style=invis, height=0, width=0];\n"
    )?;
    write!(output, "init__ -> {};\n", bdd.root_pointer())?;

    /*
       Fortunately, it seem that .dot does not care about ordering of graph elements,
       so we can just go through the BDD and print it as is.

       Note that for BDD slices, this can output unused nodes, but we don't support slices yet anyway.
    */

    // terminal nodes
    if !zero_pruned {
        write!(
            output,
            "0 [shape=box, label=\"0\", style=filled, shape=box, height=0.3, width=0.3];\n"
        )?;
    }
    write!(
        output,
        "1 [shape=box, label=\"1\", style=filled, shape=box, height=0.3, width=0.3];\n"
    )?;

    // decision nodes
    for node_pointer in bdd.pointers().skip(2) {
        // write the node itself
        let var_name = &var_names[bdd.var_of(node_pointer).0 as usize];
        write!(output, "{}[label=\"{}\"];\n", node_pointer, var_name)?;
        let high_link = bdd.high_link_of(node_pointer);
        if !zero_pruned || !high_link.is_zero() {
            // write "high" link
            write!(
                output,
                "{} -> {} [style=filled];\n",
                node_pointer, high_link
            )?;
        }
        let low_link = bdd.low_link_of(node_pointer);
        if !zero_pruned || !low_link.is_zero() {
            // write "low" link
            write!(output, "{} -> {} [style=dotted];\n", node_pointer, low_link)?;
        }
    }
    write!(output, "}}\n")?;
    return Result::Ok(());
}

/// Converts the given BDD to a .dot graph string using given variable names.
///
/// See also: [bdd_as_dot](fn.bdd_as_dot.html)
pub fn bdd_to_dot_string(bdd: &Bdd, var_names: &Vec<String>, zero_pruned: bool) -> String {
    let mut buffer: Vec<u8> = Vec::new();
    write_bdd_as_dot(&mut buffer, bdd, var_names, zero_pruned)
        .expect("Cannot write BDD to .dot string.");
    return String::from_utf8(buffer).expect("Invalid UTF formatting in .dot string.");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::{load_expected_results, mk_small_test_bdd};
    use crate::BddUniverse;

    #[test]
    fn bdd_to_dot() {
        let bdd = mk_small_test_bdd();
        let names: Vec<String> = vec!["a".into(), "b".into(), "c".into(), "d".into(), "e".into()];
        let dot = bdd_to_dot_string(&bdd, &names, false);
        assert_eq!(load_expected_results("bdd_to_dot.dot"), dot);
    }

    #[test]
    fn bdd_to_dot_pruned() {
        let bdd = mk_small_test_bdd();
        let names: Vec<String> = vec!["a".into(), "b".into(), "c".into(), "d".into(), "e".into()];
        let dot = bdd_to_dot_string(&bdd, &names, true);
        assert_eq!(load_expected_results("bdd_to_dot_pruned.dot"), dot);
    }

    #[test]
    fn bdd_universe_bdd_to_dot() {
        let universe = BddUniverse::new(vec!["a", "b", "c", "d", "e"]);
        let bdd = universe.eval_expression("c & !d");
        let dot = universe.bdd_to_dot_string(&bdd, false);
        assert_eq!(load_expected_results("bdd_to_dot.dot"), dot);
    }

    #[test]
    fn bdd_universe_bdd_to_dot_pruned() {
        let universe = BddUniverse::new(vec!["a", "b", "c", "d", "e"]);
        let bdd = universe.eval_expression("c & !d");
        let dot = universe.bdd_to_dot_string(&bdd, true);
        assert_eq!(load_expected_results("bdd_to_dot_pruned.dot"), dot);
    }
}
