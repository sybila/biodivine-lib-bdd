use crate::*;
use std::io::Write;

/// `.dot` export procedure for `Bdd`s.
impl Bdd {
    /// Output this `Bdd` as a `.dot` string into the given `output` writer.
    ///
    /// Variable names in the graph are resolved from the given `BddVariableSet`.
    ///
    /// If `zero_pruned` is true, edges leading to `zero` are not shown. This can greatly
    /// simplify the graph without losing information.
    pub fn write_as_dot_string(
        &self,
        output: &mut dyn Write,
        variables: &BddVariableSet,
        zero_pruned: bool,
    ) -> Result<(), std::io::Error> {
        write_bdd_as_dot(output, self, &variables.var_names, zero_pruned)
    }

    /// Convert this `Bdd` to a `.dot` string.
    ///
    /// Variable names in the graph are resolved from the given `BddVariableSet`.
    ///
    /// If `zero_pruned` is true, edges leading to `zero` are not shown. This can greatly
    /// simplify the graph without losing information.
    pub fn to_dot_string(&self, variables: &BddVariableSet, zero_pruned: bool) -> String {
        bdd_to_dot_string(self, &variables.var_names, zero_pruned)
    }
}

/// Write given `Bdd` into the output buffer as `.dot` graph. Use `var_names` to specify
/// custom names for individual variables. If `pruned` is true, the output will only
/// contain edges leading to the `1` terminal node (this is often much easier to read
/// than the full graph while preserving all the information).
fn write_bdd_as_dot(
    output: &mut dyn Write,
    bdd: &Bdd,
    var_names: &[String],
    zero_pruned: bool,
) -> Result<(), std::io::Error> {
    writeln!(output, "digraph G {{")?;
    writeln!(
        output,
        "init__ [label=\"\", style=invis, height=0, width=0];"
    )?;
    writeln!(output, "init__ -> {};", bdd.root_pointer())?;

    /*
       Fortunately, it seem that .dot does not care about ordering of graph elements,
       so we can just go through the BDD and print it as is.

       Note that for BDD slices, this can output unused nodes, but we don't support slices yet anyway.
    */

    // terminal nodes
    if !zero_pruned {
        writeln!(
            output,
            "0 [shape=box, label=\"0\", style=filled, shape=box, height=0.3, width=0.3];"
        )?;
    }
    writeln!(
        output,
        "1 [shape=box, label=\"1\", style=filled, shape=box, height=0.3, width=0.3];"
    )?;

    // decision nodes
    for node_pointer in bdd.pointers().skip(2) {
        // write the node itself
        let var_name = &var_names[bdd.var_of(node_pointer).0 as usize];
        writeln!(output, "{}[label=\"{}\"];", node_pointer, var_name)?;
        let high_link = bdd.high_link_of(node_pointer);
        if !zero_pruned || !high_link.is_zero() {
            // write "high" link
            writeln!(output, "{} -> {} [style=filled];", node_pointer, high_link)?;
        }
        let low_link = bdd.low_link_of(node_pointer);
        if !zero_pruned || !low_link.is_zero() {
            // write "low" link
            writeln!(output, "{} -> {} [style=dotted];", node_pointer, low_link)?;
        }
    }
    writeln!(output, "}}")?;
    Ok(())
}

/// Converts the given BDD to a .dot graph string using given variable names.
///
/// See also: [bdd_as_dot](fn.bdd_as_dot.html)
fn bdd_to_dot_string(bdd: &Bdd, var_names: &[String], zero_pruned: bool) -> String {
    let mut buffer: Vec<u8> = Vec::new();
    write_bdd_as_dot(&mut buffer, bdd, var_names, zero_pruned)
        .expect("Cannot write BDD to .dot string.");
    String::from_utf8(buffer).expect("Invalid UTF formatting in .dot string.")
}

#[cfg(test)]
mod tests {
    use crate::_test_util::{load_expected_results, mk_small_test_bdd};
    use crate::*;

    #[test]
    fn bdd_to_dot() {
        let bdd = mk_small_test_bdd();
        let variables = BddVariableSet::new(vec!["a", "b", "c", "d", "e"]);
        let dot = bdd.to_dot_string(&variables, false);
        assert_eq!(load_expected_results("bdd_to_dot.dot"), dot);
    }

    #[test]
    fn bdd_to_dot_pruned() {
        let variables = BddVariableSet::new(vec!["a", "b", "c", "d", "e"]);
        let bdd = mk_small_test_bdd();
        let dot = bdd.to_dot_string(&variables, true);
        assert_eq!(load_expected_results("bdd_to_dot_pruned.dot"), dot);
    }

    #[test]
    fn bdd_universe_bdd_to_dot() {
        let variables = BddVariableSet::new(vec!["a", "b", "c", "d", "e"]);
        let bdd = variables.eval_expression_string("c & !d");
        let dot = bdd.to_dot_string(&variables, false);
        assert_eq!(load_expected_results("bdd_to_dot.dot"), dot);
    }

    #[test]
    fn bdd_universe_bdd_to_dot_pruned() {
        let variables = BddVariableSet::new(vec!["a", "b", "c", "d", "e"]);
        let bdd = variables.eval_expression_string("c & !d");
        let dot = bdd.to_dot_string(&variables, true);
        assert_eq!(load_expected_results("bdd_to_dot_pruned.dot"), dot);
    }
}
