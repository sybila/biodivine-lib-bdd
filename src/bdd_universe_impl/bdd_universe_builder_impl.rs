use super::super::bdd_expression_parser::NOT_IN_VAR_NAME;
use crate::{BddUniverse, BddVariable};
use std::collections::{HashMap, HashSet};

/// BDD universe builder is used to safely create BDD universes.
pub struct BddUniverseBuilder {
    var_names: Vec<String>,
    var_names_set: HashSet<String>,
}

impl BddUniverseBuilder {
    /// Create a new builder without any variables.
    pub fn new() -> BddUniverseBuilder {
        return BddUniverseBuilder {
            var_names: Vec::new(),
            var_names_set: HashSet::new(),
        };
    }

    /// Create a new variable with the given `name`. Returns a BDD variable
    /// instance that can be later used to create and query actual BDDs.
    ///
    /// *Panics*:
    ///  - Each variable name has to be unique.
    ///  - Currently, there can be at most 65535 variables.
    pub fn make_variable(&mut self, name: &str) -> BddVariable {
        let new_variable_id = self.var_names.len();
        if new_variable_id >= (std::u16::MAX - 1) as usize {
            panic!(
                "BDD universe is too large. There can be at most {} variables.",
                std::u16::MAX - 1
            )
        }
        if self.var_names_set.contains(name) {
            panic!("BDD variable {} already exists.", name);
        }
        if name.chars().any(|c| NOT_IN_VAR_NAME.contains(&c)) {
            panic!(
                "Variable name {} is invalid. Cannot use {:?}",
                name, NOT_IN_VAR_NAME
            );
        }
        self.var_names_set.insert(name.to_string());
        self.var_names.push(name.to_string());
        return BddVariable(new_variable_id as u16);
    }

    /// Similar to make_variable, but allows creating multiple variables at the same time.
    pub fn make_variables(&mut self, names: Vec<&str>) -> Vec<BddVariable> {
        return names
            .into_iter()
            .map(|name| self.make_variable(name))
            .collect();
    }

    /// Convert this builder to an actual BDD worker.
    pub fn build(self) -> BddUniverse {
        let mut mapping: HashMap<String, u16> = HashMap::new();
        for name_index in 0..self.var_names.len() {
            let name = self.var_names[name_index].clone();
            mapping.insert(name, name_index as u16);
        }
        return BddUniverse {
            num_vars: self.var_names.len() as u16,
            var_names: self.var_names,
            var_index_mapping: mapping,
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn bdd_universe_builder_too_large() {
        let mut builder = BddUniverseBuilder::new();
        for i in 0..std::u16::MAX {
            builder.make_variable(&format!("v{}", i));
        }
    }

    #[test]
    #[should_panic]
    fn bdd_universe_builder_duplicate_variable() {
        let mut builder = BddUniverseBuilder::new();
        builder.make_variable("var1");
        builder.make_variable("var1");
    }

    #[test]
    fn bdd_universe_builder() {
        let mut builder = BddUniverseBuilder::new();
        let v1 = builder.make_variable("v1");
        let v2 = builder.make_variable("v2");
        let v3 = builder.make_variable("v3");
        let universe = builder.build();
        assert_eq!(3, universe.num_vars());
        assert_eq!(Some(v1), universe.var_by_name("v1"));
        assert_eq!(Some(v2), universe.var_by_name("v2"));
        assert_eq!(Some(v3), universe.var_by_name("v3"));
        assert_eq!(None, universe.var_by_name("v4"));
    }

    #[test]
    fn bdd_universe_builder_batch() {
        let mut builder = BddUniverseBuilder::new();
        let vars = builder.make_variables(vec!["v1", "v2", "v3"]);
        let universe = builder.build();
        assert_eq!(3, universe.num_vars());
        assert_eq!(Some(vars[0]), universe.var_by_name("v1"));
        assert_eq!(Some(vars[1]), universe.var_by_name("v2"));
        assert_eq!(Some(vars[2]), universe.var_by_name("v3"));
        assert_eq!(None, universe.var_by_name("v4"));
    }

    #[test]
    #[should_panic]
    fn bdd_universe_builder_invalid_name() {
        let mut builder = BddUniverseBuilder::new();
        builder.make_variable("a^b");
    }

}
