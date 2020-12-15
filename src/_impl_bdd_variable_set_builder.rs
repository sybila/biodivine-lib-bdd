use super::*;
use std::collections::HashMap;

impl BddVariableSetBuilder {
    /// Create a new builder without any variables.
    pub fn new() -> BddVariableSetBuilder {
        BddVariableSetBuilder {
            var_names: Vec::new(),
            var_names_set: HashSet::new(),
        }
    }

    /// Create a new variable with the given `name`. Returns a `BddVariable`
    /// instance that can be later used to create and query actual BDDs.
    ///
    /// *Panics*:
    ///  - Each variable name has to be unique.
    ///  - Currently, there can be at most 65535 variables.
    ///  - The name must not contain `!`, `&`, `|`, `^`, `=`, `<`, `>`, `(` or `)`.
    pub fn make_variable(&mut self, name: &str) -> BddVariable {
        let new_variable_id = self.var_names.len();
        if new_variable_id >= (std::u16::MAX - 1) as usize {
            panic!(
                "Too many BDD variables. There can be at most {} variables.",
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
        BddVariable(new_variable_id as u16)
    }

    /// Similar to `make_variable`, but allows creating multiple variables at the same time.
    pub fn make_variables(&mut self, names: Vec<&str>) -> Vec<BddVariable> {
        names
            .into_iter()
            .map(|name| self.make_variable(name))
            .collect()
    }

    /// Convert this builder to an actual variable set.
    pub fn build(self) -> BddVariableSet {
        let mut mapping: HashMap<String, u16> = HashMap::new();
        for name_index in 0..self.var_names.len() {
            let name = self.var_names[name_index].clone();
            mapping.insert(name, name_index as u16);
        }
        BddVariableSet {
            num_vars: self.var_names.len() as u16,
            var_names: self.var_names,
            var_index_mapping: mapping,
        }
    }
}

impl Default for BddVariableSetBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn bdd_variables_builder_too_large() {
        let mut builder = BddVariableSetBuilder::new();
        for i in 0..std::u16::MAX {
            builder.make_variable(&format!("v{}", i));
        }
    }

    #[test]
    #[should_panic]
    fn bdd_variables_builder_duplicate_variable() {
        let mut builder = BddVariableSetBuilder::new();
        builder.make_variable("var1");
        builder.make_variable("var1");
    }

    #[test]
    fn bdd_variables_builder() {
        let mut builder = BddVariableSetBuilder::new();
        let v1 = builder.make_variable("v1");
        let v2 = builder.make_variable("v2");
        let v3 = builder.make_variable("v3");
        let variables = builder.build();
        assert_eq!(3, variables.num_vars());
        assert_eq!(Some(v1), variables.var_by_name("v1"));
        assert_eq!(Some(v2), variables.var_by_name("v2"));
        assert_eq!(Some(v3), variables.var_by_name("v3"));
        assert_eq!(None, variables.var_by_name("v4"));
    }

    #[test]
    fn bdd_variables_builder_batch() {
        let mut builder = BddVariableSetBuilder::new();
        let vars = builder.make_variables(vec!["v1", "v2", "v3"]);
        let variables = builder.build();
        assert_eq!(3, variables.num_vars());
        assert_eq!(Some(vars[0]), variables.var_by_name("v1"));
        assert_eq!(Some(vars[1]), variables.var_by_name("v2"));
        assert_eq!(Some(vars[2]), variables.var_by_name("v3"));
        assert_eq!(None, variables.var_by_name("v4"));
    }

    #[test]
    #[should_panic]
    fn bdd_variables_builder_invalid_name() {
        let mut builder = BddVariableSetBuilder::new();
        builder.make_variable("a^b");
    }
}
