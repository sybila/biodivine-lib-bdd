use crate::{Bdd, BddPartialValuation, BddPathIterator, BddPointer};

impl BddPathIterator<'_> {
    pub fn new(bdd: &Bdd) -> BddPathIterator {
        if bdd.is_false() {
            BddPathIterator {
                bdd,
                stack: Vec::new(),
            }
        } else {
            let mut stack = Vec::new();
            stack.push(bdd.root_pointer());
            continue_path(bdd, &mut stack); // Compute the first valid path.
            BddPathIterator { bdd, stack }
        }
    }
}

impl Iterator for BddPathIterator<'_> {
    type Item = BddPartialValuation;

    fn next(&mut self) -> Option<Self::Item> {
        if self.stack.is_empty() {
            None
        } else {
            let item = make_clause(self.bdd, &self.stack);

            // Now, we need to pop the path until we find a node with a valid successor,
            // and then extend the path using `continue_path`.

            let mut last_child = self.stack.pop().unwrap();

            while let Some(top) = self.stack.last() {
                if self.bdd.low_link_of(*top) == last_child {
                    // Try to advance to the high link.
                    if self.bdd.high_link_of(*top).is_zero() {
                        // If high link is zero, we cannot advance and have to pop.
                        last_child = *top;
                        self.stack.pop();
                    } else {
                        // This is a sanity check which prevents the method from looping on
                        // non-canonical BDDs.
                        if self.bdd.low_link_of(*top) == self.bdd.high_link_of(*top) {
                            panic!("The BDD is not canonical.");
                        }

                        let new_entry = self.bdd.high_link_of(*top);
                        self.stack.push(new_entry);
                        continue_path(self.bdd, &mut self.stack);
                        break;
                    }
                } else if self.bdd.high_link_of(*top) == last_child {
                    // Both low and high links have been processed,
                    // so we can only pop to the next node.
                    last_child = *top;
                    self.stack.pop();
                } else {
                    // Just a sanity check. This should be unreachable.
                    unreachable!("Invalid path data in iterator.");
                }
            }

            // Here, either a path was found and extended, or the stack is empty and this was
            // the last item.

            Some(item)
        }
    }
}

/// **(internal)** Given a prefix of a path in a BDD, continue the prefix, always choosing
/// the low link unless it leads to a false leaf.
///
/// The input path must be non-empty.
fn continue_path(bdd: &Bdd, path: &mut Vec<BddPointer>) {
    assert!(!path.is_empty());
    loop {
        let top = *path.last().unwrap();
        if top.is_one() {
            return;
        }

        if !bdd.low_link_of(top).is_zero() {
            path.push(bdd.low_link_of(top));
        } else if !bdd.high_link_of(top).is_zero() {
            path.push(bdd.high_link_of(top));
        } else {
            panic!("The given BDD is not canonical.");
        }
    }
}

/// **(internal)** Convert a path in a `Bdd` saved as a stack into a clause.
///
/// The path must end with a pointer to the one-terminal node.
fn make_clause(bdd: &Bdd, path: &[BddPointer]) -> BddPartialValuation {
    let mut result = BddPartialValuation::empty();
    for i in 0..(path.len() - 1) {
        let this_node = path[i];
        let next_node = path[i + 1];
        let var = bdd.var_of(this_node);

        if bdd.low_link_of(this_node) == next_node {
            result.set_value(var, false);
        } else if bdd.high_link_of(this_node) == next_node {
            result.set_value(var, true);
        } else {
            panic!("Path {:?} is not valid in BDD {:?}", path, bdd);
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use crate::{Bdd, BddPartialValuation, BddPathIterator, BddVariable, BddVariableSet};

    #[test]
    fn bdd_path_iterator_trivial() {
        let ff = Bdd::mk_false(10);
        assert_eq!(0, BddPathIterator::new(&ff).count());

        let tt = Bdd::mk_true(10);
        assert_eq!(1, BddPathIterator::new(&tt).count());

        let tt = Bdd::mk_true(0);
        assert_eq!(1, BddPathIterator::new(&tt).count());

        let clause =
            BddPartialValuation::from_values(&[(BddVariable(1), true), (BddVariable(2), false)]);
        let vars = BddVariableSet::new_anonymous(10);
        assert_eq!(
            1,
            BddPathIterator::new(&vars.mk_conjunctive_clause(&clause)).count()
        );
        assert_eq!(
            2,
            BddPathIterator::new(&vars.mk_disjunctive_clause(&clause)).count()
        );
    }

    #[test]
    fn bdd_path_iterator() {
        let vars = BddVariableSet::new_anonymous(5);
        let v = vars.variables();

        let c1 = BddPartialValuation::from_values(&[(v[0], true), (v[1], false)]);
        let c2 = BddPartialValuation::from_values(&[(v[1], true), (v[3], false)]);
        let c3 = BddPartialValuation::from_values(&[(v[2], false), (v[4], true)]);
        let bdd = vars.mk_dnf(&[c1.clone(), c2.clone(), c3.clone()]);

        // println!("{}", bdd.to_dot_string(&vars, true));
        // Counted manually in the .dot graph:
        assert_eq!(8, BddPathIterator::new(&bdd).count());

        BddPathIterator::new(&bdd).for_each(|path| {
            assert!(path.extends(&c1) || path.extends(&c2) || path.extends(&c3));
        });
    }
}
