use crate::{Bdd, BddCube};
use std::convert::TryFrom;

impl Bdd {
    /// Compute the *smallest* cube in the `Bdd`.
    ///
    /// The smallest cube is the one with the greatest amount of
    /// fixed variables (i.e. the cube corresponds to the least
    /// amount of valuations). If there are multiple min cubes,
    /// the method places no guarantees on which cube is returned,
    /// but should be deterministic.
    pub fn min_cube(&self) -> BddCube {
        if self.is_false() {
            panic!("Calling `min_cube` on an empty Bdd.");
        }
        // A vector which contains the size (no. of free variables) of the min
        // cube originating in the corresponding Bdd node, and which link is
        // used in such cube (i.e. low=false, true=high).
        let mut cube_sizes: Vec<(u16, bool)> = Vec::new();
        // For leaves, the link does not really matter.
        cube_sizes.push((0, true));
        cube_sizes.push((0, true));
        for node in self.nodes().skip(2) {
            if node.low_link.is_zero() {
                let high_link = usize::try_from(node.high_link.0).unwrap();
                cube_sizes.push((cube_sizes[high_link].0 + 1, true));
            } else if node.high_link.is_zero() {
                let low_link = usize::try_from(node.low_link.0).unwrap();
                cube_sizes.push((cube_sizes[low_link].0 + 1, false));
            } else {
                let low_link = usize::try_from(node.low_link.0).unwrap();
                let high_link = usize::try_from(node.high_link.0).unwrap();
                if cube_sizes[high_link].0 > cube_sizes[low_link].0 {
                    cube_sizes.push((cube_sizes[high_link].0 + 1, true));
                } else {
                    cube_sizes.push((cube_sizes[low_link].0 + 1, false));
                }
            }
        }
        let mut result = BddCube::new(self.num_vars());
        let mut pointer = self.root_pointer();
        while !pointer.is_one() {
            let var = self.var_of(pointer);
            let value = cube_sizes[pointer.to_index()].1;
            result.set(var, value);
            pointer = if value {
                self.high_link_of(pointer)
            } else {
                self.low_link_of(pointer)
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use crate::_test_util::mk_small_test_bdd;
    use crate::{BddVariable, BddVariableSet};

    #[test]
    fn test_min_cube_basic() {
        let bdd = mk_small_test_bdd();
        let cube = bdd.min_cube();
        assert_eq!(
            cube.values(),
            vec![(BddVariable(2), true), (BddVariable(3), false)]
        );
    }

    #[test]
    fn test_min_cube_complex() {
        let universe = BddVariableSet::new_anonymous(5);
        let bdd = universe.eval_expression_string("x_1 & ((x_2 & !x_3 & x_4) | x_3)");
        assert_eq!(
            bdd.min_cube().values(),
            vec![
                (BddVariable(1), true),
                (BddVariable(2), true),
                (BddVariable(3), false),
                (BddVariable(4), true)
            ]
        );
    }
}
