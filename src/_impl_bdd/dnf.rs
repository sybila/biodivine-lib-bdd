use crate::*;
use fxhash::FxBuildHasher;

struct DNFContext {
    variables: Vec<BddVariable>,
    existing: HashMap<BddNode, u32, FxBuildHasher>,
    res: Vec<BddNode>,
}

impl DNFContext {
    fn new(variable_set: &BddVariableSet, variables: Vec<BddVariable>) -> Self {
        let mut dnf_context = DNFContext {
            existing: HashMap::with_capacity_and_hasher(variables.len(), FxBuildHasher::default()),
            variables,
            res: vec![
                BddNode {
                    var: BddVariable(variable_set.num_vars),
                    low_link: BddPointer(0),
                    high_link: BddPointer(0),
                },
                BddNode {
                    var: BddVariable(variable_set.num_vars),
                    low_link: BddPointer(1),
                    high_link: BddPointer(1),
                },
            ],
        };
        dnf_context.existing.insert(dnf_context.res[0], 0);
        dnf_context.existing.insert(dnf_context.res[1], 1);
        dnf_context
    }

    fn mk_node(&mut self, bn: BddNode) -> u32 {
        if self.existing.contains_key(&bn) {
            self.existing[&bn]
        } else {
            self.res.push(bn);
            let x: u32 = (self.res.len() - 1) as u32;
            self.existing.insert(bn, x);
            x
        }
    }

    fn dnf(mut self, vv: Vec<Vec<bool>>) -> Bdd {
        let b=self.dnf_inner(0, vv);
        if b==0 {
            return Bdd(vec![self.res[0] ]);
        }
        if b==1 {
            return Bdd(vec![self.res[0],self.res[1]]);
        }
        assert_eq!(b as usize,self.res.len()-1);
        Bdd(self.res)
    }

    /// WARNING: this uses recursive. Maybe out of stack
    fn dnf_inner(&mut self, index: usize, vv: Vec<Vec<bool>>) -> u32 {
        if vv.len() == 0 {
            // always false
            return 0;
        }
        if index == self.variables.len() - 1 {
            let mut pos = false;
            let mut neg = false;
            for v in vv {
                if v[index] {
                    pos = true;
                } else {
                    neg = true;
                }
            }
            if pos && neg {
                return 1;
            }
            if !pos && !neg {
                return 0;
            }
            if pos {
                return self.mk_node(BddNode {
                    var: self.variables[index],
                    high_link: BddPointer(1),
                    low_link: BddPointer(0),
                });
            } else {
                return self.mk_node(BddNode {
                    var: self.variables[index],
                    high_link: BddPointer(0),
                    low_link: BddPointer(1),
                });
            }
        } else {
            let mut h_v: Vec<Vec<bool>> = vec![];
            let mut l_v: Vec<Vec<bool>> = vec![];
            for v in vv {
                if v[index] {
                    h_v.push(v);
                } else {
                    l_v.push(v);
                }
            }
            let h_n = self.dnf_inner(index + 1, h_v);
            let l_n = self.dnf_inner(index + 1, l_v);
            if h_n == l_n {
                return h_n;
            }
            self.mk_node(BddNode {
                var: self.variables[index],
                high_link: BddPointer(h_n),
                low_link: BddPointer(l_n),
            })
        }
    }
}

impl Bdd {
    /// WARNING: this uses recursive. Maybe out of stack
    /// notice variable_set.num_vars != variables.len()
    /// variables is subset of variable_set
    /// the variables should be in order: variables[0] < variables[1]  < variables[2]
    pub fn dnf(
        variable_set: &BddVariableSet,
        variables: Vec<BddVariable>,
        vv: Vec<Vec<bool>>,
    ) -> Self {
        // assert_eq!(variables.len(),vv[0].len());

        let dnf_context = DNFContext::new(variable_set, variables);
        dnf_context.dnf(vv)
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn dnf_false(){
        let bddvariableset = BddVariableSet::new_anonymous(3);
        let vv:Vec<Vec<bool>> = vec![];
        let bdd1 = Bdd::dnf(&bddvariableset, bddvariableset.variables(), vv);
        let bdd2 = bddvariableset.mk_false();
        assert!(bdd1.iff(&bdd2).is_true());
        assert_eq!(bdd1.size(), bdd2.size());
    }

    #[test]
    fn dnf_true(){
        let bddvariableset = BddVariableSet::new_anonymous(3);
        let vv = vec![
            vec![true, true, true],
            vec![true, true, false],
            vec![true, false, true],
            vec![true, false , false],
            vec![false, true, true],
            vec![false, true, false],
            vec![false, false, true],
            vec![false, false , false],
        ];
        let bdd1 = Bdd::dnf(&bddvariableset, bddvariableset.variables(), vv);
        let bdd2 = bddvariableset.mk_true();
        assert!(bdd1.iff(&bdd2).is_true());
        assert_eq!(bdd1.size(), bdd2.size());
    }

    #[test]
    fn small_dnf1() {
        let bddvariableset = BddVariableSet::new_anonymous(3);
        let vv = vec![
            vec![true, true, true],
            vec![false, true, true],
            vec![true, false, false],
        ];
        let bdd1 = Bdd::dnf(&bddvariableset, bddvariableset.variables(), vv);
        let x_0 = bddvariableset.mk_var_by_name("x_0");
        let x_1 = bddvariableset.mk_var_by_name("x_1");
        let x_2 = bddvariableset.mk_var_by_name("x_2");
        let bdd2 = bdd!((x_0 & (x_1 & x_2)) | (((!x_0) & (x_1 & x_2)) | (x_0 & ((!x_1) & (!x_2)))));
        // dbg!(bdd1.to_string());
        // dbg!(bdd2.to_string());
        assert!(bdd1.iff(&bdd2).is_true());
        assert_eq!(bdd1.size(), bdd2.size());
    }

    #[test]
    fn small_dnf2() {
        let bddvariableset = BddVariableSet::new_anonymous(3);
        let vv = vec![vec![true, true, true], vec![false, true, true]];
        let bdd1 = Bdd::dnf(&bddvariableset, bddvariableset.variables(), vv);
        let x_0 = bddvariableset.mk_var_by_name("x_0");
        let x_1 = bddvariableset.mk_var_by_name("x_1");
        let x_2 = bddvariableset.mk_var_by_name("x_2");
        let bdd2 = bdd!((x_0 & (x_1 & x_2)) | ((!x_0) & (x_1 & x_2)));
        // dbg!(bdd1.to_string());
        // dbg!(bdd2.to_string());
        assert!(bdd1.iff(&bdd2).is_true());
        assert_eq!(bdd1.size(), bdd2.size());
    }

    #[test]
    fn large_dnf() {
        let bddvariableset = BddVariableSet::new_anonymous(30);
        let mut vv = vec![];
        for i in 0..30000 {
            let mut v = vec![];
            for j in 0..30 {
                if (i & (1 << j)) > 0 {
                    v.push(true);
                } else {
                    v.push(false);
                }
            }
            vv.push(v);
        }
        let bdd1 = Bdd::dnf(&bddvariableset, bddvariableset.variables(), vv.clone());
        // dbg!(bdd1.to_string());
        let bdd2 = {
            let variables: Vec<Bdd> = bddvariableset
                .variables()
                .into_iter()
                .map(|x| bddvariableset.mk_var(x))
                .collect();
            let mut res = bddvariableset.mk_false();
            for v in vv {
                let mut temp = bddvariableset.mk_true();
                for (v, b) in variables.iter().zip(v.into_iter()) {
                    if b {
                        temp = temp.and(v);
                    } else {
                        temp = temp.and(&v.not());
                    }
                }
                res = res.or(&temp);
            }
            res
        };
        assert!(bdd1.iff(&bdd2).is_true());
    }
}
