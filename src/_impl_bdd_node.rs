use super::*;

impl BddNode {
    /// Make a new terminal `zero` node.
    pub fn mk_zero(num_vars: u16) -> BddNode {
        BddNode {
            var: BddVariable(num_vars),
            low_link: BddPointer::zero(),
            high_link: BddPointer::zero(),
        }
    }

    /// Make a new terminal `one` node.
    pub fn mk_one(num_vars: u16) -> BddNode {
        BddNode {
            var: BddVariable(num_vars),
            low_link: BddPointer::one(),
            high_link: BddPointer::one(),
        }
    }

    /// Make a new general node.
    ///
    /// *Assumptions:*
    ///  - `low` and `high` are pointers in the same `Bdd` array.
    ///  - Returned node will be added to the same `Bdd` where `low` and `high` are pointers.
    pub fn mk_node(var: BddVariable, low_link: BddPointer, high_link: BddPointer) -> BddNode {
        BddNode {
            var,
            low_link,
            high_link,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Some basic methods used for testing.
    impl BddNode {
        /// Check whether this node is *effectively* terminal.
        ///
        /// *Warning:* This does not mean the node is necessarily terminal, it might also just
        /// point to a terminal node, effectively gaining its value. However, this should not
        /// happen in minimized BDDs.
        pub fn is_terminal(&self) -> bool {
            self.low_link == self.high_link && (self.low_link.is_one() || self.low_link.is_zero())
        }

        /// Check whether this node is *effectively* one.
        pub fn is_one(&self) -> bool {
            self.is_terminal() && self.low_link.is_one()
        }

        /// Check whether this node is *effectively* zero.
        pub fn is_zero(&self) -> bool {
            self.is_terminal() && self.low_link.is_zero()
        }
    }

    #[test]
    fn bdd_node_one() {
        let one = BddNode::mk_one(2);
        assert!(one.is_terminal());
        assert!(one.is_one());
        assert!(!one.is_zero());
        assert_eq!(BddVariable(2), one.var);
    }

    #[test]
    fn bdd_node_zero() {
        let zero = BddNode::mk_zero(2);
        assert!(zero.is_terminal());
        assert!(zero.is_zero());
        assert!(!zero.is_one());
        assert_eq!(BddVariable(2), zero.var);
    }

    #[test]
    fn bdd_node_create() {
        let node = BddNode::mk_node(
            BddVariable(4),
            BddPointer::from_index(16),
            BddPointer::zero(),
        );
        assert_eq!(BddPointer::from_index(16), node.low_link);
        assert_eq!(BddPointer::zero(), node.high_link);
        assert_eq!(BddVariable(4), node.var);
        assert!(!node.is_terminal());
        assert!(!node.is_one());
        assert!(!node.is_zero());
    }
}
