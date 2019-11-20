//! ## Introduction to BDDs
//!
//! BDD is a *directed acyclic graph* (DAG) with two types of vertices (or nodes). There are two
//! terminal vertices called `1` and `0` which have no outgoing edges. The rest of the vertices
//! are decision vertices. Each decision vertex has an associated Boolean variable $v$ and two
//! outgoing edges $low$ and $high$. In diagrams, $low$ edges are typically drawn as dashed and
//! $high$ edges as solid. The graph has always one root vertex (with no predecessors).
//!
//! Semantically, for a given valuation (assignment) of Boolean variables $Val(v) \to \\{ 0, 1 \\}$,
//! we can "evaluate" the graph by starting in the root vertex and choosing the following vertex
//! based on the value of the current decision variable in the given valuation. Once we reach
//! a terminal vertex, we obtain a final Boolean value. For example, consider the formula
//! $a \land \neg b$. The corresponding BDD is the following:
//!
//! ```mermaid
//! graph LR
//!     a($a$)
//!     b($b$)
//!     zero($0$)
//!     one($1$)
//!     a -.-> zero
//!     a --> b
//!     b -.-> one
//!     b --> zero
//! ```
//!
//! We can see that there is only one path from the root ($a$) to `1` and this path corresponds
//! to the only valuation which satisfies the Boolean formula (i.e. $a = 1; b = 0$).
//!
//! Typically, BDDs assume some **fixed ordering of variables** such that every path from root to
//! terminal follows this ordering (thus *ordered*). Furthermore, in every BDD, all **redundant
//! vertices are removed** (thus *reduced*). The vertex is redundant if both $low$ and $high$
//! point to the same vertex (there is no decision) or if there is another vertex with the same
//! values of $v$, $low$ and $high$ somewhere else in the graph (we can reuse this vertex).
//!
//! When the BDD is ordered and reduced, it is **canonical**, i.e. every equivalent Boolean formula
//! has the same BDD (equality can be thus checked syntactically on the structure of the graph).
//!
//! ## Encoding BDD in an array
//!
//! While BDD is a graph, it would be wasteful to store each node of the BDD as a separate memory
//! object requiring allocations and book keeping. Instead, we sort nodes in each BDD in the
//! DFS post-order (taking low edge first and high edge second, although this decision is arbitrary)
//! of the graph and this way, we can easily save them as a sequence in an array. The only
//! exception are the two terminal nodes which we always place on positions 0 and 1
//! (empty BDD only has the 0 node).
//!
//! Because DFS post-order is unique, we can still check formula equivalence by comparing the two
//! arrays element-wise. Also notice that the root of the BDD is always the last element of the
//! array and children of any node always have smaller indices than the parent.
//!
//! The BDD from the previous section translates to the following array:
//!
//! ```c
//! [0, 1, (b, low = 1, high = 0), (a, low = 0, high = 2)]
//! ```
//!
//! Notice that the edge pointers are now indices into the array itself instead of memory
//! references. This also allows certain memory optimisations (for "small" BDDs, the pointers
//! only need to be 32 bits even on 64 bit platforms, etc.). Also, such representation is trivial
//! to serialize, deserialize or share, since we can just clone the whole array if needed.
