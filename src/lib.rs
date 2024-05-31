//! This crate implements a tree data structure.
//!
//! A tree is a directed acyclic graph of nodes, all of them
//! carrying an optional payload, as well as an optional
//! annotation to the edge linking them to their parent.
//!
//! Internally, nodes are stored in a vec, and the topology of the tree
//!
//! Each node in the tree may contain an arbitratry number of
//! children.
use errors::Error;
use identity_hash::{IntMap, IntSet};
use std::fmt::Display;

pub mod errors;
pub mod render;

pub type NodeHandle = usize;

/// A node in the tree. A [`Node`] can carry a `Payload`, and can annotate the
/// branch to its parent with an `Edge`.
pub struct Node<Payload, Edge> {
    parent: Option<NodeHandle>,
    branch: Option<Edge>,
    data: Payload,
}
impl<Payload, Edge> Node<Payload, Edge> {
    /// If this node has a `Payload`, return a reference to it.
    pub fn data(&self) -> &Payload {
        &self.data
    }

    /// If this node has a `Payload`, return a mutable reference to it.
    pub fn data_mut(&mut self) -> &mut Payload {
        &mut self.data
    }

    /// Set the `Payload` of this `Node`.
    pub fn set_data(&mut self, e: Payload) {
        self.data = e
    }

    /// Returns a reference to this node parent branch `Edge`.
    pub fn branch(&self) -> Option<&Edge> {
        self.branch.as_ref()
    }

    /// Set the `Edge` of this node parent branch.
    pub fn set_branch(&mut self, e: Edge) {
        self.branch = Some(e)
    }

    /// Unset the `Edge` of this node parent branch.
    pub fn unset_branch(&mut self) {
        self.branch = None
    }
}

pub struct Tree<Payload = (), MetaData = (), Edge = (), Children = Vec<NodeHandle>> {
    current_id: NodeHandle,
    metadata: MetaData,
    nodes: IntMap<NodeHandle, Node<Payload, Edge>>,
    children: IntMap<NodeHandle, Children>,
    arity: Option<usize>,
    _spans_set: IntMap<NodeHandle, IntSet<NodeHandle>>,
    _descendants: IntMap<NodeHandle, Vec<NodeHandle>>,
}

impl<P, D: Default, E> Tree<P, D, E> {
    /// Create a new tree
    pub fn new() -> Self {
        Self {
            current_id: 0,
            metadata: D::default(),
            nodes: Default::default(),
            children: Default::default(),
            arity: None,
            _spans_set: Default::default(),
            _descendants: Default::default(),
        }
    }

    /// Create a new binary tree, i.e. of arity 2
    pub fn binary() -> Self {
        Self {
            current_id: 0,
            metadata: D::default(),
            nodes: Default::default(),
            children: Default::default(),
            arity: Some(2),
            _spans_set: Default::default(),
            _descendants: Default::default(),
        }
    }

    /// Create a new tree with as most `arity` children per node
    pub fn with_arity(arity: usize) -> Self {
        Self {
            current_id: 0,
            metadata: D::default(),
            nodes: Default::default(),
            children: Default::default(),
            arity: Some(arity),
            _spans_set: Default::default(),
            _descendants: Default::default(),
        }
    }
}
impl<P, D, E> Tree<P, D, E> {
    /// Assign the given `metadata` as the meta-data associated to this tree.
    pub fn set_metadata(&mut self, metadata: D) {
        self.metadata = metadata;
    }

    /// Return a reference to the meta-data associated to this tree.
    pub fn metadata(&self) -> &D {
        &self.metadata
    }

    /// Return a mutable reference to the meta-data associated to this tree.
    pub fn metadata_mut(&mut self) -> &mut D {
        &mut self.metadata
    }

    /// Return a reference the node identified by `n` if it exists, or
    /// [`Error::NodeNotFound`] otherwise.
    pub fn get(&self, n: NodeHandle) -> Result<&Node<P, E>, Error> {
        self.nodes.get(&n).ok_or(Error::NodeNotFound(n))
    }

    /// Return a mutable reference the node identified by `n` if it exists, or
    /// [`Error::NodeNotFound`] otherwise.
    pub fn get_mut(&mut self, n: NodeHandle) -> Result<&mut Node<P, E>, Error> {
        self.nodes.get_mut(&n).ok_or(Error::NodeNotFound(n))
    }

    /// Return `true` if the node `n` has no children.
    pub fn is_leaf(&self, n: NodeHandle) -> bool {
        self.children[&n].is_empty()
    }

    /// Return a reference to the children of the node `n`.
    pub fn children(&self, n: NodeHandle) -> &[NodeHandle] {
        &self.children[&n]
    }

    pub fn root(&self) -> NodeHandle {
        self.roots().next().unwrap()
    }

    pub fn roots(&self) -> impl Iterator<Item = NodeHandle> + '_ {
        self.nodes
            .iter()
            .filter_map(|(i, n)| if n.parent.is_none() { Some(i) } else { None })
            .cloned()
    }

    /// Return true if the given node is root; panic if it does not exist.
    pub fn is_root(&self, n: NodeHandle) -> bool {
        self[n].parent.is_none()
    }

    /// Provide an iterator over all the node handles in the tree.
    pub fn nodes(&self) -> impl Iterator<Item = NodeHandle> + '_ {
        self.nodes.keys().cloned()
    }

    /// Return an iterator over mutable reference to the nodes of the tree.
    pub fn nodes_mut(&mut self) -> impl Iterator<Item = &mut Node<P, E>> {
        self.nodes.values_mut()
    }

    /// Provide an iterator over the handles of all the leaves of this tree.
    pub fn leaves(&self) -> impl Iterator<Item = NodeHandle> + '_ {
        self.nodes.keys().filter(|&&n| self.is_leaf(n)).copied()
    }

    /// Return the number of nodes in this tree.
    pub fn len(&self) -> NodeHandle {
        self.nodes.len()
    }

    /// Return true if the tree is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    fn insert_node(&mut self, parent: Option<NodeHandle>, n: Node<P, E>) -> NodeHandle {
        self.current_id = self.current_id.checked_add(1).expect("Tree is too big");
        let id = self.current_id;
        assert!(!self.nodes.contains_key(&id), "{} already exists", id);
        assert!(parent.is_none() || self.nodes.contains_key(&parent.unwrap()));
        self.nodes.insert(id, n);
        if let Some(parent) = parent {
            if let Some(arity) = self.arity {
                assert!(self.children(parent).len() < arity)
            }
            self.children.get_mut(&parent).unwrap().push(id);
        }

        id
    }

    pub fn add_node(&mut self, parent: Option<NodeHandle>, data: P) -> NodeHandle {
        if let Some(parent) = parent {
            assert!(self.nodes.contains_key(&parent));
        }

        self.insert_node(
            parent,
            Node {
                parent,
                branch: None,
                data,
            },
        )
    }

    /// Connect the free-standing node `n` under `target`.
    ///
    /// Panic if `n` is not free-standing or if the arity constraints are broken.
    pub fn plug(&mut self, n: NodeHandle, target: NodeHandle) {
        assert!(self[n].parent.is_none());
        assert!(!self.children[&target].contains(&n));
        if let Some(arity) = self.arity {
            assert!(self.children[&target].len() < arity)
        }
        self.nodes.get_mut(&n).unwrap().parent = Some(target);
        self.children.get_mut(&target).unwrap().push(n);
    }

    /// Disconnect the node `n` from its parent.
    pub fn unplug(&mut self, n: NodeHandle) {
        let parent = self.nodes[&n].parent;
        assert!(parent.is_none() || self.children[&parent.unwrap()].contains(&n));

        self.nodes.get_mut(&n).unwrap().parent = None;
        if let Some(parent) = parent {
            self.children
                .get_mut(&parent)
                .unwrap()
                .retain(|nn| *nn != n);
        }
    }

    /// Delete the node `n`, and all its children recursively.
    ///
    /// Panic if `n` does not exist in the tree.
    pub fn delete_node(&mut self, n: NodeHandle) {
        assert!(self.nodes.contains_key(&n));
        for c in self.children[&n].clone().into_iter() {
            self.delete_node(c);
        }
        self.unplug(n);
        self.nodes.remove(&n);
    }

    /// Delete the nodes `ns`, and all their children recursively.
    ///
    /// Panic if any node in `ns` does not exist.
    pub fn delete_nodes(&mut self, ns: &[NodeHandle]) {
        for n in ns {
            self.delete_node(*n);
        }
    }

    /// Move `n` from its current position to under `target`.
    ///
    /// Panic if `n` is free-standing or if arity constraints is broken.
    pub fn move_node(&mut self, n: NodeHandle, target: NodeHandle) {
        self.unplug(n);
        self.plug(target, n);
    }

    /// Insert the existing node `between` between the nodes `a` and `b`;
    /// turning `a <-- b` into `a <-- between <-- b`.
    ///
    /// Panic if a is not the parent of b or if arity constraint is broken.
    pub fn insert_between(&mut self, between: NodeHandle, a: NodeHandle, b: NodeHandle) {
        if let Some(b_parent) = self.parent(b) {
            assert!(b_parent == a);
        } else {
            panic!("a is not the parent of b");
        }

        self.unplug(b);
        self.plug(a, between);
        self.plug(between, b);
    }

    /// Return the parent of `n`, or `None` if `n` is a root.
    pub fn parent(&self, n: NodeHandle) -> Option<NodeHandle> {
        self[n].parent
    }

    /// Return, if it exists, the first leaf in tree satisfying the predicate.
    ///
    /// # Arguments
    ///
    /// * f - A predicate taking a reference to a node payload
    pub fn find_leaf<F>(&self, f: F) -> Option<NodeHandle>
    where
        F: Fn(&P) -> bool,
    {
        self.nodes
            .iter()
            .filter(|(i, _)| self.is_leaf(**i))
            .find(|(_i, n)| f(&n.data))
            .map(|(i, _)| *i)
    }

    /// Return, if it exists, the first node in tree satisfying the predicate.
    ///
    /// # Arguments
    ///
    /// * f - A predicate taking a reference to a node payload
    pub fn find_node<F>(&self, f: F) -> Option<NodeHandle>
    where
        F: Fn(&P) -> bool,
    {
        self.nodes
            .iter()
            .find(|(_i, n)| f(&n.data))
            .map(|(i, _)| *i)
    }

    /// Return, if it exists, the first child of `n` tree satisfying the predicate.
    ///
    /// # Arguments
    ///
    /// * n - The reference node
    /// * f - A predicate taking a reference to a node payload
    pub fn find_child<F>(&self, n: NodeHandle, f: F) -> Option<NodeHandle>
    where
        F: Fn(&P) -> bool,
    {
        self.children(n)
            .iter()
            .cloned()
            .find(|&n| f(self[n].data()))
    }

    /// Compute the Most Recent Common Ancestor of a set of nodes.
    /// If the set is empty, return the tree root.
    pub fn mrca(&self, nodes: impl IntoIterator<Item = NodeHandle>) -> Result<NodeHandle, Error> {
        let mut nodes = nodes.into_iter();
        let first = if let Some(node) = nodes.next() {
            node
        } else {
            return Ok(self.root());
        };

        let ancestors = self.ascendance(first);
        let ranks = ancestors
            .iter()
            .copied()
            .enumerate()
            .map(|(i, j)| (j, i))
            .collect::<IntMap<_, _>>();
        let mut checked = IntSet::<NodeHandle>::from_iter(ancestors.iter().copied());
        let mut oldest: NodeHandle = 0;

        for species in nodes {
            let mut species: NodeHandle = species;
            while !checked.contains(&species) {
                checked.insert(species);
                species = self.nodes[&species].parent.unwrap();
                oldest = oldest.max(*ranks.get(&species).unwrap_or(&0));
            }
        }

        Ok(ancestors[oldest])
    }

    /// Return the lineage of n, i.e. the direct path from `n` to the root.
    ///
    /// Panic if `n` does not exist in the tree.
    pub fn ascendance(&self, n: NodeHandle) -> Vec<NodeHandle> {
        let mut r = Vec::new();
        let mut parent = Some(n);

        while let Some(me) = parent {
            r.push(me);
            parent = self.parent(me);
        }

        r
    }

    /// Find all the descendants of `n`, i.e. all the nodes below `n` in the
    /// tree, not including `n`.
    ///
    /// Panic if `n` does not exist in the tree.
    pub fn descendants(&self, n: NodeHandle) -> Vec<NodeHandle> {
        fn find_descendants<PP, DD, EE>(
            t: &Tree<PP, DD, EE>,
            n: NodeHandle,
            ax: &mut Vec<NodeHandle>,
        ) {
            ax.push(n);
            for &c in t.children[&n].iter() {
                find_descendants(t, c, ax);
            }
        }

        let mut r = vec![];
        for &c in self.children[&n].iter() {
            find_descendants(self, c, &mut r);
        }
        r
    }

    /// Return a [`Vec`] containing all the leaves being descendant of `n`.
    pub fn leaves_of(&self, n: NodeHandle) -> Vec<NodeHandle> {
        self.leave_set_of(n).into_iter().collect()
    }

    /// Return a set containing all the leaves being descendant of `n`.
    pub fn leave_set_of(&self, n: NodeHandle) -> IntSet<NodeHandle> {
        fn find_descendants_leaves<PP, DD, EE>(
            t: &Tree<PP, DD, EE>,
            n: NodeHandle,
            ax: &mut IntSet<NodeHandle>,
        ) {
            if t.is_leaf(n) {
                ax.insert(n);
            } else {
                for &c in t.children[&n].iter() {
                    find_descendants_leaves(t, c, ax);
                }
            }
        }

        let mut r = Default::default();
        find_descendants_leaves(self, n, &mut r);
        r
    }

    pub fn cache_descendants(&mut self) {
        let mut me = self.root();
        let todo = self.descendants(me);
        self._descendants.insert(me, todo.to_owned());
        for n in todo {
            self._descendants.insert(n, self.descendants(n));
        }
        while let Some(parent) = self[me].parent {
            self._descendants.insert(parent, self.descendants(parent));
            me = parent;
        }
    }

    pub fn cache_descendants_of(&mut self, from: NodeHandle) {
        let mut me = from;
        let todo = self.descendants(me);
        self._descendants.insert(me, todo.to_owned());
        for n in todo {
            self._descendants.insert(n, self.descendants(n));
        }
        while let Some(parent) = self[me].parent {
            self._descendants.insert(parent, self.descendants(parent));
            me = parent;
        }
    }

    pub fn cached_descendants(&self, n: NodeHandle) -> Option<&Vec<NodeHandle>> {
        self._descendants.get(&n)
    }

    pub fn cache_leaves(&mut self) {
        for &k in self.nodes.keys() {
            self._spans_set.insert(k, self.leave_set_of(k));
        }
    }

    pub fn cached_leaves_of(&self, n: NodeHandle) -> &IntSet<NodeHandle> {
        &self._spans_set[&n]
    }

    pub fn cached_leaves_of_vec(&self, n: NodeHandle) -> Vec<NodeHandle> {
        let mut r = Vec::with_capacity(self._spans_set[&n].len());
        r.extend(self._spans_set[&n].iter().copied());
        r
    }

    pub fn siblings(&self, n: NodeHandle) -> Vec<NodeHandle> {
        if let Some(parent) = self[n].parent {
            self.descendants(parent)
                .into_iter()
                .filter(|&nn| nn != n)
                .filter(|n| self.is_leaf(*n))
                .collect()
        } else {
            vec![]
        }
    }

    pub fn depth(&self) -> f32 {
        todo!()
    }

    /// Compute the depth of `n` according to the given measure.
    ///
    /// # Arguments
    ///
    /// * `n` - The node to compute the depth of.
    /// * `f` - A function associating a length to a an edge.
    pub fn depth_of<Measure: Fn(&E) -> f32>(&self, n: NodeHandle, f: &Measure) -> f32 {
        let mut depth = self[n].branch.as_ref().map(f).unwrap_or(0.);
        let mut n = n;
        while let Some(parent) = self[n].parent {
            depth += self[parent].branch.as_ref().map(f).unwrap_or(0.);
            n = parent;
        }
        depth
    }

    /// Return the topological depth of `n`, i.e. its distance to the root of
    /// the tree.
    pub fn topological_depth_of(&self, n: NodeHandle) -> Result<i64, Error> {
        let mut depth = 0;
        let mut n = n;
        while let Some(parent) = self.nodes[&n].parent {
            depth += 1;
            n = parent;
        }
        Ok(depth)
    }

    /// Compute the topological depth of the tree, i.e. the depth of the deepest node.
    pub fn topological_depth(&self) -> (NodeHandle, usize) {
        fn _rec_depth<PP, DD, EE>(t: &Tree<PP, DD, EE>, n: NodeHandle) -> (NodeHandle, usize) {
            if t.is_leaf(n) {
                (n, 0)
            } else {
                let (n, d) = t
                    .children(n)
                    .iter()
                    .map(|&c| _rec_depth(t, c))
                    .max_by_key(|(_, d)| *d)
                    .unwrap_or_default();
                (n, d + 1)
            }
        }

        _rec_depth(self, self.root())
    }

    /// Execute a function over all the leaves of the tree.
    ///
    /// # Arguments
    ///
    /// * `f` - a function taking a reference to a node
    pub fn for_each_leave<F: FnMut(&Node<P, E>)>(&self, f: &mut F) {
        self.nodes
            .iter()
            .filter_map(|(i, n)| if self.is_leaf(*i) { Some(n) } else { None })
            .for_each(f);
    }

    /// Execute a function over all the leaves of the tree.
    ///
    /// # Arguments
    ///
    /// * `f` - a function taking a mutable reference to a node
    pub fn for_each_leave_mut<F: FnMut(&mut Node<P, E>)>(&mut self, f: &mut F) {
        let to_process = self
            .nodes
            .keys()
            .filter(|i| self.is_leaf(**i))
            .copied()
            .collect::<Vec<_>>();

        to_process
            .into_iter()
            .for_each(|i| f(self.nodes.get_mut(&i).unwrap()));
    }

    /// Return an iterator over all the non-leaf nodes of the tree.
    pub fn inners(&self) -> impl Iterator<Item = NodeHandle> + '_ {
        self.nodes
            .keys()
            .filter(move |n| !self.is_leaf(**n))
            .copied()
    }

    /// Recursively delete all the nodes satisfyin the given predicate.
    ///
    /// # Arguments
    ///
    /// * `is_useless` - A predicate taking a node, and returning whether it
    /// should be removed.
    pub fn prune_by<U: Fn(NodeHandle, &Node<P, E>) -> bool>(&mut self, is_useless: U) {
        loop {
            let todo = self
                .nodes
                .iter()
                .find_map(|(i, n)| if is_useless(*i, n) { Some(i) } else { None })
                .copied();

            if let Some(i) = todo {
                let children = self.children(i).to_vec();
                for c in children {
                    self.move_node(c, self.parent(i).unwrap());
                }
                self.delete_node(i);
            } else {
                break;
            }
        }
    }

    /// Remove empty inner nodes (i.e. nodes without content nor children) and
    /// compress redundant inner nodes (i.e. nodes with a single child and no
    /// content).
    pub fn prune(&mut self, is_empty: impl Fn(&P) -> bool) {
        loop {
            let todo = self
                .nodes
                .iter()
                .find_map(|(i, n)| {
                    if (self.children(*i).is_empty() && is_empty(&n.data))
                        || (self.children(*i).len() == 1 && is_empty(&n.data))
                    {
                        Some(i)
                    } else {
                        None
                    }
                })
                .copied();

            if let Some(i) = todo {
                let children = self.children(i).to_vec();
                for c in children {
                    self.move_node(c, self.parent(i).unwrap());
                }
                self.delete_node(i);
            } else {
                break;
            }
        }
    }

    fn rec_sort_by<K: Ord + Clone + std::fmt::Debug>(
        &mut self,
        n: NodeHandle,
        k: &impl Fn(&P) -> K,
        by_leaves: bool,
    ) -> K {
        let mut children = self.children[&n].clone();
        children.sort_by_cached_key(|c| k(self[*c].data()));
        self.children.insert(n, children);

        if by_leaves || self.children[&n].is_empty() {
            k(&self[n].data)
        } else {
            k(&self[self.children[&n][0]].data)
        }
    }

    /// Sort all sibling nodes according to the given key function.
    ///
    /// # Arguments
    ///
    /// * k - a function producing a [`Ord`] sorting criterion from a node data
    pub fn sort_by<K: std::fmt::Debug + Ord + Clone>(&mut self, k: impl Fn(&P) -> K) {
        let _ = self.rec_sort_by(self.root(), &k, false);
    }

    /// Sort sibling leave nodes according to the given key function.
    ///
    /// # Arguments
    ///
    /// * k - a function producing a [`Ord`] sorting criterion from a node data
    pub fn sort_leaves_by<K: std::fmt::Debug + Ord + Clone>(&mut self, k: impl Fn(&P) -> K) {
        let _ = self.rec_sort_by(self.root(), &k, true);
    }

    fn print_node<
        NodeFormatter: Fn(&P) -> S1,
        S1: Default + Display,
        EdgeFormatter: Fn(&E) -> S2,
        S2: Default + Display,
    >(
        &self,
        n: NodeHandle,
        indent: NodeHandle,
        f: &NodeFormatter,
        g: &EdgeFormatter,
    ) {
        println!(
            "{}{}{}",
            str::repeat(" ", indent),
            f(&self[n].data),
            self[n]
                .branch
                .as_ref()
                .map(|x| format!(":{}", g(x)))
                .unwrap_or_default(),
        );
        self.children[&n]
            .iter()
            .for_each(|c| self.print_node(*c, indent + 4, f, g))
    }

    /// Print a text representation of the tree, leveraging the given formatting functions.
    ///
    /// # Arguments
    ///
    /// * `node_printer` - A function producing a [`Display`]-able value from a node.
    /// * `edge_printer` - A function producing a [`Display`]-able value from an edge.
    pub fn print<
        NodeFormatter: Fn(&P) -> S1,
        S1: Default + Display,
        EdgeFormatter: Fn(&E) -> S2,
        S2: Default + Display,
    >(
        &self,
        node_printer: NodeFormatter,
        edge_printer: EdgeFormatter,
    ) {
        if !self.nodes.is_empty() {
            for root in self.roots() {
                self.print_node(root, 0, &node_printer, &edge_printer);
            }
        }
    }
}
impl<'a, P: Ord, D, E> Tree<P, D, E> {
    fn rec_sort(&'a mut self, n: NodeHandle, by_leaves: bool) -> &P {
        let mut children = self.children[&n].clone();
        children.sort_by_cached_key(|c| self[*c].data());
        self.children.insert(n, children);

        if by_leaves || self.children[&n].is_empty() {
            &self[n].data
        } else {
            &self[self.children[&n][0]].data
        }
    }

    pub fn sort(&'a mut self) {
        let _ = self.rec_sort(self.root(), false);
    }

    pub fn sort_leaves(&'a mut self) {
        let _ = self.rec_sort(self.root(), true);
    }
}
impl<P, D, E> std::ops::Index<NodeHandle> for Tree<P, D, E> {
    type Output = Node<P, E>;
    fn index(&self, i: usize) -> &Self::Output {
        &self.nodes[&i]
    }
}
impl<P, D, E> std::ops::IndexMut<usize> for Tree<P, D, E> {
    fn index_mut(&mut self, i: NodeHandle) -> &mut Self::Output {
        self.nodes.get_mut(&i).unwrap()
    }
}
