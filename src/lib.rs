//! This crate implements a tree data structure.
//!
//! A tree is a directed acyclic graph of nodes, all of them
//! carrying an optional payload, as well as an optional
//! annotation to the edge linking them to their parent.
//!
//! Each node in the tree may contain an arbitratry number of
//! children.
use errors::Error;
use identity_hash::{IntMap, IntSet};
use std::fmt::Display;

pub mod errors;
pub mod render;

pub type NodeID = usize;

/// A node in the tree. A [`Node`] can carry a `Payload`, and annotate the
/// branch to its parent with an `Edge`.
pub struct Node<Payload, Edge, Children = Vec<NodeID>> {
    parent: Option<NodeID>,
    children: Children,
    branch: Option<Edge>,
    data: Payload,
}
impl<Payload, Edge> Node<Payload, Edge> {
    /// Return `true` if this node has no children.
    pub fn is_leaf(&self) -> bool {
        self.children.is_empty()
    }

    /// Returns a slice of the [`NodeID`] of this node children.
    pub fn children(&self) -> &[NodeID] {
        &self.children
    }

    /// If this node has a `Payload`, returns a reference to it
    pub fn data(&self) -> &Payload {
        &self.data
    }

    /// If this node has a `Payload`, returns a mutable reference to it
    pub fn data_mut(&mut self) -> &mut Payload {
        &mut self.data
    }

    /// Set the [`Payload`] of this [`Node`]
    pub fn set_data(&mut self, e: Payload) {
        self.data = e
    }

    /// Returns a reference to this node parent branch [`Edge`]
    pub fn branch(&self) -> Option<&Edge> {
        self.branch.as_ref()
    }

    /// Set the [`Edge`] of this node parent branch
    pub fn set_branch(&mut self, e: Edge) {
        self.branch = Some(e)
    }

    /// Unset the [`Edge`] of this node parent branch
    pub fn unset_branch(&mut self) {
        self.branch = None
    }
}

pub struct Tree<Payload, MetaData, Edge> {
    root: NodeID,
    current_id: NodeID,
    metadata: MetaData,
    nodes: IntMap<NodeID, Node<Payload, Edge>>,
    _spans_set: IntMap<NodeID, IntSet<NodeID>>,
    _descendants: IntMap<NodeID, Vec<NodeID>>,
}

impl<P, D: Default, E> Default for Tree<P, D, E> {
    fn default() -> Self {
        Self::with_metadata(D::default())
    }
}
impl<P, D: Default, E> Tree<P, D, E> {
    pub fn new() -> Self {
        Self {
            root: 0,
            current_id: 0,
            metadata: D::default(),
            nodes: Default::default(),
            _spans_set: Default::default(),
            _descendants: Default::default(),
        }
    }
}
impl<P, D, E> Tree<P, D, E> {
    pub fn with_metadata(metadata: D) -> Self {
        Self {
            root: 0,
            metadata,
            current_id: 0,
            nodes: Default::default(),
            _spans_set: Default::default(),
            _descendants: Default::default(),
        }
    }

    pub fn metadata(&self) -> &D {
        &self.metadata
    }

    pub fn metadata_mut(&mut self) -> &mut D {
        &mut self.metadata
    }

    pub fn get(&self, n: NodeID) -> Result<&Node<P, E>, Error> {
        self.nodes.get(&n).ok_or(Error::NodeNotFound(n))
    }

    pub fn get_mut(&mut self, n: NodeID) -> Result<&mut Node<P, E>, Error> {
        self.nodes.get_mut(&n).ok_or(Error::NodeNotFound(n))
    }

    pub fn set_root(&mut self, new_root: NodeID) {
        self.root = new_root;
    }

    pub fn root(&self) -> NodeID {
        self.root
    }

    pub fn is_root(&self, n: NodeID) -> bool {
        self.root == n
    }

    pub fn nodes(&self) -> impl Iterator<Item = NodeID> + '_ {
        self.nodes.keys().cloned()
    }

    pub fn leaves(&self) -> impl Iterator<Item = NodeID> + '_ {
        self.nodes
            .iter()
            .filter(|(_, n)| n.is_leaf())
            .map(|(i, _)| i)
            .copied()
    }

    pub fn len(&self) -> NodeID {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn nodes_mut(&mut self) -> impl Iterator<Item = &mut Node<P, E>> {
        self.nodes.values_mut()
    }

    fn insert_node(&mut self, parent: Option<NodeID>, n: Node<P, E>) -> NodeID {
        self.current_id = self.current_id.checked_add(1).expect("Tree is too big");
        let id = self.current_id;
        assert!(!self.nodes.contains_key(&id), "{} already exists", id);
        assert!(parent.is_none() || self.nodes.contains_key(&parent.unwrap()));
        self.nodes.insert(id, n);
        if let Some(parent) = parent {
            self[parent].children.push(id);
        }

        if self.nodes.len() == 1 {
            self.root = id;
        }
        id
    }

    pub fn add_node(&mut self, parent: Option<NodeID>, data: P) -> NodeID {
        if let Some(parent) = parent {
            assert!(self.nodes.contains_key(&parent));
        }

        self.insert_node(
            parent,
            Node {
                parent,
                children: vec![],
                branch: None,
                data,
            },
        )
    }

    pub fn plug(&mut self, target: NodeID, n: NodeID) {
        assert!(self.nodes[&n].parent.is_none());
        assert!(!self.nodes[&target].children.contains(&n));
        self.nodes.get_mut(&n).unwrap().parent = Some(target);
        self.nodes.get_mut(&target).unwrap().children.push(n)
    }

    pub fn unplug(&mut self, n: NodeID) {
        let parent = self.nodes[&n].parent;
        assert!(parent.is_none() || self.nodes[&parent.unwrap()].children.contains(&n));

        self.nodes.get_mut(&n).unwrap().parent = None;
        if let Some(parent) = parent {
            self.nodes
                .get_mut(&parent)
                .unwrap()
                .children
                .retain(|nn| *nn != n);
        }
    }

    pub fn delete_node(&mut self, n: NodeID) -> Option<()> {
        assert!(self.nodes.contains_key(&n));
        for c in self[n].children.clone().into_iter() {
            self.delete_node(c);
        }
        self.unplug(n);
        self.nodes.remove(&n).map(|_| ())
    }

    pub fn delete_nodes(&mut self, ns: &[NodeID]) -> Option<()> {
        for n in ns {
            self.delete_node(*n)?;
        }
        Some(())
    }

    pub fn move_node(&mut self, n: NodeID, dest: NodeID) {
        self.unplug(n);
        self.plug(dest, n);
    }

    fn print_node<
        NodeFormatter: Fn(&P) -> S1,
        S1: Default + Display,
        EdgeFormatter: Fn(&E) -> S2,
        S2: Default + Display,
    >(
        &self,
        n: NodeID,
        indent: NodeID,
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
        self[n]
            .children
            .iter()
            .for_each(|c| self.print_node(*c, indent + 2, f, g))
    }
    pub fn print<
        NodeFormatter: Fn(&P) -> S1,
        S1: Default + Display,
        EdgeFormatter: Fn(&E) -> S2,
        S2: Default + Display,
    >(
        &self,
        f: NodeFormatter,
        g: EdgeFormatter,
    ) {
        if !self.nodes.is_empty() {
            self.print_node(self.root, 0, &f, &g);
        }
    }

    pub fn parent(&self, n: NodeID) -> Option<NodeID> {
        self[n].parent
    }

    pub fn find_leaf<F>(&self, f: F) -> Option<NodeID>
    where
        F: Fn(&P) -> bool,
    {
        self.nodes
            .iter()
            .filter(|(_, n)| n.is_leaf())
            .find(|(_i, n)| f(&n.data))
            .map(|(i, _)| *i)
    }

    pub fn find_node<F>(&self, f: F) -> Option<NodeID>
    where
        F: Fn(&P) -> bool,
    {
        self.nodes
            .iter()
            .find(|(_i, n)| f(&n.data))
            .map(|(i, _)| *i)
    }

    pub fn find_child<F>(&self, n: NodeID, f: F) -> Result<Option<NodeID>, Error>
    where
        F: Fn(&P) -> bool,
    {
        Ok(self
            .children(n)?
            .iter()
            .cloned()
            .find(|&n| f(self[n].data())))
    }

    pub fn mrca(&self, nodes: impl IntoIterator<Item = NodeID>) -> Result<Option<NodeID>, Error> {
        let mut nodes = nodes.into_iter();
        let first = if let Some(node) = nodes.next() {
            node
        } else {
            return Ok(None);
        };

        let ancestors = self.ascendance(first);
        let ranks = ancestors
            .iter()
            .copied()
            .enumerate()
            .map(|(i, j)| (j, i))
            .collect::<IntMap<_, _>>();
        let mut checked = IntSet::<NodeID>::from_iter(ancestors.iter().copied());
        let mut oldest: NodeID = 0;

        for species in nodes {
            let mut species: NodeID = species;
            while !checked.contains(&species) {
                checked.insert(species);
                species = self.nodes[&species].parent.unwrap();
                oldest = oldest.max(*ranks.get(&species).unwrap_or(&0));
            }
        }

        Ok(Some(ancestors[oldest]))
    }

    pub fn ascendance(&self, n: NodeID) -> Vec<NodeID> {
        let mut r = Vec::new();
        let mut parent = Some(n);

        while let Some(me) = parent {
            r.push(me);
            parent = self.parent(me);
        }

        r
    }

    pub fn descendants(&self, n: NodeID) -> Vec<NodeID> {
        fn find_descendants<PP, DD, EE>(t: &Tree<PP, DD, EE>, n: NodeID, ax: &mut Vec<NodeID>) {
            ax.push(n);
            for &c in t[n].children.iter() {
                find_descendants(t, c, ax);
            }
        }

        let mut r = vec![];
        for &c in self[n].children.iter() {
            find_descendants(self, c, &mut r);
        }
        r
    }

    pub fn leave_set_of(&self, n: NodeID) -> IntSet<NodeID> {
        fn find_descendants_leaves<PP, DD, EE>(
            t: &Tree<PP, DD, EE>,
            n: NodeID,
            ax: &mut IntSet<NodeID>,
        ) {
            if t[n].is_leaf() {
                ax.insert(n);
            } else {
                for &c in t[n].children.iter() {
                    find_descendants_leaves(t, c, ax);
                }
            }
        }

        let mut r = Default::default();
        find_descendants_leaves(self, n, &mut r);
        r
    }

    pub fn leaves_of(&self, n: NodeID) -> Vec<NodeID> {
        self.leave_set_of(n).into_iter().collect()
    }

    pub fn cache_descendants(&mut self) {
        let mut me = self.root;
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

    pub fn cache_descendants_of(&mut self, from: NodeID) {
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

    pub fn cached_descendants(&self, n: NodeID) -> Option<&Vec<NodeID>> {
        self._descendants.get(&n)
    }

    pub fn cache_leaves(&mut self) {
        for &k in self.nodes.keys() {
            self._spans_set.insert(k, self.leave_set_of(k));
        }
    }

    pub fn cached_leaves_of(&self, n: NodeID) -> &IntSet<NodeID> {
        &self._spans_set[&n]
    }

    pub fn cached_leaves_of_vec(&self, n: NodeID) -> Vec<NodeID> {
        let mut r = Vec::with_capacity(self._spans_set[&n].len());
        r.extend(self._spans_set[&n].iter().copied());
        r
    }

    pub fn children(&self, n: NodeID) -> Result<&[NodeID], Error> {
        Ok(self.get(n)?.children())
    }

    pub fn siblings(&self, n: NodeID) -> Vec<NodeID> {
        if let Some(parent) = self[n].parent {
            self.descendants(parent)
                .into_iter()
                .filter(|&nn| nn != n)
                .filter(|n| self[*n].is_leaf())
                .collect()
        } else {
            vec![]
        }
    }

    pub fn depth(&self) -> f32 {
        todo!()
    }

    pub fn node_depth<Measure: Fn(&E) -> f32>(&self, n: NodeID, f: &Measure) -> f32 {
        let mut depth = self[n].branch.as_ref().map(f).unwrap_or(0.);
        let mut n = n;
        while let Some(parent) = self[n].parent {
            depth += self[parent].branch.as_ref().map(f).unwrap_or(0.);
            n = parent;
        }
        depth
    }

    /// Returns the topological depth of the
    pub fn node_topological_depth(&self, n: NodeID) -> Result<usize, Error> {
        let mut depth = 0;
        let mut n = n;
        while let Some(parent) = self.nodes.get(&n).ok_or(Error::NodeNotFound(n))?.parent {
            depth += 1;
            n = parent;
        }
        Ok(depth)
    }

    pub fn topological_depth(&self) -> (NodeID, usize) {
        fn _rec_depth<PP, DD, EE>(t: &Tree<PP, DD, EE>, n: NodeID) -> (NodeID, usize) {
            if t[n].is_leaf() {
                (0, n)
            } else {
                let (n, d) = t[n]
                    .children()
                    .iter()
                    .map(|&c| _rec_depth(t, c))
                    .max_by_key(|(_, d)| *d)
                    .unwrap_or_default();
                (n, d + 1)
            }
        }

        _rec_depth(self, 0)
    }

    pub fn for_each_leave<F: FnMut(&Node<P, E>)>(&self, f: &mut F) {
        self.nodes.values().filter(|n| n.is_leaf()).for_each(f);
    }

    pub fn for_each_leave_mut<F: FnMut(&mut Node<P, E>)>(&mut self, f: &mut F) {
        self.nodes.values_mut().filter(|n| n.is_leaf()).for_each(f);
    }

    pub fn inners(&self) -> impl Iterator<Item = NodeID> + '_ {
        self.nodes
            .keys()
            .filter(move |n| !self.nodes[n].is_leaf())
            .copied()
    }

    pub fn prune_by<U: Fn(&Node<P, E>) -> bool>(&mut self, is_useless: &U) {
        loop {
            let todo = self.nodes.keys().cloned().find(|k| is_useless(&self[*k]));

            if let Some(k) = todo {
                let children = self[k].children().to_vec();
                for c in children {
                    self.move_node(c, self[k].parent.unwrap());
                }
                self.delete_node(k);
            } else {
                break;
            }
        }
    }

    // Remove empty inner nodes (i.e. nodes without content nor children)
    // and compress redundant inner nodes (i.e. nodes with a single child and no content)
    pub fn prune(&mut self, is_empty: impl Fn(&P) -> bool) {
        self.prune_by(&|n: &Node<P, E>| {
            (n.children().is_empty() && is_empty(&n.data))
                || (n.children().len() == 1 && is_empty(&n.data))
        });
    }

    fn rec_sort_by<K: Ord + Clone + std::fmt::Debug>(
        &mut self,
        n: NodeID,
        k: &impl Fn(&P) -> K,
        by_leaves: bool,
    ) -> K {
        let mut children = self[n].children.clone();
        children.sort_by_cached_key(|c| k(self[*c].data()));
        self[n].children = children;

        if by_leaves || self[n].children.is_empty() {
            k(&self[n].data)
        } else {
            k(&self[self[n].children[0]].data)
        }
    }

    pub fn sort_by<K: std::fmt::Debug + Ord + Clone>(&mut self, k: impl Fn(&P) -> K) {
        let _ = self.rec_sort_by(self.root(), &k, false);
    }

    pub fn sort_leaves_by<K: std::fmt::Debug + Ord + Clone>(&mut self, k: impl Fn(&P) -> K) {
        let _ = self.rec_sort_by(self.root(), &k, true);
    }
}
impl<'a, P: Ord, D, E> Tree<P, D, E> {
    fn rec_sort(&'a mut self, n: NodeID, by_leaves: bool) -> &P {
        let mut children = self[n].children.clone();
        children.sort_by_cached_key(|c| self[*c].data());
        self[n].children = children;

        if by_leaves || self[n].children.is_empty() {
            &self[n].data
        } else {
            &self[self[n].children[0]].data
        }
    }

    pub fn sort(&'a mut self) {
        let _ = self.rec_sort(self.root(), false);
    }

    pub fn sort_leaves(&'a mut self) {
        let _ = self.rec_sort(self.root(), true);
    }
}
impl<P, D, E> std::ops::Index<NodeID> for Tree<P, D, E> {
    type Output = Node<P, E>;
    fn index(&self, i: usize) -> &Self::Output {
        &self.nodes[&i]
    }
}
impl<P, D, E> std::ops::IndexMut<usize> for Tree<P, D, E> {
    fn index_mut(&mut self, i: NodeID) -> &mut Self::Output {
        self.nodes.get_mut(&i).unwrap()
    }
}
