use identity_hash::{IntMap, IntSet};

pub type NodeID = usize;

pub struct Node<P> {
    parent: Option<NodeID>,
    children: Vec<NodeID>,
    pub branch_length: Option<f32>,
    data: Option<P>,
}
impl<P> Node<P> {
    pub fn is_leaf(&self) -> bool {
        self.children.is_empty()
    }
    pub fn children(&self) -> &[NodeID] {
        &self.children
    }

    pub fn data(&self) -> Option<&P> {
        self.data.as_ref()
    }

    pub fn data_mut(&mut self) -> Option<&mut P> {
        self.data.as_mut()
    }

    pub fn unwrap_data(&self) -> &P {
        self.data.as_ref().unwrap()
    }

    pub fn unwrap_data_mut(&mut self) -> &mut P {
        self.data.as_mut().unwrap()
    }
}

pub struct Tree<P, D> {
    root: NodeID,
    current_id: NodeID,
    metadata: D,
    nodes: IntMap<NodeID, Node<P>>,
    _spans_set: IntMap<NodeID, IntSet<NodeID>>,
    _descendants: IntMap<NodeID, Vec<NodeID>>,
}

impl<P, D> Default for Tree<P, D>
where
    D: Default,
{
    fn default() -> Self {
        Self::with_metadata(D::default())
    }
}
impl<P, D> Tree<P, D>
where
    D: Default,
{
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

impl<P, D> Tree<P, D> {
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

    pub fn data(&self, n: NodeID) -> Option<&P> {
        self[n].data.as_ref()
    }

    pub fn data_mut(&mut self, n: NodeID) -> Option<&mut P> {
        self[n].data.as_mut()
    }

    pub fn unwrap_data(&self, n: NodeID) -> &P {
        self[n].data.as_ref().unwrap()
    }

    pub fn unwrap_data_mut(&mut self, n: NodeID) -> &mut P {
        self[n].data.as_mut().unwrap()
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

    pub fn nodes_mut(&mut self) -> impl Iterator<Item = &mut Node<P>> {
        self.nodes.values_mut()
    }

    fn insert_node(&mut self, parent: Option<NodeID>, n: Node<P>) -> NodeID {
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

    pub fn add_node(&mut self, parent: Option<NodeID>, data: Option<P>) -> NodeID {
        if let Some(parent) = parent {
            assert!(self.nodes.contains_key(&parent));
        }

        self.insert_node(
            parent,
            Node {
                parent,
                children: vec![],
                branch_length: None,
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

    fn print_node<F: Fn(&P) -> S, S: Default + std::fmt::Display>(
        &self,
        n: NodeID,
        indent: NodeID,
        f: &F,
    ) {
        println!(
            "{}{}{}",
            str::repeat(" ", indent),
            self[n].data.as_ref().map(f).unwrap_or_default(),
            self[n]
                .branch_length
                .map(|x| format!(":{}", x))
                .unwrap_or(String::new()),
        );
        self[n]
            .children
            .iter()
            .for_each(|c| self.print_node(*c, indent + 2, f))
    }
    pub fn print<F: Fn(&P) -> S, S: Default + std::fmt::Display>(&self, f: F) {
        if !self.nodes.is_empty() {
            self.print_node(self.root, 0, &f);
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
            .find(|(_i, n)| n.data.as_ref().map(&f).unwrap_or(false))
            .map(|(i, _)| *i)
    }

    pub fn find_node<F>(&self, f: F) -> Option<NodeID>
    where
        F: Fn(&P) -> bool,
    {
        self.nodes
            .iter()
            .find(|(_i, n)| n.data.as_ref().map(&f).unwrap_or(false))
            .map(|(i, _)| *i)
    }

    pub fn find_child<F>(&self, n: NodeID, f: F) -> Option<NodeID>
    where
        F: Fn(&P) -> bool,
    {
        self.children(n)
            .iter()
            .cloned()
            .find(|n| self.data(*n).map(&f).unwrap_or(false))
    }

    pub fn mrca<'a>(&self, nodes: impl IntoIterator<Item = NodeID>) -> Option<NodeID> {
        let mut nodes = nodes.into_iter();
        let first = if let Some(node) = nodes.next() {
            node
        } else {
            return None;
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

        Some(ancestors[oldest])
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
        fn find_descendants<PP, DD>(t: &Tree<PP, DD>, n: NodeID, ax: &mut Vec<NodeID>) {
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
        fn find_descendants_leaves<PP, DD>(t: &Tree<PP, DD>, n: NodeID, ax: &mut IntSet<NodeID>) {
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

    pub fn children(&self, n: NodeID) -> &[NodeID] {
        &self[n].children
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

    pub fn node_depth(&self, n: NodeID) -> f32 {
        let mut depth = self[n].branch_length.unwrap();
        let mut n = n;
        while let Some(parent) = self[n].parent {
            depth += self[parent].branch_length.unwrap();
            n = parent;
        }
        depth
    }

    pub fn node_topological_depth(&self, n: NodeID) -> i64 {
        let mut depth = 0;
        let mut n = n;
        while let Some(parent) = self[n].parent {
            depth += 1;
            n = parent;
        }
        depth
    }

    pub fn topological_depth(&self) -> (NodeID, i64) {
        self.leaves()
            .map(|n| (n, self.node_topological_depth(n)))
            .max_by(|x, y| x.1.partial_cmp(&y.1).unwrap())
            .unwrap()
    }

    pub fn map_leaves<F: FnMut(&mut Node<P>)>(&mut self, f: &mut F) {
        self.nodes.values_mut().filter(|n| n.is_leaf()).for_each(f);
    }

    pub fn inners(&self) -> impl Iterator<Item = NodeID> + '_ {
        self.nodes
            .keys()
            .filter(move |n| !self.nodes[n].is_leaf())
            .copied()
    }

    pub fn to_newick<ID: Fn(&P) -> S, S: std::fmt::Display + Default>(
        &self,
        node_to_id: ID,
    ) -> String {
        fn fmt_node<PP, DD, Render: Fn(&PP) -> S, S: std::fmt::Display + Default>(
            t: &Tree<PP, DD>,
            n: NodeID,
            r: &mut String,
            formatter: &Render,
        ) {
            if t[n].is_leaf() {
                r.push_str(
                    &t[n]
                        .data
                        .as_ref()
                        .map(formatter)
                        .unwrap_or_default()
                        .to_string(),
                );
                if let Some(l) = t[n].branch_length {
                    r.push_str(&format!(":{}", l));
                }
            } else {
                r.push('(');

                let mut children = t[n].children().iter().peekable();
                while let Some(c) = children.next() {
                    fmt_node(t, *c, r, formatter);
                    if children.peek().is_some() {
                        r.push_str(",\n");
                    }
                }
                r.push(')');
                r.push_str(
                    &t[n]
                        .data
                        .as_ref()
                        .map(formatter)
                        .unwrap_or_default()
                        .to_string(),
                );
                if let Some(l) = t[n].branch_length {
                    r.push_str(&format!(":{}", l));
                }
            }
        }
        let mut r = String::new();
        fmt_node(self, self.root, &mut r, &node_to_id);
        r.push(';');
        r
    }

    fn get_mut(&mut self, i: NodeID) -> Option<&mut Node<P>> {
        self.nodes.get_mut(&i)
    }

    pub fn prune_by<U: Fn(&Node<P>) -> bool>(&mut self, is_useless: &U) {
        loop {
            let todo = self
                .nodes
                .keys()
                .cloned()
                .filter(|k| is_useless(&self[*k]))
                .next();

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
    pub fn prune(&mut self) {
        self.prune_by(&|n: &Node<P>| {
            (n.children().is_empty() && n.data.is_none())
                || (n.children().len() == 1 && n.data.is_none())
        });
    }
}
impl<P, D> std::ops::Index<usize> for Tree<P, D> {
    type Output = Node<P>;
    fn index(&self, i: usize) -> &Self::Output {
        &self.nodes[&i]
    }
}
impl<P, D> std::ops::IndexMut<usize> for Tree<P, D> {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        self.nodes.get_mut(&i).unwrap()
    }
}
