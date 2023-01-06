use std::collections::{HashMap, HashSet};

pub type NodeID = usize;

pub struct Node<T> {
    parent: Option<NodeID>,
    children: Vec<NodeID>,
    pub branch_length: Option<f32>,
    pub data: T,
}
impl<T> Node<T> {
    pub fn is_leaf(&self) -> bool {
        self.children.is_empty()
    }
    pub fn children(&self) -> &[NodeID] {
        &self.children
    }
}

pub struct Tree<P> {
    root: NodeID,
    current_id: NodeID,
    nodes: HashMap<NodeID, Node<P>>,
    _spans: HashMap<NodeID, Vec<NodeID>>,
    _descendants: HashMap<NodeID, Vec<NodeID>>,
}

impl<P> Default for Tree<P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P> Tree<P> {
    pub fn new() -> Self {
        Self {
            root: 0,
            current_id: 0,
            nodes: HashMap::new(),
            _spans: HashMap::new(),
            _descendants: HashMap::new(),
        }
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

    pub fn nodes(&self) -> impl Iterator<Item = &Node<P>> {
        self.nodes.values()
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

    pub fn add_node(&mut self, parent: Option<NodeID>, data: P) -> NodeID {
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

    fn print_node<F: Fn(&P) -> S, S: AsRef<str>>(nodes: &[&Node<P>], n: NodeID, o: NodeID, f: &F) {
        println!(
            "{}{}:{:?}",
            str::repeat(" ", o),
            f(&nodes[n].data).as_ref(),
            nodes[n].branch_length.unwrap_or(-1.),
        );
        nodes[n]
            .children
            .iter()
            .for_each(|c| Tree::<P>::print_node(nodes, *c, o + 2, f))
    }
    pub fn print<F: Fn(&P) -> S, S: AsRef<str>>(&self, f: F) {
        if !self.nodes.is_empty() {
            Tree::<P>::print_node(&self.nodes.values().collect::<Vec<_>>(), self.root, 0, &f);
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

    pub fn mrca<'a>(&self, nodes: impl IntoIterator<Item = &'a NodeID>) -> Option<NodeID> {
        let mut nodes = nodes.into_iter();
        let first = if let Some(node) = nodes.next() {
            *node
        } else {
            return None;
        };

        let ancestors = self.ascendance(first);
        let ranks = ancestors
            .iter()
            .enumerate()
            .map(|(i, j)| (j, i))
            .collect::<HashMap<_, _>>();
        let mut checked = HashSet::<NodeID>::from_iter(ancestors.iter().copied());
        let mut oldest: NodeID = 0;

        for species in nodes {
            let mut species: NodeID = *species;
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
        fn find_descendants<PP>(t: &Tree<PP>, n: NodeID, ax: &mut Vec<NodeID>) {
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

    pub fn leaves_of(&self, n: NodeID) -> Vec<NodeID> {
        fn find_descendants_leaves<PP>(t: &Tree<PP>, n: NodeID, ax: &mut Vec<NodeID>) {
            if t[n].is_leaf() {
                ax.push(n);
            } else {
                for &c in t[n].children.iter() {
                    find_descendants_leaves(t, c, ax);
                }
            }
        }

        let mut r = vec![];
        find_descendants_leaves(self, n, &mut r);
        r
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
            self._spans.insert(k, self.leaves_of(k));
        }
    }

    pub fn cached_leaves_of(&self, n: NodeID) -> &[NodeID] {
        &self._spans[&n]
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

    pub fn leaves(&self) -> impl Iterator<Item = NodeID> + '_ {
        self.nodes
            .iter()
            .filter(|(_, n)| n.is_leaf())
            .map(|(i, _)| i)
            .copied()
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

    pub fn to_newick<ID: Fn(&P) -> S, S: AsRef<str>>(&self, node_to_id: ID) -> String {
        fn fmt_node<PP, ID: Fn(&PP) -> S, S: AsRef<str>>(
            t: &Tree<PP>,
            n: NodeID,
            r: &mut String,
            node_to_id: &ID,
        ) {
            if t[n].is_leaf() {
                r.push_str(node_to_id(&t[n].data).as_ref());
                if let Some(l) = t[n].branch_length {
                    r.push_str(&format!(":{}", l));
                }
            } else {
                r.push('(');

                let mut children = t[n].children().iter().peekable();
                while let Some(c) = children.next() {
                    fmt_node(t, *c, r, node_to_id);
                    if children.peek().is_some() {
                        r.push_str(",\n");
                    }
                }
                r.push(')');
                r.push_str(node_to_id(&t[n].data).as_ref());
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

    pub fn prune(&mut self) {
        // Remove empty inner nodes (i.e. nodes without content nor children)
        loop {
            let todos = tree
                .nodes()
                .copied()
                .filter(|&k| tree[k].children.is_empty() && tree[k].content.is_empty())
                .collect::<Vec<_>>();
            if todos.is_empty() {
                break;
            } else {
                tree.delete_nodes(&todos);
            }
        }

        // Compress redundant outer nodes (i.e. nodes with a single content and no child)
        loop {
            let todo = tree
                .nodes()
                .copied()
                .find(|&k| tree[k].children.is_empty() && tree[k].content.len() == 1 && k != root);

            if let Some(k) = todo {
                let content = tree[k].content[0];
                let parent = tree[k].parent.unwrap();
                tree[parent].content.push(content);
                tree.delete_node(k);
            } else {
                break;
            }
        }

        // Compress redundant inner nodes (i.e. nodes with a single child and no content)
        loop {
            let todo = tree
                .nodes()
                .copied()
                .find(|&k| k != root && tree[k].children.len() == 1 && tree[k].content.is_empty());

            if let Some(k) = todo {
                tree.move_node(tree[k].children[0], tree[k].parent.unwrap());
                tree.delete_node(k);
            } else {
                break;
            }
        }
    }
}
impl<P> std::ops::Index<usize> for Tree<P> {
    type Output = Node<P>;
    fn index(&self, i: usize) -> &Self::Output {
        &self.nodes[&i]
    }
}
impl<P> std::ops::IndexMut<usize> for Tree<P> {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        self.nodes.get_mut(&i).unwrap()
    }
}
