pub struct Node<T> {
    parent: usize,
    children: Vec<usize>,
    pub branch_length: Option<f32>,
    pub data: T,
}
impl<T> Node<T> {
    pub fn is_leaf(&self) -> bool {
        self.children.is_empty()
    }
    pub fn children(&self) -> &[usize] {
        &self.children
    }
}

pub struct Tree<P> {
    nodes: Vec<Node<P>>,
}

impl<P> Tree<P> {
    pub fn new() -> Self {
        Self { nodes: vec![] }
    }

    pub fn nodes(&self) -> &[Node<P>] {
        &self.nodes
    }

    fn insert_node(&mut self, parent: usize, n: Node<P>) -> usize {
        self.nodes.push(n);
        let id = self.nodes.len() - 1;
        if !self.nodes.is_empty() && (id != parent) {
            self.nodes[parent].children.push(id);
        }
        id
    }

    pub fn add_node(&mut self, parent: usize, data: P) -> usize {
        self.insert_node(
            parent,
            Node {
                parent: parent,
                children: vec![],
                branch_length: None,
                data: data,
            },
        )
    }

    fn print_node<F: Fn(&P) -> S, S: AsRef<str>>(nodes: &[Node<P>], n: usize, o: usize, f: &F) {
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
            Tree::<P>::print_node(&self.nodes, 0, 0, &f);
        }
    }

    pub fn parent(&self, n: usize) -> Option<usize> {
        if self.nodes[n].parent == 0 {
            None
        } else {
            Some(self.nodes[n].parent)
        }
    }

    pub fn find_leaf<F>(&self, f: F) -> Option<usize>
    where
        F: Fn(&P) -> bool,
    {
        match self
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| n.is_leaf())
            .find(|(_i, n)| f(&n.data))
        {
            Some((i, _)) => Some(i),
            None => None,
        }
    }

    pub fn find_node<F>(&self, f: F) -> Option<usize>
    where
        F: Fn(&P) -> bool,
    {
        match self.nodes.iter().enumerate().find(|(_i, n)| f(&n.data)) {
            Some((i, _)) => Some(i),
            None => None,
        }
    }

    pub fn mrca(&self, nodes: &[usize]) -> Option<usize> {
        if nodes.is_empty() {
            None
        } else {
            let ancestries = nodes
                .iter()
                .map(|&n| self.ascendance(n))
                .collect::<Vec<_>>();

            for p in ancestries[0].iter() {
                if ancestries.iter().all(|a| a.contains(p)) {
                    return Some(*p);
                }
            }
            None
        }
    }

    pub fn ascendance(&self, n: usize) -> Vec<usize> {
        let mut n = n;
        let mut r = vec![n];

        while let Some(x) = self.parent(n) {
            r.push(x);
            n = x;
        }

        r
    }

    pub fn descendants(&self, n: usize) -> Vec<usize> {
        fn find_descendants<PP>(t: &Tree<PP>, n: usize, ax: &mut Vec<usize>) {
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

    pub fn leaves_of(&self, n: usize) -> Vec<usize> {
        fn find_descendants_leaves<PP>(t: &Tree<PP>, n: usize, ax: &mut Vec<usize>) {
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

    pub fn children(&self, n: usize) -> &[usize] {
        &self[n].children
    }

    pub fn siblings(&self, n: usize) -> Vec<usize> {
        self.descendants(self[n].parent)
            .into_iter()
            .filter(|&nn| nn != n)
            .filter(|n| self[*n].is_leaf())
            .collect()
    }

    pub fn depth(&self) -> f32 {
        todo!()
    }

    pub fn node_depth(&self, n: usize) -> f32 {
        let mut depth = self.nodes[n].branch_length.unwrap();
        let mut parent = self.nodes[n].parent;
        while parent != 0 {
            depth += self.nodes[parent].branch_length.unwrap();
            parent = self.nodes[parent].parent;
        }
        depth
    }

    pub fn node_topological_depth(&self, n: usize) -> f32 {
        let mut depth = 0.;
        let mut parent = self.nodes[n].parent;
        while parent != 0 {
            depth += 1.;
            parent = self.nodes[parent].parent;
        }
        depth
    }

    pub fn topological_depth(&self) -> (usize, f32) {
        self.leaves()
            .map(|n| (n, self.node_topological_depth(n)))
            .max_by(|x, y| x.1.partial_cmp(&y.1).unwrap())
            .unwrap()
    }

    pub fn leaves<'a>(&'a self) -> impl Iterator<Item = usize> + 'a {
        (0..self.nodes.len()).filter(move |n| self.nodes[*n].is_leaf())
    }

    pub fn inners<'a>(&'a self) -> impl Iterator<Item = usize> + 'a {
        (0..self.nodes.len()).filter(move |n| !self.nodes[*n].is_leaf())
    }

    pub fn to_newick<ID: Fn(&P) -> S, S: AsRef<str>>(&self, node_to_id: ID) -> String {
        fn fmt_node<PP, ID: Fn(&PP) -> S, S: AsRef<str>>(t: &Tree<PP>, n: usize, r: &mut String, node_to_id: &ID) {
            if t[n].is_leaf() {
                r.push_str(node_to_id(&t[n].data).as_ref());
                t[n].branch_length.map(|l| r.push_str(&format!(":{}", l)));
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
                t[n].branch_length.map(|l| r.push_str(&format!(":{}", l)));
            }
        }
        let mut r = String::new();
        fmt_node(self, 0, &mut r, &node_to_id);
        r.push(';');
        r
    }
}
impl<P> std::ops::Index<usize> for Tree<P> {
    type Output = Node<P>;
    fn index(&self, i: usize) -> &Self::Output {
        &self.nodes[i]
    }
}
impl<P> std::ops::IndexMut<usize> for Tree<P> {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        &mut self.nodes[i]
    }
}
