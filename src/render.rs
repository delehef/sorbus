use std::fmt::Display;

use crate::{NodeHandle, Tree};

impl<P, D, E> Tree<P, D, E> {
    pub fn to_newick<
        NodeFormatter: Fn(&P) -> S1,
        S1: Display + Default,
        EdgeFormatter: Fn(&E) -> S2,
        S2: Display + Default,
    >(
        &self,
        fmt_node: NodeFormatter,
        fmt_edge: EdgeFormatter,
    ) -> String {
        fn render_node<
            PP,
            DD,
            EE,
            NodeFormatter: Fn(&PP) -> S1,
            EdgeFormatter: Fn(&EE) -> S2,
            S1: Display + Default,
            S2: Display + Default,
        >(
            t: &Tree<PP, DD, EE>,
            n: NodeHandle,
            r: &mut String,
            fmt_node: &NodeFormatter,
            fmt_edge: &EdgeFormatter,
        ) {
            if t[n].is_leaf() {
                r.push_str(&fmt_node(&t[n].data).to_string());
                if let Some(e) = t[n].branch.as_ref() {
                    r.push_str(&format!(":{}", fmt_edge(e)));
                }
            } else {
                r.push('(');

                let mut children = t[n].children().iter().peekable();
                while let Some(c) = children.next() {
                    render_node(t, *c, r, fmt_node, fmt_edge);
                    if children.peek().is_some() {
                        r.push_str(",\n");
                    }
                }
                r.push(')');
                r.push_str(&fmt_node(&t[n].data).to_string());
                if let Some(e) = t[n].branch.as_ref() {
                    r.push_str(&format!(":{}", fmt_edge(e)));
                }
            }
        }
        let mut r = String::new();
        render_node(self, self.root(), &mut r, &fmt_node, &fmt_edge);
        r.push(';');
        r
    }
    pub fn to_string<
        NodeFormatter: Fn(&P) -> S1,
        S1: Display + Default,
        EdgeFormatter: Fn(&E) -> S2,
        S2: Display + Default,
    >(
        &self,
        fmt_node: NodeFormatter,
        fmt_edge: EdgeFormatter,
        only_leaves: bool,
    ) -> String {
        fn render_node<
            PP,
            DD,
            EE,
            NodeFormatter: Fn(&PP) -> S1,
            EdgeFormatter: Fn(&EE) -> S2,
            S1: Display + Default,
            S2: Display + Default,
        >(
            t: &Tree<PP, DD, EE>,
            n: NodeHandle,
            r: &mut String,
            indent: usize,
            only_leaves: bool,
            fmt_node: &NodeFormatter,
            fmt_edge: &EdgeFormatter,
        ) {
            if t[n].is_leaf() {
                r.push_str(&" ".repeat(indent));
                r.push_str(&fmt_node(&t[n].data).to_string());
                if let Some(e) = t[n].branch.as_ref() {
                    r.push_str(&format!(" {}", fmt_edge(e)));
                }
                r.push('\n');
            } else {
                if !only_leaves {
                    r.push_str(&" ".repeat(indent));
                    r.push_str(&fmt_node(&t[n].data).to_string());
                    if let Some(e) = t[n].branch.as_ref() {
                        r.push_str(&format!(":{}", fmt_edge(e)));
                    }
                    r.push('\n');
                }

                let mut children = t[n].children().iter().peekable();
                while let Some(c) = children.next() {
                    render_node(t, *c, r, indent + 2, only_leaves, fmt_node, fmt_edge);
                }
            }
        }

        let mut r = String::new();
        render_node(
            self,
            self.root(),
            &mut r,
            0,
            only_leaves,
            &fmt_node,
            &fmt_edge,
        );
        r
    }
}
