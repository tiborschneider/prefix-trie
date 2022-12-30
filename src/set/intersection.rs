use crate::{to_right, Prefix, PrefixMap};

#[derive(Clone)]
/// an iterator over the intersection of two [`crate::PrefixSet`]s in lexicographic order.
pub struct Intersection<'a, P> {
    pub(super) set_a: &'a PrefixMap<P, ()>,
    pub(super) set_b: &'a PrefixMap<P, ()>,
    pub(super) nodes: Vec<IntersectionIndex>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub(super) enum IntersectionIndex {
    Both(usize, usize),
    FirstA(usize, usize),
    FirstB(usize, usize),
}

impl<'a, P: Prefix> Iterator for Intersection<'a, P> {
    type Item = &'a P;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(cur) = self.nodes.pop() {
            match cur {
                IntersectionIndex::Both(a, b) => {
                    let node_a = &self.set_a.table[a];
                    let node_b = &self.set_b.table[b];
                    self.nodes.extend(next_indices(
                        self.set_a,
                        self.set_b,
                        node_a.right,
                        node_b.right,
                    ));
                    self.nodes.extend(next_indices(
                        self.set_a,
                        self.set_b,
                        node_a.left,
                        node_b.left,
                    ));
                    if node_a.value.is_some() && node_b.value.is_some() {
                        return Some(&node_a.prefix);
                    }
                }
                IntersectionIndex::FirstA(a, b) => {
                    let node_a = &self.set_a.table[a];
                    self.nodes.extend(next_indices_first_a(
                        self.set_a,
                        self.set_b,
                        a,
                        node_a.left,
                        node_a.right,
                        b,
                    ));
                }
                IntersectionIndex::FirstB(a, b) => {
                    let node_b = &self.set_b.table[b];
                    self.nodes.extend(next_indices_first_b(
                        self.set_a,
                        self.set_b,
                        a,
                        b,
                        node_b.left,
                        node_b.right,
                    ));
                }
            }
        }
        None
    }
}

fn next_indices<'a, P: Prefix>(
    set_a: &'a PrefixMap<P, ()>,
    set_b: &'a PrefixMap<P, ()>,
    node_a: Option<usize>,
    node_b: Option<usize>,
) -> Option<IntersectionIndex> {
    match (node_a, node_b) {
        (None, Some(_)) => None,
        (Some(_), None) => None,
        (Some(a), Some(b)) => {
            let p_a = &set_a.table[a].prefix;
            let p_b = &set_b.table[b].prefix;
            if p_a.prefix_len() == p_b.prefix_len() {
                match p_a.mask().cmp(&p_b.mask()) {
                    std::cmp::Ordering::Equal => Some(IntersectionIndex::Both(a, b)),
                    _ => None,
                }
            } else if p_a.contains(p_b) {
                Some(IntersectionIndex::FirstA(a, b))
            } else if p_b.contains(p_a) {
                Some(IntersectionIndex::FirstB(a, b))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn next_indices_first_a<'a, P: Prefix>(
    set_a: &'a PrefixMap<P, ()>,
    set_b: &'a PrefixMap<P, ()>,
    a: usize,
    a_left: Option<usize>,
    a_right: Option<usize>,
    b: usize,
) -> Option<IntersectionIndex> {
    match (a_left, a_right) {
        (None, None) => None,
        (None, Some(r)) => next_indices(set_a, set_b, Some(r), Some(b)),
        (Some(l), None) => next_indices(set_a, set_b, Some(l), Some(b)),
        (Some(l), Some(r)) => {
            if to_right(&set_a.table[a].prefix, &set_b.table[b].prefix) {
                next_indices(set_a, set_b, Some(r), Some(b))
            } else {
                next_indices(set_a, set_b, Some(l), Some(b))
            }
        }
    }
}

fn next_indices_first_b<'a, P: Prefix>(
    set_a: &'a PrefixMap<P, ()>,
    set_b: &'a PrefixMap<P, ()>,
    a: usize,
    b: usize,
    b_left: Option<usize>,
    b_right: Option<usize>,
) -> Option<IntersectionIndex> {
    match (b_left, b_right) {
        (None, None) => None,
        (None, Some(r)) => next_indices(set_a, set_b, Some(a), Some(r)),
        (Some(l), None) => next_indices(set_a, set_b, Some(a), Some(l)),
        (Some(l), Some(r)) => {
            if to_right(&set_b.table[b].prefix, &set_a.table[a].prefix) {
                next_indices(set_a, set_b, Some(a), Some(r))
            } else {
                next_indices(set_a, set_b, Some(a), Some(l))
            }
        }
    }
}
