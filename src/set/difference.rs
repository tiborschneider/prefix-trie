use crate::{to_right, Prefix, PrefixMap};

#[derive(Clone)]
/// an iterator over the difference of two [`crate::PrefixSet`]s in lexicographic order.
pub struct Difference<'a, P> {
    pub(super) set_a: &'a PrefixMap<P, ()>,
    pub(super) set_b: &'a PrefixMap<P, ()>,
    pub(super) nodes: Vec<DifferenceIndex>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub(super) enum DifferenceIndex {
    Both(usize, usize),
    FirstA(usize, usize),
    FirstB(usize, usize),
    OnlyA(usize),
}

impl<'a, P: Prefix> Iterator for Difference<'a, P> {
    type Item = &'a P;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(cur) = self.nodes.pop() {
            match cur {
                DifferenceIndex::Both(a, b) => {
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
                    if node_a.value.is_some() && node_b.value.is_none() {
                        return Some(&node_a.prefix);
                    }
                }
                DifferenceIndex::FirstA(a, b) => {
                    let node_a = &self.set_a.table[a];
                    self.nodes.extend(next_indices_first_a(
                        self.set_a,
                        self.set_b,
                        a,
                        node_a.left,
                        node_a.right,
                        b,
                    ));
                    if node_a.value.is_some() {
                        return Some(&node_a.prefix);
                    }
                }
                DifferenceIndex::FirstB(a, b) => {
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
                DifferenceIndex::OnlyA(a) => {
                    let node_a = &self.set_a.table[a];
                    if let Some(right) = node_a.right {
                        self.nodes.push(DifferenceIndex::OnlyA(right));
                    }
                    if let Some(left) = node_a.left {
                        self.nodes.push(DifferenceIndex::OnlyA(left));
                    }
                    if node_a.value.is_some() {
                        return Some(&node_a.prefix);
                    }
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
) -> Vec<DifferenceIndex> {
    match (node_a, node_b) {
        (None, Some(_)) => vec![],
        (Some(a), None) => vec![DifferenceIndex::OnlyA(a)],
        (Some(a), Some(b)) => {
            let p_a = &set_a.table[a].prefix;
            let p_b = &set_b.table[b].prefix;
            if p_a.prefix_len() == p_b.prefix_len() {
                match p_a.mask().cmp(&p_b.mask()) {
                    std::cmp::Ordering::Equal => {
                        vec![DifferenceIndex::Both(a, b)]
                    }
                    _ => {
                        vec![DifferenceIndex::OnlyA(a)]
                    }
                }
            } else if p_a.contains(p_b) {
                vec![DifferenceIndex::FirstA(a, b)]
            } else if p_b.contains(p_a) {
                vec![DifferenceIndex::FirstB(a, b)]
            } else {
                vec![DifferenceIndex::OnlyA(a)]
            }
        }
        _ => vec![],
    }
}

fn next_indices_first_a<'a, P: Prefix>(
    set_a: &'a PrefixMap<P, ()>,
    set_b: &'a PrefixMap<P, ()>,
    a: usize,
    a_left: Option<usize>,
    a_right: Option<usize>,
    b: usize,
) -> Vec<DifferenceIndex> {
    match (a_left, a_right) {
        (None, None) => vec![],
        (None, Some(r)) => next_indices(set_a, set_b, Some(r), Some(b)),
        (Some(l), None) => next_indices(set_a, set_b, Some(l), Some(b)),
        (Some(l), Some(r)) => {
            if to_right(&set_a.table[a].prefix, &set_b.table[b].prefix) {
                let mut idxes = next_indices(set_a, set_b, Some(r), Some(b));
                idxes.push(DifferenceIndex::OnlyA(l));
                idxes
            } else {
                let mut idxes = next_indices(set_a, set_b, Some(l), Some(b));
                idxes.insert(0, DifferenceIndex::OnlyA(r));
                idxes
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
) -> Vec<DifferenceIndex> {
    match (b_left, b_right) {
        (None, None) => vec![DifferenceIndex::OnlyA(a)],
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
