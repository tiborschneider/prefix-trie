use crate::{to_right, Prefix, PrefixMap};

#[derive(Clone)]
/// an iterator over all entries of two [`crate::PrefixSet`]s in lexicographic order.
pub struct Union<'a, P> {
    pub(super) set_a: &'a PrefixMap<P, ()>,
    pub(super) set_b: &'a PrefixMap<P, ()>,
    pub(super) nodes: Vec<UnionIndex>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub(super) enum UnionIndex {
    Both(usize, usize),
    FirstA(usize, usize),
    FirstB(usize, usize),
    OnlyA(usize),
    OnlyB(usize),
}

impl<'a, P: Prefix> Iterator for Union<'a, P> {
    type Item = &'a P;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(cur) = self.nodes.pop() {
            match cur {
                UnionIndex::Both(a, b) => {
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
                    if node_a.value.is_some() || node_b.value.is_some() {
                        return Some(&node_a.prefix);
                    }
                }
                UnionIndex::FirstA(a, b) => {
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
                UnionIndex::FirstB(a, b) => {
                    let node_b = &self.set_b.table[b];
                    self.nodes.extend(next_indices_first_b(
                        self.set_a,
                        self.set_b,
                        a,
                        b,
                        node_b.left,
                        node_b.right,
                    ));
                    if node_b.value.is_some() {
                        return Some(&node_b.prefix);
                    }
                }
                UnionIndex::OnlyA(a) => {
                    let node_a = &self.set_a.table[a];
                    if let Some(right) = node_a.right {
                        self.nodes.push(UnionIndex::OnlyA(right));
                    }
                    if let Some(left) = node_a.left {
                        self.nodes.push(UnionIndex::OnlyA(left));
                    }
                    if node_a.value.is_some() {
                        return Some(&node_a.prefix);
                    }
                }
                UnionIndex::OnlyB(b) => {
                    let node_b = &self.set_b.table[b];
                    if let Some(right) = node_b.right {
                        self.nodes.push(UnionIndex::OnlyB(right));
                    }
                    if let Some(left) = node_b.left {
                        self.nodes.push(UnionIndex::OnlyB(left));
                    }
                    if node_b.value.is_some() {
                        return Some(&node_b.prefix);
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
) -> Vec<UnionIndex> {
    match (node_a, node_b) {
        (None, Some(b)) => vec![UnionIndex::OnlyB(b)],
        (Some(a), None) => vec![UnionIndex::OnlyA(a)],
        (Some(a), Some(b)) => {
            let p_a = &set_a.table[a].prefix;
            let p_b = &set_b.table[b].prefix;
            if p_a.prefix_len() == p_b.prefix_len() {
                match p_a.mask().cmp(&p_b.mask()) {
                    std::cmp::Ordering::Less => {
                        vec![UnionIndex::OnlyB(b), UnionIndex::OnlyA(a)]
                    }
                    std::cmp::Ordering::Equal => {
                        vec![UnionIndex::Both(a, b)]
                    }
                    std::cmp::Ordering::Greater => {
                        vec![UnionIndex::OnlyA(a), UnionIndex::OnlyB(b)]
                    }
                }
            } else if p_a.contains(p_b) {
                vec![UnionIndex::FirstA(a, b)]
            } else if p_b.contains(p_a) {
                vec![UnionIndex::FirstB(a, b)]
            } else {
                if p_a.mask() < p_b.mask() {
                    vec![UnionIndex::OnlyB(b), UnionIndex::OnlyA(a)]
                } else {
                    vec![UnionIndex::OnlyA(a), UnionIndex::OnlyB(b)]
                }
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
) -> Vec<UnionIndex> {
    match (a_left, a_right) {
        (None, None) => vec![UnionIndex::OnlyB(b)],
        (None, Some(r)) => next_indices(set_a, set_b, Some(r), Some(b)),
        (Some(l), None) => next_indices(set_a, set_b, Some(l), Some(b)),
        (Some(l), Some(r)) => {
            if to_right(&set_a.table[a].prefix, &set_b.table[b].prefix) {
                let mut idxes = next_indices(set_a, set_b, Some(r), Some(b));
                idxes.push(UnionIndex::OnlyA(l));
                idxes
            } else {
                let mut idxes = next_indices(set_a, set_b, Some(l), Some(b));
                idxes.insert(0, UnionIndex::OnlyA(r));
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
) -> Vec<UnionIndex> {
    match (b_left, b_right) {
        (None, None) => vec![UnionIndex::OnlyA(a)],
        (None, Some(r)) => next_indices(set_a, set_b, Some(a), Some(r)),
        (Some(l), None) => next_indices(set_a, set_b, Some(a), Some(l)),
        (Some(l), Some(r)) => {
            if to_right(&set_b.table[b].prefix, &set_a.table[a].prefix) {
                let mut idxes = next_indices(set_a, set_b, Some(a), Some(r));
                idxes.push(UnionIndex::OnlyB(l));
                idxes
            } else {
                let mut idxes = next_indices(set_a, set_b, Some(a), Some(l));
                idxes.insert(0, UnionIndex::OnlyB(r));
                idxes
            }
        }
    }
}
