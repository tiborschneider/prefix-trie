use crate::to_right;

use super::*;

/// An iterator over the difference of two [`TrieView`]s. See [`TrieView::difference`] for more
/// information and an example.
pub struct Difference<'a, P, L, R> {
    map_l: &'a PrefixMap<P, L>,
    map_r: &'a PrefixMap<P, R>,
    nodes: Vec<(DifferenceIndex, Option<(&'a P, &'a R)>)>,
}

/// An iterator over the covering difference of two [`TrieView`]s. See
/// [`TrieView::covering_difference`] for more information and an example.
pub struct CoveringDifference<'a, P, L, R> {
    map_l: &'a PrefixMap<P, L>,
    map_r: &'a PrefixMap<P, R>,
    nodes: Vec<DifferenceIndex>,
}

pub(super) enum DifferenceIndex {
    Both(usize, usize),
    FirstL(usize, usize),
    FirstR(usize, usize),
    OnlyL(usize),
}

/// An item of the [`Difference`] iterator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DifferenceItem<'a, P, L, R> {
    /// The prefix that is present in `self` but not in `other`.
    pub prefix: &'a P,
    /// The value that is stored in `self`.
    pub value: &'a L,
    /// The longest-prefix-match that is present in `other`.
    pub right: Option<(&'a P, &'a R)>,
}

impl<'a, P, L> TrieView<'a, P, L>
where
    P: Prefix,
{
    /// Iterate over the all elements in `self` that are not present in `other`. Each item will
    /// return a reference to the prefix and value in `self`, as well as the longest prefix match of
    /// `other`.
    ///
    /// **Warning**: The iterator will only yield elements of the given views. If `other` points to
    /// a branching node, then the longest prefix match returned may be `None`, even though it
    /// exists in the original map referenced by `other`.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # use prefix_trie::trieview::DifferenceItem;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::Ipv4Net>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map_a: PrefixMap<ipnet::Ipv4Net, usize> = PrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), 1),
    ///     (net!("192.168.0.0/22"), 2),
    ///     (net!("192.168.0.0/24"), 3),
    ///     (net!("192.168.2.0/23"), 4),
    /// ]);
    /// let mut map_b: PrefixMap<ipnet::Ipv4Net, &'static str> = PrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), "a"),
    ///     (net!("192.168.0.0/22"), "b"),
    ///     (net!("192.168.0.0/23"), "c"),
    ///     (net!("192.168.2.0/24"), "d"),
    /// ]);
    /// let sub_a = map_a.trie_view_at(&net!("192.168.0.0/22")).unwrap();
    /// let sub_b = map_b.trie_view_at(&net!("192.168.0.0/22")).unwrap();
    /// assert_eq!(
    ///     sub_a.difference(&sub_b).collect::<Vec<_>>(),
    ///     vec![
    ///         DifferenceItem { prefix: &net!("192.168.0.0/24"), value: &3, right: Some((&net!("192.168.0.0/23"), &"c"))},
    ///         DifferenceItem { prefix: &net!("192.168.2.0/23"), value: &4, right: Some((&net!("192.168.0.0/22"), &"b"))},
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn difference<R>(&self, other: &'a impl AsTrieView<P, R>) -> Difference<'a, P, L, R> {
        let other = other.trie_view();
        Difference {
            map_l: self.map,
            map_r: other.map,
            nodes: extend_lpm(
                other.map,
                other.map.table[other.idx].prefix_value(),
                next_indices(self.map, other.map, Some(self.idx), Some(other.idx)),
            )
            .collect(),
        }
    }

    /// Iterate over all elements in `self` that are not not covered in `other`. In other words,
    /// only items of `self` are yielded for which there does not exist a prefix in `other` that
    /// covers it.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::Ipv4Net>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map_a: PrefixMap<ipnet::Ipv4Net, usize> = PrefixMap::from_iter([
    ///     (net!("192.168.0.0/22"), 1),
    ///     (net!("192.168.0.0/24"), 2),
    ///     (net!("192.168.2.0/23"), 3),
    /// ]);
    /// let mut set_b: PrefixSet<ipnet::Ipv4Net> = PrefixSet::from_iter([
    ///     net!("192.168.0.0/23"),
    /// ]);
    /// assert_eq!(
    ///     map_a.trie_view().covering_difference(&set_b).collect::<Vec<_>>(),
    ///     vec![(&net!("192.168.0.0/22"), &1), (&net!("192.168.2.0/23"), &3)],
    /// );
    /// # }
    /// ```
    pub fn covering_difference<R>(
        &self,
        other: &'a impl AsTrieView<P, R>,
    ) -> CoveringDifference<'a, P, L, R> {
        let other = other.trie_view();
        CoveringDifference {
            map_l: self.map,
            map_r: other.map,
            nodes: next_indices(self.map, other.map, Some(self.idx), Some(other.idx)),
        }
    }
}

impl<'a, P: Prefix, L, R> Iterator for Difference<'a, P, L, R> {
    type Item = DifferenceItem<'a, P, L, R>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((cur, lpm_r)) = self.nodes.pop() {
            match cur {
                DifferenceIndex::Both(l, r) => {
                    let node_l = &self.map_l.table[l];
                    let node_r = &self.map_r.table[r];
                    self.extend(
                        next_indices(self.map_l, self.map_r, node_l.right, node_r.right),
                        lpm_r,
                    );
                    self.extend(
                        next_indices(self.map_l, self.map_r, node_l.left, node_r.left),
                        lpm_r,
                    );
                    if let Some(value) = node_l.value.as_ref() {
                        if node_r.value.is_none() {
                            return Some(DifferenceItem {
                                prefix: &node_l.prefix,
                                value,
                                right: lpm_r,
                            });
                        }
                    }
                }
                DifferenceIndex::FirstL(l, r) => {
                    let node_l = &self.map_l.table[l];
                    self.extend(
                        next_indices_first_a(
                            self.map_l,
                            self.map_r,
                            l,
                            node_l.left,
                            node_l.right,
                            r,
                        ),
                        lpm_r,
                    );
                    if let Some(value) = node_l.value.as_ref() {
                        return Some(DifferenceItem {
                            prefix: &node_l.prefix,
                            value,
                            right: lpm_r,
                        });
                    }
                }
                DifferenceIndex::FirstR(l, r) => {
                    let node_r = &self.map_r.table[r];
                    self.extend(
                        next_indices_first_b(
                            self.map_l,
                            self.map_r,
                            l,
                            r,
                            node_r.left,
                            node_r.right,
                        ),
                        lpm_r,
                    );
                }
                DifferenceIndex::OnlyL(l) => {
                    let node_l = &self.map_l.table[l];
                    if let Some(right) = node_l.right {
                        self.extend([DifferenceIndex::OnlyL(right)], lpm_r);
                    }
                    if let Some(left) = node_l.left {
                        self.extend([DifferenceIndex::OnlyL(left)], lpm_r);
                    }
                    if let Some(value) = node_l.value.as_ref() {
                        return Some(DifferenceItem {
                            prefix: &node_l.prefix,
                            value,
                            right: lpm_r,
                        });
                    }
                }
            }
        }
        None
    }
}

impl<'a, P: Prefix, L, R> Iterator for CoveringDifference<'a, P, L, R> {
    type Item = (&'a P, &'a L);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(cur) = self.nodes.pop() {
            match cur {
                DifferenceIndex::Both(l, r) => {
                    let node_l = &self.map_l.table[l];
                    let node_r = &self.map_r.table[r];
                    // skip if r has a value (this all children must be ignored)
                    if node_r.value.is_some() {
                        continue;
                    }
                    self.nodes.extend(next_indices(
                        self.map_l,
                        self.map_r,
                        node_l.right,
                        node_r.right,
                    ));
                    self.nodes.extend(next_indices(
                        self.map_l,
                        self.map_r,
                        node_l.left,
                        node_r.left,
                    ));
                    if let Some(value) = node_l.value.as_ref() {
                        return Some((&node_l.prefix, value));
                    }
                }
                DifferenceIndex::FirstL(l, r) => {
                    let node_l = &self.map_l.table[l];
                    self.nodes.extend(next_indices_first_a(
                        self.map_l,
                        self.map_r,
                        l,
                        node_l.left,
                        node_l.right,
                        r,
                    ));
                    if let Some(value) = node_l.value.as_ref() {
                        return Some((&node_l.prefix, value));
                    }
                }
                DifferenceIndex::FirstR(l, r) => {
                    let node_r = &self.map_r.table[r];
                    // skip if r has a value (this all children must be ignored)
                    if node_r.value.is_some() {
                        continue;
                    }
                    self.nodes.extend(next_indices_first_b(
                        self.map_l,
                        self.map_r,
                        l,
                        r,
                        node_r.left,
                        node_r.right,
                    ));
                }
                DifferenceIndex::OnlyL(l) => {
                    let node_l = &self.map_l.table[l];
                    if let Some(right) = node_l.right {
                        self.nodes.extend([DifferenceIndex::OnlyL(right)]);
                    }
                    if let Some(left) = node_l.left {
                        self.nodes.extend([DifferenceIndex::OnlyL(left)]);
                    }
                    if let Some(value) = node_l.value.as_ref() {
                        return Some((&node_l.prefix, value));
                    }
                }
            }
        }
        None
    }
}

impl<'a, P: Prefix, L, R> Difference<'a, P, L, R> {
    fn extend(
        &mut self,
        indices: impl IntoIterator<Item = DifferenceIndex> + 'static,
        lpm_r: Option<(&'a P, &'a R)>,
    ) {
        self.nodes.extend(extend_lpm(self.map_r, lpm_r, indices));
    }
}

fn next_indices<'a, P: Prefix, L, R>(
    map_l: &'a PrefixMap<P, L>,
    map_r: &'a PrefixMap<P, R>,
    l: Option<usize>,
    r: Option<usize>,
) -> Vec<DifferenceIndex> {
    match (l, r) {
        (None, Some(_)) => vec![],
        (Some(l), None) => vec![DifferenceIndex::OnlyL(l)],
        (Some(l), Some(r)) => {
            let p_l = &map_l.table[l].prefix;
            let p_r = &map_r.table[r].prefix;
            if p_l.prefix_len() == p_r.prefix_len() {
                match p_l.mask().cmp(&p_r.mask()) {
                    std::cmp::Ordering::Equal => {
                        vec![DifferenceIndex::Both(l, r)]
                    }
                    _ => {
                        vec![DifferenceIndex::OnlyL(l)]
                    }
                }
            } else if p_l.contains(p_r) {
                vec![DifferenceIndex::FirstL(l, r)]
            } else if p_r.contains(p_l) {
                vec![DifferenceIndex::FirstR(l, r)]
            } else {
                vec![DifferenceIndex::OnlyL(l)]
            }
        }
        _ => vec![],
    }
}

fn next_indices_first_a<'a, P: Prefix, L, R>(
    map_l: &'a PrefixMap<P, L>,
    map_r: &'a PrefixMap<P, R>,
    l: usize,
    ll: Option<usize>,
    lr: Option<usize>,
    r: usize,
) -> Vec<DifferenceIndex> {
    match (ll, lr) {
        (None, None) => vec![],
        (None, Some(lr)) => next_indices(map_l, map_r, Some(lr), Some(r)),
        (Some(ll), None) => next_indices(map_l, map_r, Some(ll), Some(r)),
        (Some(ll), Some(lr)) => {
            if to_right(&map_l.table[l].prefix, &map_r.table[r].prefix) {
                let mut idxes = next_indices(map_l, map_r, Some(lr), Some(r));
                idxes.push(DifferenceIndex::OnlyL(ll));
                idxes
            } else {
                let mut idxes = next_indices(map_l, map_r, Some(ll), Some(r));
                idxes.insert(0, DifferenceIndex::OnlyL(lr));
                idxes
            }
        }
    }
}

fn next_indices_first_b<'a, P: Prefix, L, R>(
    map_l: &'a PrefixMap<P, L>,
    map_r: &'a PrefixMap<P, R>,
    l: usize,
    r: usize,
    rl: Option<usize>,
    rr: Option<usize>,
) -> Vec<DifferenceIndex> {
    match (rl, rr) {
        (None, None) => vec![DifferenceIndex::OnlyL(l)],
        (None, Some(rr)) => next_indices(map_l, map_r, Some(l), Some(rr)),
        (Some(rl), None) => next_indices(map_l, map_r, Some(l), Some(rl)),
        (Some(rl), Some(rr)) => {
            if to_right(&map_r.table[r].prefix, &map_l.table[l].prefix) {
                next_indices(map_l, map_r, Some(l), Some(rr))
            } else {
                next_indices(map_l, map_r, Some(l), Some(rl))
            }
        }
    }
}

fn extend_lpm<'a, P: Prefix, R>(
    map_r: &'a PrefixMap<P, R>,
    lpm_r: Option<(&'a P, &'a R)>,
    indices: impl IntoIterator<Item = DifferenceIndex> + 'static,
) -> impl Iterator<Item = (DifferenceIndex, Option<(&'a P, &'a R)>)> + 'a {
    let get_lpm_r = move |r: usize| map_r.table[r].prefix_value().or(lpm_r);
    indices.into_iter().map(move |x| match x {
        DifferenceIndex::Both(_, r) | DifferenceIndex::FirstR(_, r) => (x, get_lpm_r(r)),
        DifferenceIndex::FirstL(_, _) | DifferenceIndex::OnlyL(_) => (x, lpm_r),
    })
}
