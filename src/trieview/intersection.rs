use crate::to_right;

use super::*;

/// an iterator over the intersection of two [`crate::PrefixSet`]s in lexicographic order.
pub struct Intersection<'a, P, L, R> {
    pub(super) map_l: &'a PrefixMap<P, L>,
    pub(super) map_r: &'a PrefixMap<P, R>,
    pub(super) nodes: Vec<IntersectionIndex>,
}

pub(super) enum IntersectionIndex {
    Both(usize, usize),
    FirstA(usize, usize),
    FirstB(usize, usize),
}

impl<'a, P, L> TrieView<'a, P, L>
where
    P: Prefix,
{
    /// Iterate over the union of both Views. Each element will yield a reference to the prefix and
    /// the value stored in `self` and `other` (if the prefix is in both views).
    ///
    /// If instead you are interested in the longest prefix match, look at [`TrieView::union_lpm`].
    ///
    /// ```
    /// # use prefix_trie::*;
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
    ///     (net!("192.168.0.0/24"), "d"),
    ///     (net!("192.168.2.0/24"), "e"),
    /// ]);
    /// let sub_a = map_a.trie_view_at(&net!("192.168.0.0/22")).unwrap();
    /// let sub_b = map_b.trie_view_at(&net!("192.168.0.0/22")).unwrap();
    /// assert_eq!(
    ///     sub_a.intersection(&sub_b).collect::<Vec<_>>(),
    ///     vec![
    ///         (&net!("192.168.0.0/22"), &2, &"b"),
    ///         (&net!("192.168.0.0/24"), &3, &"d"),
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn intersection<R>(&self, other: &TrieView<'a, P, R>) -> Intersection<'a, P, L, R> {
        Intersection {
            map_l: self.map,
            map_r: other.map,
            nodes: Vec::from_iter(next_indices(
                self.map,
                other.map,
                Some(self.idx),
                Some(other.idx),
            )),
        }
    }
}

impl<'a, P: Prefix, L, R> Iterator for Intersection<'a, P, L, R> {
    type Item = (&'a P, &'a L, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(cur) = self.nodes.pop() {
            match cur {
                IntersectionIndex::Both(l, r) => {
                    let node_l = &self.map_l.table[l];
                    let node_r = &self.map_r.table[r];
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
                    if let (Some(left), Some(right)) =
                        (node_l.value.as_ref(), node_r.value.as_ref())
                    {
                        return Some((&node_l.prefix, left, right));
                    }
                }
                IntersectionIndex::FirstA(l, r) => {
                    let node_l = &self.map_l.table[l];
                    self.nodes.extend(next_indices_first_a(
                        self.map_l,
                        self.map_r,
                        l,
                        node_l.left,
                        node_l.right,
                        r,
                    ));
                }
                IntersectionIndex::FirstB(l, r) => {
                    let node_r = &self.map_r.table[r];
                    self.nodes.extend(next_indices_first_b(
                        self.map_l,
                        self.map_r,
                        l,
                        r,
                        node_r.left,
                        node_r.right,
                    ));
                }
            }
        }
        None
    }
}

fn next_indices<'a, P: Prefix, L, R>(
    map_l: &'a PrefixMap<P, L>,
    map_r: &'a PrefixMap<P, R>,
    node_l: Option<usize>,
    node_r: Option<usize>,
) -> Option<IntersectionIndex> {
    match (node_l, node_r) {
        (None, Some(_)) => None,
        (Some(_), None) => None,
        (Some(a), Some(b)) => {
            let p_a = &map_l.table[a].prefix;
            let p_b = &map_r.table[b].prefix;
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

fn next_indices_first_a<'a, P: Prefix, L, R>(
    map_l: &'a PrefixMap<P, L>,
    map_r: &'a PrefixMap<P, R>,
    l: usize,
    ll: Option<usize>,
    lr: Option<usize>,
    r: usize,
) -> Option<IntersectionIndex> {
    match (ll, lr) {
        (None, None) => None,
        (None, Some(lr)) => next_indices(map_l, map_r, Some(lr), Some(r)),
        (Some(ll), None) => next_indices(map_l, map_r, Some(ll), Some(r)),
        (Some(ll), Some(lr)) => {
            if to_right(&map_l.table[l].prefix, &map_r.table[r].prefix) {
                next_indices(map_l, map_r, Some(lr), Some(r))
            } else {
                next_indices(map_l, map_r, Some(ll), Some(r))
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
) -> Option<IntersectionIndex> {
    match (rl, rr) {
        (None, None) => None,
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
