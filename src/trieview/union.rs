use crate::to_right;

use super::*;

/// An iterator over the union of two TrieViews.
pub struct Union<'a, P, L, R> {
    map_l: &'a PrefixMap<P, L>,
    map_r: &'a PrefixMap<P, R>,
    nodes: Vec<UnionIndex>,
}

/// An iterator over the union of two TrieViews that always yields the longest prefix match of both
/// of them.
pub struct UnionLpm<'a, P, L, R> {
    map_l: &'a PrefixMap<P, L>,
    map_r: &'a PrefixMap<P, R>,
    nodes: Vec<(UnionIndex, usize, usize)>,
}

/// An item of the [`UnionLpm`] iterator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnionLpmItem<'a, P, L, R> {
    /// The prefix is only present in the left TrieView (`self`).
    Left {
        /// The prefix of the element.
        prefix: &'a P,
        /// The value of the element in the left TrieView (`self`).
        left: &'a L,
        /// The longest prefix match in the right TrieView (`other`).
        right: Option<(&'a P, &'a R)>,
    },
    /// The prefix is only present in the right TrieView (`other`).
    Right {
        /// The prefix of the element.
        prefix: &'a P,
        /// The longest prefix match in the left TrieView (`self`).
        left: Option<(&'a P, &'a L)>,
        /// The value of the element in the right TrieView (`other`).
        right: &'a R,
    },
    /// The prefix is only present in the right TrieView (`other`).
    Both {
        /// The prefix of the element.
        prefix: &'a P,
        /// The value of the element in the left TrieView (`self`).
        left: &'a L,
        /// The value of the element in the right TrieView (`other`).
        right: &'a R,
    },
}

impl<'a, P, L, R> UnionLpmItem<'a, P, L, R> {
    /// Get the prefix of the current element (in the exact match).
    pub fn prefix(&self) -> &'a P {
        match self {
            UnionLpmItem::Left { prefix, .. }
            | UnionLpmItem::Right { prefix, .. }
            | UnionLpmItem::Both { prefix, .. } => prefix,
        }
    }

    /// Get the value of the left item (`self`). This either returns the exact match or the
    /// longest-prefix match.
    pub fn left(&self) -> Option<(&'a P, &'a L)> {
        match self {
            UnionLpmItem::Right { left, .. } => *left,
            UnionLpmItem::Left { prefix, left, .. } | UnionLpmItem::Both { prefix, left, .. } => {
                Some((prefix, left))
            }
        }
    }

    /// Get the value of the right item (`other`). This either returns the exact match or the
    /// longest-prefix match.
    pub fn right(&self) -> Option<(&'a P, &'a R)> {
        match self {
            UnionLpmItem::Left { right, .. } => *right,
            UnionLpmItem::Right { prefix, right, .. }
            | UnionLpmItem::Both { prefix, right, .. } => Some((prefix, right)),
        }
    }
}

/// A pointer to a value in either `Self` or in `Other`, or `Both`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Either<L, R> {
    /// The element is only present in the left map (`self`).
    Left(L),
    /// The element is only present in the right map (`other`).
    Right(R),
    /// The element is only present in both maps (`self` and `other`).
    Both(L, R),
}

impl<L, R> Either<L, R> {
    /// Get the left part of `self`
    pub fn left(self) -> Option<L> {
        match self {
            Either::Left(l) | Either::Both(l, _) => Some(l),
            _ => None,
        }
    }

    /// Get the right part of `self`
    pub fn right(self) -> Option<R> {
        match self {
            Either::Right(r) | Either::Both(_, r) => Some(r),
            _ => None,
        }
    }

    /// Get a reference to the inner data of `self`.
    pub fn as_ref(&self) -> Either<&L, &R> {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(r),
            Either::Both(l, r) => Either::Both(l, r),
        }
    }

    fn from_options(left: Option<L>, right: Option<R>) -> Option<Self> {
        match (left, right) {
            (None, None) => None,
            (None, Some(r)) => Some(Self::Right(r)),
            (Some(l), None) => Some(Self::Left(l)),
            (Some(l), Some(r)) => Some(Self::Both(l, r)),
        }
    }
}

enum UnionIndex {
    Both(usize, usize),
    FirstL(usize, usize),
    FirstR(usize, usize),
    OnlyL(usize),
    OnlyR(usize),
}

impl<'a, P, L> TrieView<'a, P, L>
where
    P: Prefix,
{
    /// Iterate over the union of two views. Each element contains the prefix and a reference to the
    /// value stored in either `self`, or `other` (see [`Either`]).
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # use prefix_trie::trieview::Either;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::Ipv4Net>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut set_a: PrefixMap<ipnet::Ipv4Net, usize> = PrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), 1),
    ///     (net!("192.168.0.0/22"), 2),
    ///     (net!("192.168.0.0/24"), 3),
    ///     (net!("192.168.2.0/23"), 4),
    /// ]);
    /// let mut set_b: PrefixMap<ipnet::Ipv4Net, &'static str> = PrefixMap::from_iter([
    ///     (net!("192.168.0.0/22"), "a"),
    ///     (net!("192.168.0.0/23"), "b"),
    ///     (net!("192.168.2.0/24"), "c"),
    /// ]);
    /// let sub_a = set_a.trie_view_at(&net!("192.168.0.0/22")).unwrap();
    /// let sub_b = set_b.trie_view_at(&net!("192.168.0.0/22")).unwrap();
    /// assert_eq!(
    ///     sub_a.union(&sub_b).collect::<Vec<_>>(),
    ///     vec![
    ///         (&net!("192.168.0.0/22"), Either::Both(&2, &"a")),
    ///         (&net!("192.168.0.0/23"), Either::Right(&"b")),
    ///         (&net!("192.168.0.0/24"), Either::Left(&3)),
    ///         (&net!("192.168.2.0/23"), Either::Left(&4)),
    ///         (&net!("192.168.2.0/24"), Either::Right(&"c")),
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn union<R>(&self, other: &TrieView<'a, P, R>) -> Union<'a, P, L, R> {
        Union {
            map_l: self.map,
            map_r: other.map,
            nodes: next_indices(self.map, other.map, Some(self.idx), Some(other.idx)),
        }
    }

    /// Iterate over the union of two views. If a prefix is present in both trees, the iterator
    /// will yield both elements. Otherwise, the iterator will yield the element of one TrieView
    /// together with the longest prefix match in the other TrieView. Elements are of type
    /// [`UnionLpmItem`].
    ///
    /// **Warning**: The iterator will only yield elements of the given TrieViews. If either of the
    /// two TrieViews is pointing to a branching node, then the longest prefix match returned may be
    /// `None`, even though it exists in the larger tree.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # use prefix_trie::trieview::UnionLpmItem;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::Ipv4Net>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut set_a: PrefixMap<ipnet::Ipv4Net, usize> = PrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), 1),
    ///     (net!("192.168.0.0/22"), 2),
    ///     (net!("192.168.0.0/24"), 3),
    ///     (net!("192.168.2.0/23"), 4),
    /// ]);
    /// let mut set_b: PrefixMap<ipnet::Ipv4Net, &'static str> = PrefixMap::from_iter([
    ///     (net!("192.168.0.0/22"), "a"),
    ///     (net!("192.168.0.0/23"), "b"),
    ///     (net!("192.168.2.0/24"), "c"),
    /// ]);
    /// let sub_a = set_a.trie_view();
    /// let sub_b = set_b.trie_view();
    /// assert_eq!(
    ///     sub_a.union_lpm(&sub_b).collect::<Vec<_>>(),
    ///     vec![
    ///         UnionLpmItem::Left{
    ///             prefix: &net!("192.168.0.0/20"),
    ///             left: &1,
    ///             right: None,
    ///         },
    ///         UnionLpmItem::Both{
    ///             prefix: &net!("192.168.0.0/22"),
    ///             left: &2,
    ///             right: &"a",
    ///         },
    ///         UnionLpmItem::Right{
    ///             prefix: &net!("192.168.0.0/23"),
    ///             left: Some((&net!("192.168.0.0/22"), &2)),
    ///             right: &"b",
    ///         },
    ///         UnionLpmItem::Left{
    ///             prefix: &net!("192.168.0.0/24"),
    ///             left: &3,
    ///             right: Some((&net!("192.168.0.0/23"), &"b")),
    ///         },
    ///         UnionLpmItem::Left{
    ///             prefix: &net!("192.168.2.0/23"),
    ///             left: &4,
    ///             right: Some((&net!("192.168.0.0/22"), &"a")),
    ///         },
    ///         UnionLpmItem::Right{
    ///             prefix: &net!("192.168.2.0/24"),
    ///             left: Some((&net!("192.168.2.0/23"), &4)),
    ///             right: &"c",
    ///         },
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn union_lpm<R>(&self, other: &TrieView<'a, P, R>) -> UnionLpm<'a, P, L, R> {
        UnionLpm {
            map_l: self.map,
            map_r: other.map,
            nodes: extend_lpm(
                self.map,
                other.map,
                self.idx,
                other.idx,
                next_indices(self.map, other.map, Some(self.idx), Some(other.idx)),
            )
            .collect(),
        }
    }
}

impl<'a, P: Prefix, L, R> Iterator for Union<'a, P, L, R> {
    type Item = (&'a P, Either<&'a L, &'a R>);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(cur) = self.nodes.pop() {
            match cur {
                UnionIndex::Both(a, b) => {
                    let node_l = &self.map_l.table[a];
                    let node_r = &self.map_r.table[b];
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
                    if let Some(x) =
                        Either::from_options(node_l.value.as_ref(), node_r.value.as_ref())
                    {
                        return Some((&node_l.prefix, x));
                    }
                }
                UnionIndex::FirstL(l, r) => {
                    let node_l = &self.map_l.table[l];
                    self.nodes.extend(next_indices_first_l(
                        self.map_l,
                        self.map_r,
                        l,
                        node_l.left,
                        node_l.right,
                        r,
                    ));
                    if let Some(x) = Either::from_options(node_l.value.as_ref(), None) {
                        return Some((&node_l.prefix, x));
                    }
                }
                UnionIndex::FirstR(l, r) => {
                    let node_r = &self.map_r.table[r];
                    self.nodes.extend(next_indices_first_r(
                        self.map_l,
                        self.map_r,
                        l,
                        r,
                        node_r.left,
                        node_r.right,
                    ));
                    if let Some(x) = Either::from_options(None, node_r.value.as_ref()) {
                        return Some((&node_r.prefix, x));
                    }
                }
                UnionIndex::OnlyL(l) => {
                    let node_l = &self.map_l.table[l];
                    if let Some(right) = node_l.right {
                        self.nodes.push(UnionIndex::OnlyL(right));
                    }
                    if let Some(left) = node_l.left {
                        self.nodes.push(UnionIndex::OnlyL(left));
                    }
                    if let Some(x) = Either::from_options(node_l.value.as_ref(), None) {
                        return Some((&node_l.prefix, x));
                    }
                }
                UnionIndex::OnlyR(r) => {
                    let node_r = &self.map_r.table[r];
                    if let Some(right) = node_r.right {
                        self.nodes.push(UnionIndex::OnlyR(right));
                    }
                    if let Some(left) = node_r.left {
                        self.nodes.push(UnionIndex::OnlyR(left));
                    }
                    if let Some(x) = Either::from_options(None, node_r.value.as_ref()) {
                        return Some((&node_r.prefix, x));
                    }
                }
            }
        }
        None
    }
}

impl<'a, P: Prefix, L, R> UnionLpm<'a, P, L, R> {
    fn extend(
        &mut self,
        indices: impl IntoIterator<Item = UnionIndex> + 'static,
        lpm_l: usize,
        lpm_r: usize,
    ) {
        self.nodes
            .extend(extend_lpm(self.map_l, self.map_r, lpm_l, lpm_r, indices));
    }

    fn get_next(
        &self,
        prefix: &'a P,
        l: Option<&'a L>,
        r: Option<&'a R>,
        lpm_l: usize,
        lpm_r: usize,
    ) -> Option<UnionLpmItem<'a, P, L, R>> {
        match (l, r) {
            (None, None) => None,
            (None, Some(right)) => Some(UnionLpmItem::Right {
                prefix,
                left: self.map_l.table[lpm_l].prefix_value(),
                right,
            }),
            (Some(left), None) => Some(UnionLpmItem::Left {
                prefix,
                left,
                right: self.map_r.table[lpm_r].prefix_value(),
            }),
            (Some(left), Some(right)) => Some(UnionLpmItem::Both {
                prefix,
                left,
                right,
            }),
        }
    }
}

impl<'a, P: Prefix, L, R> Iterator for UnionLpm<'a, P, L, R> {
    type Item = UnionLpmItem<'a, P, L, R>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((cur, lpm_l, lpm_r)) = self.nodes.pop() {
            match cur {
                UnionIndex::Both(l, r) => {
                    let node_l = &self.map_l.table[l];
                    let node_r = &self.map_r.table[r];
                    self.extend(
                        next_indices(self.map_l, self.map_r, node_l.right, node_r.right),
                        lpm_l,
                        lpm_r,
                    );
                    self.extend(
                        next_indices(self.map_l, self.map_r, node_l.left, node_r.left),
                        lpm_l,
                        lpm_r,
                    );
                    if let Some(x) = self.get_next(
                        &node_l.prefix,
                        node_l.value.as_ref(),
                        node_r.value.as_ref(),
                        lpm_l,
                        lpm_r,
                    ) {
                        return Some(x);
                    }
                }
                UnionIndex::FirstL(l, r) => {
                    let node_l = &self.map_l.table[l];
                    self.extend(
                        next_indices_first_l(
                            self.map_l,
                            self.map_r,
                            l,
                            node_l.left,
                            node_l.right,
                            r,
                        ),
                        lpm_l,
                        lpm_r,
                    );
                    if let Some(x) =
                        self.get_next(&node_l.prefix, node_l.value.as_ref(), None, lpm_l, lpm_r)
                    {
                        return Some(x);
                    }
                }
                UnionIndex::FirstR(l, r) => {
                    let node_r = &self.map_r.table[r];
                    self.extend(
                        next_indices_first_r(
                            self.map_l,
                            self.map_r,
                            l,
                            r,
                            node_r.left,
                            node_r.right,
                        ),
                        lpm_l,
                        lpm_r,
                    );
                    if let Some(x) =
                        self.get_next(&node_r.prefix, None, node_r.value.as_ref(), lpm_l, lpm_r)
                    {
                        return Some(x);
                    }
                }
                UnionIndex::OnlyL(l) => {
                    let node_l = &self.map_l.table[l];
                    if let Some(right) = node_l.right {
                        self.extend([UnionIndex::OnlyL(right)], lpm_l, lpm_r);
                    }
                    if let Some(left) = node_l.left {
                        self.extend([UnionIndex::OnlyL(left)], lpm_l, lpm_r);
                    }
                    if let Some(x) =
                        self.get_next(&node_l.prefix, node_l.value.as_ref(), None, lpm_l, lpm_r)
                    {
                        return Some(x);
                    }
                }
                UnionIndex::OnlyR(r) => {
                    let node_r = &self.map_r.table[r];
                    if let Some(right) = node_r.right {
                        self.extend([UnionIndex::OnlyR(right)], lpm_l, lpm_r);
                    }
                    if let Some(left) = node_r.left {
                        self.extend([UnionIndex::OnlyR(left)], lpm_l, lpm_r);
                    }
                    if let Some(x) =
                        self.get_next(&node_r.prefix, None, node_r.value.as_ref(), lpm_l, lpm_r)
                    {
                        return Some(x);
                    }
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
) -> Vec<UnionIndex> {
    match (node_l, node_r) {
        (None, Some(b)) => vec![UnionIndex::OnlyR(b)],
        (Some(a), None) => vec![UnionIndex::OnlyL(a)],
        (Some(a), Some(b)) => {
            let p_a = &map_l.table[a].prefix;
            let p_b = &map_r.table[b].prefix;
            if p_a.prefix_len() == p_b.prefix_len() {
                match p_a.mask().cmp(&p_b.mask()) {
                    std::cmp::Ordering::Less => {
                        vec![UnionIndex::OnlyR(b), UnionIndex::OnlyL(a)]
                    }
                    std::cmp::Ordering::Equal => {
                        vec![UnionIndex::Both(a, b)]
                    }
                    std::cmp::Ordering::Greater => {
                        vec![UnionIndex::OnlyL(a), UnionIndex::OnlyR(b)]
                    }
                }
            } else if p_a.contains(p_b) {
                vec![UnionIndex::FirstL(a, b)]
            } else if p_b.contains(p_a) {
                vec![UnionIndex::FirstR(a, b)]
            } else {
                if p_a.mask() < p_b.mask() {
                    vec![UnionIndex::OnlyR(b), UnionIndex::OnlyL(a)]
                } else {
                    vec![UnionIndex::OnlyL(a), UnionIndex::OnlyR(b)]
                }
            }
        }
        _ => vec![],
    }
}

fn next_indices_first_l<'a, P: Prefix, L, R>(
    map_l: &'a PrefixMap<P, L>,
    map_r: &'a PrefixMap<P, R>,
    l: usize,
    ll: Option<usize>,
    lr: Option<usize>,
    r: usize,
) -> Vec<UnionIndex> {
    match (ll, lr) {
        (None, None) => vec![UnionIndex::OnlyR(r)],
        (None, Some(lr)) => next_indices(map_l, map_r, Some(lr), Some(r)),
        (Some(ll), None) => next_indices(map_l, map_r, Some(ll), Some(r)),
        (Some(ll), Some(lr)) => {
            if to_right(&map_l.table[l].prefix, &map_r.table[r].prefix) {
                let mut idxes = next_indices(map_l, map_r, Some(lr), Some(r));
                idxes.push(UnionIndex::OnlyL(ll));
                idxes
            } else {
                let mut idxes = next_indices(map_l, map_r, Some(ll), Some(r));
                idxes.insert(0, UnionIndex::OnlyL(lr));
                idxes
            }
        }
    }
}

fn next_indices_first_r<'a, P: Prefix, L, R>(
    map_l: &'a PrefixMap<P, L>,
    map_r: &'a PrefixMap<P, R>,
    l: usize,
    r: usize,
    rl: Option<usize>,
    rr: Option<usize>,
) -> Vec<UnionIndex> {
    match (rl, rr) {
        (None, None) => vec![UnionIndex::OnlyL(l)],
        (None, Some(rr)) => next_indices(map_l, map_r, Some(l), Some(rr)),
        (Some(rl), None) => next_indices(map_l, map_r, Some(l), Some(rl)),
        (Some(rl), Some(rr)) => {
            if to_right(&map_r.table[r].prefix, &map_l.table[l].prefix) {
                let mut idxes = next_indices(map_l, map_r, Some(l), Some(rr));
                idxes.push(UnionIndex::OnlyR(rl));
                idxes
            } else {
                let mut idxes = next_indices(map_l, map_r, Some(l), Some(rl));
                idxes.insert(0, UnionIndex::OnlyR(rr));
                idxes
            }
        }
    }
}

fn extend_lpm<'a, P: Prefix, L, R>(
    map_l: &'a PrefixMap<P, L>,
    map_r: &'a PrefixMap<P, R>,
    lpm_l: usize,
    lpm_r: usize,
    indices: impl IntoIterator<Item = UnionIndex> + 'static,
) -> impl Iterator<Item = (UnionIndex, usize, usize)> + 'a {
    let get_lpm_l = move |l: usize| map_l.table[l].value.as_ref().map(|_| l).unwrap_or(lpm_l);
    let get_lpm_r = move |r: usize| map_r.table[r].value.as_ref().map(|_| r).unwrap_or(lpm_r);
    indices.into_iter().map(move |x| match x {
        UnionIndex::Both(l, r) => (x, get_lpm_l(l), get_lpm_r(r)),
        UnionIndex::FirstL(l, _) | UnionIndex::OnlyL(l) => (x, get_lpm_l(l), lpm_r),
        UnionIndex::FirstR(_, r) | UnionIndex::OnlyR(r) => (x, lpm_l, get_lpm_r(r)),
    })
}
