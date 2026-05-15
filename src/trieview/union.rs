//! Union set-operation view.
//!
//! [`UnionView`] yields every prefix present in **either** the left or right view.
//! The two views are **not** aligned at construction: if one is shallower (smaller `depth`),
//! it leads the traversal on its own, and the deeper side is incorporated only once the
//! traversal descends to its depth.
//!
//! - Same depth:   `data_bitmap = L | R`,  `child_bitmap = L | R`
//! - L shallower:  `data_bitmap = L only`, `child_bitmap = L | (1 << toward_R)`
//! - R shallower:  mirror of above

use std::marker::PhantomData;

use num_traits::PrimInt;

use crate::{
    prefix::mask_from_prefix_len,
    Prefix,
    {
        node::{child_bit as node_child_bit, extend_repr},
        table::K,
        AsView,
    },
};

use super::{TrieView, ViewIter};

/// The item type yielded by iterating a [`UnionView`].
///
/// Indicates whether a prefix is present in only the left view, only the right view,
/// or in both.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnionItem<L, R> {
    /// Present only in the left view.
    Left(L),
    /// Present only in the right view.
    Right(R),
    /// Present in both views.
    Both(L, R),
}

impl<L, R> UnionItem<L, R> {
    /// Get a reference to the left element (if present).
    pub fn left(&self) -> Option<&L> {
        match self {
            UnionItem::Left(l) | UnionItem::Both(l, _) => Some(l),
            UnionItem::Right(_) => None,
        }
    }

    /// Get a reference to the right element (if present).
    pub fn right(&self) -> Option<&R> {
        match self {
            UnionItem::Right(r) | UnionItem::Both(_, r) => Some(r),
            UnionItem::Left(_) => None,
        }
    }

    /// Get a reference to both elements if both are set.
    pub fn both(&self) -> Option<(&L, &R)> {
        match self {
            UnionItem::Both(l, r) => Some((l, r)),
            _ => None,
        }
    }

    /// Extract the left element (and dropping the right if present.)
    pub fn into_left(self) -> Option<L> {
        match self {
            UnionItem::Left(l) | UnionItem::Both(l, _) => Some(l),
            UnionItem::Right(_) => None,
        }
    }

    /// Extract the right element (and dropping the left if present.)
    pub fn into_right(self) -> Option<R> {
        match self {
            UnionItem::Right(r) | UnionItem::Both(_, r) => Some(r),
            UnionItem::Left(_) => None,
        }
    }

    /// Extract both elements, each if they are present.
    pub fn into_both(self) -> (Option<L>, Option<R>) {
        match self {
            UnionItem::Left(l) => (Some(l), None),
            UnionItem::Right(r) => (None, Some(r)),
            UnionItem::Both(l, r) => (Some(l), Some(r)),
        }
    }
}

/// An immutable view over the union of two [`TrieView`]s.
///
/// Returned by [`TrieView::union`]. The two views are **not** aligned at
/// construction: if one is shallower (smaller `depth`) than the other, it
/// continues iterating on its own, incorporating the deeper view only once the
/// traversal reaches the deeper view's multi-bit node depth.
///
/// Yields every prefix present in **either** sub-trie in lexicographic order,
/// with [`UnionItem::Left`], [`UnionItem::Right`], or [`UnionItem::Both`] indicating
/// membership.
#[derive(Clone)]
pub struct UnionView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    left: Option<L>,
    right: Option<R>,
    depth: u32,
    key: <<L as TrieView<'a>>::P as Prefix>::R,
    prefix_len: u32,
    _phantom: PhantomData<&'a ()>,
}

impl<'a, L, R> UnionView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    /// Construct a `UnionView` from two views without aligning their depths.
    pub(crate) fn new(left: L, right: R) -> Self {
        let (key, prefix_len) = common_prefix::<L::P>(
            left.key(),
            left.prefix_len(),
            right.key(),
            right.prefix_len(),
        );
        let depth = (prefix_len / K) * K;
        Self {
            left: Some(left),
            right: Some(right),
            depth,
            key,
            prefix_len,
            _phantom: PhantomData,
        }
    }
}

impl<'a, L, R> TrieView<'a> for UnionView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    type P = L::P;
    type T = UnionItem<L::T, R::T>;

    #[inline]
    fn depth(&self) -> u32 {
        self.depth
    }

    #[inline]
    fn key(&self) -> <L::P as Prefix>::R {
        self.key
    }

    #[inline]
    fn prefix_len(&self) -> u32 {
        self.prefix_len
    }

    #[inline]
    fn data_bitmap(&self) -> u32 {
        side_data_bitmap(&self.left, self.depth) | side_data_bitmap(&self.right, self.depth)
    }

    #[inline]
    fn child_bitmap(&self) -> u32 {
        side_child_bitmap(&self.left, self.depth) | side_child_bitmap(&self.right, self.depth)
    }

    #[inline]
    unsafe fn get_data(&mut self, data_bit: u32) -> UnionItem<L::T, R::T> {
        match (self.left.as_mut(), self.right.as_mut()) {
            (Some(l), Some(r)) => {
                if l.depth() == self.depth && r.depth() == self.depth {
                    let in_l = (l.data_bitmap() >> data_bit) & 1 == 1;
                    let in_r = (r.data_bitmap() >> data_bit) & 1 == 1;
                    match (in_l, in_r) {
                        (true, true) => UnionItem::Both(l.get_data(data_bit), r.get_data(data_bit)),
                        (true, false) => UnionItem::Left(l.get_data(data_bit)),
                        (false, true) => UnionItem::Right(r.get_data(data_bit)),
                        (false, false) => unreachable!("get_data on bit absent from data_bitmap"),
                    }
                } else if l.depth() == self.depth {
                    UnionItem::Left(l.get_data(data_bit))
                } else if r.depth() == self.depth {
                    UnionItem::Right(r.get_data(data_bit))
                } else {
                    unreachable!("get_data on virtual UnionView root")
                }
            }
            (Some(l), None) => UnionItem::Left(l.get_data(data_bit)),
            (None, Some(r)) => UnionItem::Right(r.get_data(data_bit)),
            (None, None) => unreachable!("get_data on empty UnionView"),
        }
    }

    unsafe fn get_child(&mut self, child_bit: u32) -> Self {
        let new_depth = self.depth + K;
        let new_key = extend_repr(self.key, self.depth, child_bit);
        UnionView {
            left: take_child(&mut self.left, self.depth, child_bit),
            right: take_child(&mut self.right, self.depth, child_bit),
            depth: new_depth,
            key: new_key,
            prefix_len: new_depth,
            _phantom: PhantomData,
        }
    }

    unsafe fn reposition(&mut self, key: <L::P as Prefix>::R, prefix_len: u32) {
        reposition_side(&mut self.left, self.depth, key, prefix_len);
        reposition_side(&mut self.right, self.depth, key, prefix_len);
        self.key = key;
        self.prefix_len = prefix_len;
    }
}

fn common_prefix<P: Prefix>(
    left_key: P::R,
    left_len: u32,
    right_key: P::R,
    right_len: u32,
) -> (P::R, u32) {
    let max_len = left_len.min(right_len);
    let diff = (left_key & mask_from_prefix_len(max_len as u8))
        ^ (right_key & mask_from_prefix_len(max_len as u8));
    let len = diff.leading_zeros().min(max_len);
    (left_key & mask_from_prefix_len(len as u8), len)
}

fn paths_overlap<P: Prefix>(
    left_key: P::R,
    left_len: u32,
    right_key: P::R,
    right_len: u32,
) -> bool {
    let min_len = left_len.min(right_len);
    let mask = mask_from_prefix_len(min_len as u8);
    left_key & mask == right_key & mask
}

fn side_data_bitmap<'a, V: TrieView<'a>>(side: &Option<V>, depth: u32) -> u32 {
    match side {
        Some(view) if view.depth() == depth => view.data_bitmap(),
        _ => 0,
    }
}

fn side_child_bitmap<'a, V: TrieView<'a>>(side: &Option<V>, depth: u32) -> u32 {
    match side {
        Some(view) if view.depth() == depth => view.child_bitmap(),
        Some(view) if view.depth() > depth => 1 << node_child_bit(depth, view.key()),
        _ => 0,
    }
}

unsafe fn take_child<'a, V: TrieView<'a>>(
    side: &mut Option<V>,
    depth: u32,
    child_bit: u32,
) -> Option<V> {
    let view = side.as_mut()?;
    if view.depth() == depth {
        if (view.child_bitmap() >> child_bit) & 1 == 1 {
            Some(view.get_child(child_bit))
        } else {
            None
        }
    } else if view.depth() > depth {
        if child_bit == node_child_bit(depth, view.key()) {
            side.take()
        } else {
            None
        }
    } else {
        None
    }
}

unsafe fn reposition_side<'a, V: TrieView<'a>>(
    side: &mut Option<V>,
    union_depth: u32,
    key: <<V as TrieView<'a>>::P as Prefix>::R,
    prefix_len: u32,
) {
    let Some(view) = side.as_mut() else {
        return;
    };
    if !paths_overlap::<V::P>(view.key(), view.prefix_len(), key, prefix_len) {
        *side = None;
    } else if view.depth() == union_depth && prefix_len >= view.prefix_len() {
        view.reposition(key, prefix_len);
    }
}

impl<'a, L, R> IntoIterator for UnionView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    type Item = (L::P, UnionItem<L::T, R::T>);
    type IntoIter = ViewIter<'a, UnionView<'a, L, R>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, L, R> AsView<'a> for UnionView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    type P = L::P;
    type View = Self;

    fn view(self) -> Self {
        self
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        Prefix,
        {
            trieview::{AsView, TrieView},
            PrefixMap,
        },
    };

    use super::UnionItem;

    type P = (u32, u8);

    fn p(repr: u32, len: u8) -> P {
        P::from_repr_len(repr, len)
    }

    fn map_from(entries: &[(u32, u8, i32)]) -> PrefixMap<P, i32> {
        let mut m = PrefixMap::new();
        for &(repr, len, val) in entries {
            m.insert(p(repr, len), val);
        }
        m
    }

    fn collect_union<'a>(
        iter: impl Iterator<Item = (P, UnionItem<&'a i32, &'a i32>)>,
    ) -> Vec<(P, Option<i32>, Option<i32>)> {
        iter.map(|(p, item)| match item {
            UnionItem::Left(l) => (p, Some(*l), None),
            UnionItem::Right(r) => (p, None, Some(*r)),
            UnionItem::Both(l, r) => (p, Some(*l), Some(*r)),
        })
        .collect()
    }

    // -- Same-depth cases ------------------------------------------------------

    #[test]
    fn union_disjoint() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0b000000, 8, 10), (0x0b010000, 16, 20)]);
        let got = collect_union(a.view().union(b.view()).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x0a000000, 8), Some(1), None),
                (p(0x0a010000, 16), Some(2), None),
                (p(0x0b000000, 8), None, Some(10)),
                (p(0x0b010000, 16), None, Some(20)),
            ]
        );
    }

    #[test]
    fn union_overlapping() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a000000, 8, 10), (0x0b000000, 8, 20)]);
        let got = collect_union(a.view().union(b.view()).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x0a000000, 8), Some(1), Some(10)),
                (p(0x0a010000, 16), Some(2), None),
                (p(0x0b000000, 8), None, Some(20)),
            ]
        );
    }

    #[test]
    fn union_identical() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a000000, 8, 10), (0x0a010000, 16, 20)]);
        let got = collect_union(a.view().union(b.view()).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x0a000000, 8), Some(1), Some(10)),
                (p(0x0a010000, 16), Some(2), Some(20)),
            ]
        );
    }

    #[test]
    fn union_one_empty() {
        let a = map_from(&[(0x0a000000, 8, 1)]);
        let b: PrefixMap<P, i32> = PrefixMap::new();
        let got = collect_union(a.view().union(b.view()).into_iter());
        assert_eq!(got, vec![(p(0x0a000000, 8), Some(1), None)]);
    }

    #[test]
    fn union_both_empty() {
        let a: PrefixMap<P, i32> = PrefixMap::new();
        let b: PrefixMap<P, i32> = PrefixMap::new();
        assert!(a.view().union(b.view()).into_iter().next().is_none());
    }

    #[test]
    fn union_into_iter_for_loop() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a000000, 8, 10), (0x0b000000, 8, 20)]);
        let mut count = 0;
        for (_p, _item) in a.view().union(b.view()) {
            count += 1;
        }
        assert_eq!(count, 3);
    }

    /// Larger same-depth test: many entries spread across the address space,
    /// covering Left-only, Right-only, and Both across multiple subtries and levels.
    #[test]
    fn union_large_same_depth() {
        let a = map_from(&[
            (0x01000000, 8, 1),
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 11),
            (0x0a020000, 16, 12),
            (0x0a010100, 24, 13),
            (0x64000000, 8, 100),
            (0x64010000, 16, 101),
            (0xc0a80000, 16, 200), // 192.168.0.0/16
        ]);
        let b = map_from(&[
            (0x0a000000, 8, 20),  // overlaps a
            (0x0a010000, 16, 21), // overlaps a
            (0x0a030000, 16, 22), // new in b
            (0x0b000000, 8, 30),
            (0x0b010000, 16, 31),
            (0x64000000, 8, 110),  // overlaps a
            (0xc0a80100, 24, 210), // 192.168.1.0/24 -> new in b
        ]);
        let got = collect_union(a.view().union(b.view()).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x01000000, 8), Some(1), None),        // Left
                (p(0x0a000000, 8), Some(10), Some(20)),   // Both
                (p(0x0a010000, 16), Some(11), Some(21)),  // Both
                (p(0x0a010100, 24), Some(13), None),      // Left
                (p(0x0a020000, 16), Some(12), None),      // Left
                (p(0x0a030000, 16), None, Some(22)),      // Right
                (p(0x0b000000, 8), None, Some(30)),       // Right
                (p(0x0b010000, 16), None, Some(31)),      // Right
                (p(0x64000000, 8), Some(100), Some(110)), // Both
                (p(0x64010000, 16), Some(101), None),     // Left
                (p(0xc0a80000, 16), Some(200), None),     // Left
                (p(0xc0a80100, 24), None, Some(210)),     // Right
            ]
        );
    }

    #[test]
    fn union_large_same_depth_view_at() {
        let a = map_from(&[
            (0x01000000, 8, 1),
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 11),
            (0x0a020000, 16, 12),
            (0x0a010100, 24, 13),
            (0x64000000, 8, 100),
            (0x64010000, 16, 101),
            (0xc0a80000, 16, 200), // 192.168.0.0/16
        ]);
        let b = map_from(&[
            (0x0a000000, 8, 20),  // overlaps a
            (0x0a010000, 16, 21), // overlaps a
            (0x0a030000, 16, 22), // new in b
            (0x0b000000, 8, 30),
            (0x0b010000, 16, 31),
            (0x64000000, 8, 110),  // overlaps a
            (0xc0a80100, 24, 210), // 192.168.1.0/24 -> new in b
        ]);
        let got = collect_union(
            a.view_at(&p(0x00000000, 1))
                .unwrap()
                .union(b.view_at(&p(0x00000000, 1)).unwrap())
                .into_iter(),
        );
        let want = vec![
            (p(0x01000000, 8), Some(1), None),        // Left
            (p(0x0a000000, 8), Some(10), Some(20)),   // Both
            (p(0x0a010000, 16), Some(11), Some(21)),  // Both
            (p(0x0a010100, 24), Some(13), None),      // Left
            (p(0x0a020000, 16), Some(12), None),      // Left
            (p(0x0a030000, 16), None, Some(22)),      // Right
            (p(0x0b000000, 8), None, Some(30)),       // Right
            (p(0x0b010000, 16), None, Some(31)),      // Right
            (p(0x64000000, 8), Some(100), Some(110)), // Both
            (p(0x64010000, 16), Some(101), None),     // Left
        ];
        assert_eq!(got, want);
    }

    #[test]
    fn union_large_different_depth() {
        let a = map_from(&[
            (0x01000000, 8, 1),
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 11),
            (0x0a020000, 16, 12),
            (0x0a010100, 24, 13),
            (0x64000000, 8, 100),
            (0x64010000, 16, 101),
            (0xc0a80000, 16, 200), // 192.168.0.0/16
        ]);
        let b = map_from(&[
            (0x0a000000, 8, 20),  // overlaps a
            (0x0a010000, 16, 21), // overlaps a
            (0x0a030000, 16, 22), // new in b
            (0x0b000000, 8, 30),
            (0x0b010000, 16, 31),
            (0x64000000, 8, 110),  // overlaps a
            (0xc0a80100, 24, 210), // 192.168.1.0/24 -> new in b
        ]);
        let got = collect_union(
            a.view_at(&p(0x00000000, 1))
                .unwrap()
                .union(b.view_at(&p(0x0a000000, 8)).unwrap())
                .into_iter(),
        );
        let want = vec![
            (p(0x01000000, 8), Some(1), None),       // Left
            (p(0x0a000000, 8), Some(10), Some(20)),  // Both
            (p(0x0a010000, 16), Some(11), Some(21)), // Both
            (p(0x0a010100, 24), Some(13), None),     // Left
            (p(0x0a020000, 16), Some(12), None),     // Left
            (p(0x0a030000, 16), None, Some(22)),     // Right
            (p(0x64000000, 8), Some(100), None),     // Both
            (p(0x64010000, 16), Some(101), None),    // Left
        ];
        assert_eq!(got, want);
    }

    // -- find / find_lpm on a union --------------------------------------------

    #[test]
    fn union_find_then_iter() {
        let a = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a010100, 24, 3),
            (0x0b000000, 8, 4),
        ]);
        let b = map_from(&[
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 20),
            (0x0a020000, 16, 30),
            (0x0c000000, 8, 40),
        ]);
        // find 10.1.0.0/16 on the union -> a has {10.1/16, 10.1.1/24}, b has {10.1/16}
        let got = collect_union(
            a.view()
                .union(b.view())
                .find(&p(0x0a010000, 16))
                .unwrap()
                .into_iter(),
        );
        assert_eq!(
            got,
            vec![
                (p(0x0a010000, 16), Some(2), Some(20)),
                (p(0x0a010100, 24), Some(3), None),
            ]
        );
    }

    #[test]
    fn union_find_exact_and_value() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a000000, 8, 10), (0x0b000000, 8, 20)]);
        let u = a.view().union(b.view());

        // find_exact on a prefix present in both
        let v = u.clone().find_exact(&p(0x0a000000, 8)).unwrap();
        assert!(matches!(v.value().unwrap(), UnionItem::Both(l, r) if *l == 1 && *r == 10));

        // find_exact on a prefix present only in a
        let v2 = u.clone().find_exact(&p(0x0a010000, 16)).unwrap();
        assert!(matches!(v2.value().unwrap(), UnionItem::Left(l) if *l == 2));

        // find_exact on a prefix present only in b
        let v3 = u.clone().find_exact(&p(0x0b000000, 8)).unwrap();
        assert!(matches!(v3.value().unwrap(), UnionItem::Right(r) if *r == 20));

        // find_exact on a prefix in neither
        assert!(u.find_exact(&p(0x0c000000, 8)).is_none());
    }

    #[test]
    fn union_find_lpm_value_keys_values() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a010100, 24, 30), (0x0b000000, 8, 40)]);
        let u = a.view().union(b.view());

        let lpm = u.clone().find_lpm(&p(0x0a010180, 25)).unwrap();
        assert_eq!(lpm.prefix(), p(0x0a010100, 24));
        assert!(matches!(lpm.value().unwrap(), UnionItem::Right(r) if *r == 30));

        let got = u
            .clone()
            .find_lpm_value(&p(0x0a010180, 25))
            .map(|(prefix, value)| (prefix, value.into_both()));
        assert!(matches!(
            got,
            Some((prefix, (None, Some(r)))) if prefix == p(0x0a010100, 24) && *r == 30
        ));

        assert_eq!(
            u.clone().keys().collect::<Vec<_>>(),
            vec![
                p(0x0a000000, 8),
                p(0x0a010000, 16),
                p(0x0a010100, 24),
                p(0x0b000000, 8),
            ]
        );
        assert_eq!(u.values().count(), 4);
    }

    #[test]
    fn union_mut_find_lpm_value_does_not_require_clone() {
        let mut a = map_from(&[(0x0a000000, 8, 1), (0x0a010100, 24, 3)]);
        let b = map_from(&[(0x0a000000, 8, 10), (0x0a010000, 16, 20)]);

        let got = (&mut a)
            .view()
            .union(b.view())
            .find_lpm_value(&p(0x0a010180, 25))
            .map(|(prefix, item)| match item {
                UnionItem::Left(l) => {
                    *l += 10;
                    (prefix, *l)
                }
                other => panic!("expected left-only LPM, got {other:?}"),
            });

        assert_eq!(got, Some((p(0x0a010100, 24), 13)));
        assert_eq!(a.get(&p(0x0a010100, 24)), Some(&13));
    }

    // -- Depth-difference cases ------------------------------------------------
    //
    // With K=5, nodes live at depths 0, 5, 10, 15, 20, 25, 30.
    // `view_at(&p(addr, len))` lands in the node at depth = floor(len / K) * K.
    //   e.g. len=8  -> depth 5    (5 ≤ 8 < 10)
    //        len=16 -> depth 15   (15 ≤ 16 < 20)
    //
    // Tests cover:
    //   (a) "going toward"    : child_bit == toward_deeper: deeper view is carried along
    //   (b) "not going toward": child_bit != toward_deeper: deeper view is dropped
    //   (c) shallower has NO child in the direction of the deeper view

    /// L deeper (depth 5), R shallower (depth 0).
    /// R leads at depth 0; the child toward 10.x carries L along and merges at depth 5.
    /// Children of R toward 9.x and 11.x are NOT toward L -> only R data there.
    #[test]
    fn union_l_deeper_r_shallower_going_toward_and_not() {
        let a = map_from(&[
            (0x0a000000, 8, 1),  // 10.0.0.0/8
            (0x0a010000, 16, 2), // 10.1.0.0/16
            (0x0a020000, 16, 3), // 10.2.0.0/16
        ]);
        let b = map_from(&[
            (0x09000000, 8, 90),  // 9.0.0.0/8  -> NOT toward a_sub
            (0x0a000000, 8, 10),  // 10.0.0.0/8 -> toward a_sub; merged
            (0x0a010000, 16, 20), // 10.1.0.0/16
            (0x0b000000, 8, 30),  // 11.0.0.0/8 -> NOT toward a_sub
        ]);
        let a_sub = a.view_at(&p(0x0a000000, 8)).unwrap(); // depth 5
        let b_root = b.view(); // depth 0

        let got = collect_union(a_sub.union(b_root).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x09000000, 8), None, Some(90)), // not toward a_sub -> b only
                (p(0x0a000000, 8), Some(1), Some(10)), // toward a_sub, merged -> Both
                (p(0x0a010000, 16), Some(2), Some(20)), // merged
                (p(0x0a020000, 16), Some(3), None), // a only
                (p(0x0b000000, 8), None, Some(30)), // not toward a_sub -> b only
            ]
        );
    }

    /// Mirror: L shallower (depth 0), R deeper (depth 5).
    /// L leads; child toward 10.x carries R; children toward 9.x and 11.x drop R.
    #[test]
    fn union_r_deeper_l_shallower_going_toward_and_not() {
        let a = map_from(&[
            (0x09000000, 8, 90),
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 20),
            (0x0b000000, 8, 30),
        ]);
        let b = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a020000, 16, 3)]);
        let a_root = a.view();
        let b_sub = b.view_at(&p(0x0a000000, 8)).unwrap(); // depth 5

        let got = collect_union(a_root.union(b_sub).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x09000000, 8), Some(90), None), // not toward b_sub -> a only
                (p(0x0a000000, 8), Some(10), Some(1)), // toward b_sub -> Both
                (p(0x0a010000, 16), Some(20), Some(2)),
                (p(0x0a020000, 16), None, Some(3)), // b only
                (p(0x0b000000, 8), Some(30), None), // not toward b_sub -> a only
            ]
        );
    }

    /// The shallower side has **no** child in the direction of the deeper side.
    /// child_bitmap() forcibly adds the bit toward the deeper view (via `| (1 << toward)`),
    /// so the deeper view's entries still appear even though the shallower has no child there.
    #[test]
    fn union_shallower_has_no_child_toward_deeper() {
        // a_root has entries only in 9.x and 11.x -> no 10.x child at all.
        // b_sub is positioned at the 10.x subtrie (depth 5).
        let a = map_from(&[
            (0x09000000, 8, 1), // 9.0.0.0/8
            (0x0b000000, 8, 2), // 11.0.0.0/8
        ]);
        let b = map_from(&[
            (0x0a000000, 8, 10),  // 10.0.0.0/8
            (0x0a010000, 16, 20), // 10.1.0.0/16
            (0x0a010100, 24, 30), // 10.1.1.0/24
        ]);
        let a_root = a.view();
        let b_sub = b.view_at(&p(0x0a000000, 8)).unwrap(); // depth 5

        let got = collect_union(a_root.union(b_sub).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x09000000, 8), Some(1), None),   // a only
                (p(0x0a000000, 8), None, Some(10)),  // b only -> a had no child here
                (p(0x0a010000, 16), None, Some(20)), // b only
                (p(0x0a010100, 24), None, Some(30)), // b only
                (p(0x0b000000, 8), Some(2), None),   // a only
            ]
        );
    }

    /// L has entries in multiple children; only one child is "toward" R.
    /// Tests that going-toward carries R, not-going-toward drops R.
    #[test]
    fn union_shallower_multiple_children_only_one_toward_deeper() {
        // a_root: entries in 10.x, 11.x, 12.x.
        // b_sub: in 10.x subtrie (depth 5).
        //   child toward 10.x -> merge; children toward 11.x and 12.x -> a only.
        let a = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0b000000, 8, 3),
            (0x0c000000, 8, 4),
        ]);
        let b = map_from(&[
            (0x0a000000, 8, 10),
            (0x0a020000, 16, 20), // 10.2/16 -> only in b
        ]);
        let a_root = a.view();
        let b_sub = b.view_at(&p(0x0a000000, 8)).unwrap(); // depth 5

        let got = collect_union(a_root.union(b_sub).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x0a000000, 8), Some(1), Some(10)), // toward b_sub -> merged
                (p(0x0a010000, 16), Some(2), None),    // a only (b has nothing here)
                (p(0x0a020000, 16), None, Some(20)),   // b only
                (p(0x0b000000, 8), Some(3), None),     // NOT toward b_sub -> a only
                (p(0x0c000000, 8), Some(4), None),     // NOT toward b_sub -> a only
            ]
        );
    }

    /// Three levels of depth difference (depth 15 vs depth 0 with K=5).
    /// Requires three successive get_child calls to align the two sides.
    /// Entries in b's intermediate nodes (depth 5) appear as Right before alignment.
    #[test]
    fn union_multi_level_depth_difference() {
        // a_sub at depth 15 (since K=5 and 15 ≤ 16 < 20).
        // b_root at depth 0.
        // Hops needed: depth 0 -> 5 -> 10 -> 15 (three hops).
        let a = map_from(&[
            (0x0a010000, 16, 1), // 10.1.0.0/16
            (0x0a010100, 24, 2), // 10.1.1.0/24
            (0x0a010200, 24, 3), // 10.1.2.0/24
        ]);
        let b = map_from(&[
            (0x0a000000, 8, 10),  // 10.0.0.0/8  -> in depth-5 node, appears before alignment
            (0x0a010000, 16, 20), // 10.1.0.0/16 -> aligned at depth 15
            (0x0b000000, 8, 30),  // 11.0.0.0/8
        ]);
        let a_sub = a.view_at(&p(0x0a010000, 16)).unwrap(); // depth 15
        let b_root = b.view(); // depth 0

        let got = collect_union(a_sub.union(b_root).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x0a000000, 8), None, Some(10)),     // b only (in depth-5 node)
                (p(0x0a010000, 16), Some(1), Some(20)), // both  (aligned at depth 15)
                (p(0x0a010100, 24), Some(2), None),     // a only
                (p(0x0a010200, 24), Some(3), None),     // a only
                (p(0x0b000000, 8), None, Some(30)),     // b only
            ]
        );
    }

    // -- Composition -----------------------------------------------------------

    #[test]
    fn union_composed_with_intersection() {
        // (a ∪ b) ∩ c -> UnionView implements TrieView so it composes.
        let a = map_from(&[(0x0a000000, 8, 1), (0x0b000000, 8, 2)]);
        let b = map_from(&[(0x0a000000, 8, 10), (0x0c000000, 8, 20)]);
        let c = map_from(&[(0x0a000000, 8, 100)]);

        let got: Vec<_> = a
            .view()
            .union(&b)
            .intersection(&c)
            .unwrap()
            .into_iter()
            .map(|(p, (u, r))| (p, u, *r))
            .collect();
        assert_eq!(got.len(), 1);
        assert_eq!(got[0].0, p(0x0a000000, 8));
        assert_eq!(got[0].2, 100);
        assert!(matches!(got[0].1, UnionItem::Both(l, r) if *l == 1 && *r == 10));
    }

    #[test]
    fn union_composed_union_of_unions() {
        // (a ∪ b) ∪ c -> UnionView<UnionView<..>, ..> works end-to-end.
        let a = map_from(&[(0x0a000000, 8, 1)]);
        let b = map_from(&[(0x0b000000, 8, 2)]);
        let c = map_from(&[(0x0c000000, 8, 3), (0x0a000000, 8, 10)]);

        let count = a.view().union(b.view()).union(c.view()).into_iter().count();
        // 10/8 (in a and c -> Both in ab∪c), 11/8 (b only), 12/8 (c only)
        assert_eq!(count, 3);
    }

    // -- iter_from on union views -----------------------------------------------

    #[test]
    fn union_iter_from_inclusive() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a020000, 16, 3)]);
        let b = map_from(&[(0x0a010000, 16, 20), (0x0a030000, 16, 40)]);

        // Full union: 10/8(L), 10.1/16(B), 10.2/16(L), 10.3/16(R)
        let u = a.view().union(b.view());
        let from: Vec<_> = u
            .iter_from(&p(0x0a010000, 16), true)
            .map(|(p, _)| p)
            .collect();
        assert_eq!(
            from,
            vec![p(0x0a010000, 16), p(0x0a020000, 16), p(0x0a030000, 16)]
        );
    }

    #[test]
    fn union_iter_from_exclusive() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a020000, 16, 3)]);
        let b = map_from(&[(0x0a010000, 16, 20), (0x0a030000, 16, 40)]);

        let u = a.view().union(b.view());
        let from: Vec<_> = u
            .iter_from(&p(0x0a010000, 16), false)
            .map(|(p, _)| p)
            .collect();
        assert_eq!(from, vec![p(0x0a020000, 16), p(0x0a030000, 16)]);
    }

    #[test]
    fn union_iter_from_subview() {
        let a = map_from(&[
            (0x0a000000, 8, 1), // excluded by sub-view
            (0x0a020000, 16, 2),
            (0x0a030000, 16, 3),
            (0x0b000000, 8, 4), // excluded by sub-view
        ]);
        let b = map_from(&[
            (0x0a020000, 16, 20),
            (0x0a030000, 16, 40),
            (0x0b000000, 8, 50), // excluded by sub-view
        ]);

        // Sub-view at 10.2.0.0/15 covers 10.2.x.x–10.3.x.x, excludes 10/8, 11/8
        let u = a
            .view_at(&p(0x0a020000, 15))
            .unwrap()
            .union(b.view_at(&p(0x0a020000, 15)).unwrap());

        // Full union of the sub-views: 10.2/16(B), 10.3/16(B)
        let all: Vec<_> = u.clone().iter().map(|(p, _)| p).collect();
        assert_eq!(all, vec![p(0x0a020000, 16), p(0x0a030000, 16)]);

        // iter_from exclusive from 10.2/16 → only 10.3/16
        let from: Vec<_> = u
            .iter_from(&p(0x0a020000, 16), false)
            .map(|(p, _)| p)
            .collect();
        assert_eq!(from, vec![p(0x0a030000, 16)]);
    }
}
