//! Implementing the TrieView trait for archived variants

use num_traits::Zero;
use rkyv::Archive;

use crate::{
    allocator::compute_slot,
    node::{child_cover_mask, data_cover_mask, extend_repr},
    rkyv::{map::ArchivedNodeRepr, ArchivedPrefixMap, ArchivedPrefixSet},
    table::K,
    trieview::ViewIter,
    AsView, Prefix, TrieView,
};

/// An immutable cursor into an [`ArchivedPrefixMap`] implementing [`TrieView`].
///
/// # Invariant
///
/// `depth <= prefix_len < depth + K`, where `K` is the stride of a `MultiBitNode`.
/// `depth` is always a multiple of `K`.
/// `key` contains the accumulated bits (only the top `prefix_len` bits are significant).
#[derive(Clone, Copy)]
pub struct ArchivedTrieRef<'a, P: Prefix, T: Archive> {
    nodes: &'a [ArchivedNodeRepr],
    data: &'a [T::Archived],
    // Location of the current `ArchivedNodeRepr` that contains this view's root position.
    node_loc: u32,
    // Depth of `node_loc`': always a multiple of `K`
    depth: u32,
    // Accumulated key bits (only the top `prefix_len` bits are significant)
    key: P::R,
    // Binary-tree depth of this view's root position
    prefix_len: u32,
}

impl<'a, P: Prefix, T: Archive> ArchivedTrieRef<'a, P, T> {
    pub(super) fn new_root(archive: &'a ArchivedPrefixMap<P, T>) -> Self {
        Self {
            nodes: archive.nodes.as_slice(),
            data: archive.data.as_slice(),
            node_loc: 0,
            depth: 0,
            key: P::R::zero(),
            prefix_len: 0,
        }
    }
}

impl<'a, P: Prefix, T: Archive> TrieView<'a> for ArchivedTrieRef<'a, P, T> {
    type P = P;
    type T = &'a T::Archived;

    #[inline]
    fn depth(&self) -> u32 {
        self.depth
    }

    #[inline]
    fn key(&self) -> <Self::P as Prefix>::R {
        self.key
    }

    #[inline]
    fn prefix_len(&self) -> u32 {
        self.prefix_len
    }

    #[inline]
    fn data_bitmap(&self) -> u32 {
        self.nodes[self.node_loc as usize].data_bitmap.to_native()
            & data_cover_mask(self.depth, self.key, self.prefix_len)
    }

    fn child_bitmap(&self) -> u32 {
        self.nodes[self.node_loc as usize].child_bitmap.to_native()
            & child_cover_mask(self.depth, self.key, self.prefix_len)
    }

    #[inline]
    unsafe fn get_data(&mut self, data_bit: u32) -> Self::T {
        // construct the index into the value
        let node = &self.nodes[self.node_loc as usize];
        let slot = compute_slot(node.data_bitmap.to_native(), data_bit);
        let idx = node.data_idx.to_native() + slot;
        &self.data[idx as usize]
    }

    #[inline]
    unsafe fn get_child(&mut self, child_bit: u32) -> Self {
        let node = &self.nodes[self.node_loc as usize];
        let slot = compute_slot(node.child_bitmap.to_native(), child_bit);
        let idx = node.children_idx.to_native() + slot;
        let new_key = extend_repr(self.key, self.depth, child_bit);
        Self {
            nodes: self.nodes,
            data: self.data,
            node_loc: idx,
            depth: self.depth + K,
            key: new_key,
            prefix_len: self.depth + K,
        }
    }

    #[inline]
    unsafe fn reposition(&mut self, key: <Self::P as Prefix>::R, prefix_len: u32) {
        let _old_prefix = self.prefix();
        self.key = key;
        self.prefix_len = prefix_len;
        debug_assert!(_old_prefix.contains(&self.prefix()));
    }
}

impl<'a, P: Prefix, T: Archive> IntoIterator for ArchivedTrieRef<'a, P, T> {
    type Item = (P, &'a T::Archived);
    type IntoIter = ViewIter<'a, ArchivedTrieRef<'a, P, T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, P: Prefix, T: Archive> AsView<'a> for ArchivedTrieRef<'a, P, T> {
    type P = P;
    type View = ArchivedTrieRef<'a, P, T>;

    fn view(self) -> ArchivedTrieRef<'a, P, T> {
        self
    }
}

impl<'a, P: Prefix, T: Archive> AsView<'a> for &'a ArchivedPrefixMap<P, T> {
    type P = P;
    type View = ArchivedTrieRef<'a, P, T>;

    fn view(self) -> ArchivedTrieRef<'a, P, T> {
        ArchivedTrieRef::new_root(self)
    }
}

impl<'a, P: Prefix> AsView<'a> for &'a ArchivedPrefixSet<P> {
    type P = P;
    type View = ArchivedTrieRef<'a, P, ()>;

    fn view(self) -> ArchivedTrieRef<'a, P, ()> {
        ArchivedTrieRef::new_root(&self.0)
    }
}

#[cfg(test)]
mod tests {
    use rkyv::{access, rancor::Error, to_bytes};

    use crate::{
        rkyv::{view::ArchivedTrieRef, ArchivedPrefixMap},
        trieview::{AsView, TrieView},
        Prefix, PrefixMap,
    };

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

    fn into_bytes(entries: &[(u32, u8, i32)]) -> Vec<u8> {
        let map = map_from(entries);
        let data = to_bytes::<Error>(&map).unwrap();
        data.into_vec()
    }

    fn archive(data: &[u8]) -> &ArchivedPrefixMap<P, i32> {
        access::<ArchivedPrefixMap<P, i32>, Error>(data).unwrap()
    }

    impl<'a, P: Prefix> ArchivedTrieRef<'a, P, i32> {
        fn native_value(self) -> Option<i32> {
            self.value().map(|x| x.to_native())
        }
    }

    #[test]
    fn view_iter_all() {
        let bytes = into_bytes(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a020000, 16, 3),
            (0x0a010000, 24, 4),
        ]);
        let m = archive(&bytes);
        let expected: Vec<(P, i32)> = vec![
            ((0x0a000000, 8), 1),
            ((0x0a010000, 16), 2),
            ((0x0a010000, 24), 4),
            ((0x0a020000, 16), 3),
        ];
        let from_view: Vec<(P, i32)> = m.view().iter().map(|(p, v)| (p, v.to_native())).collect();
        assert_eq!(from_view, expected);
    }

    #[test]
    fn view_at_subtrie() {
        let bytes = into_bytes(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a020000, 16, 3),
            (0x0a010000, 24, 4),
        ]);
        let m = archive(&bytes);
        let got: Vec<_> = m
            .view_at(&p(0x0a010000, 16))
            .map(|v| {
                v.iter()
                    .map(|(p, x)| (p, x.to_native()))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        assert_eq!(got, vec![(p(0x0a010000, 16), 2), (p(0x0a010000, 24), 4)]);
    }

    #[test]
    fn view_value() {
        let bytes = into_bytes(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let m = archive(&bytes);
        let v = m.view().find(&p(0x0a010000, 16)).unwrap();
        assert_eq!(v.native_value(), Some(2));
        let v2 = m.view().find(&p(0x0a000000, 8)).unwrap();
        assert_eq!(v2.native_value(), Some(1));
    }

    #[test]
    fn view_find_exact() {
        let bytes = into_bytes(&[(0x0a000000, 8, 1), (0x0a010000, 24, 4)]);
        let m = archive(&bytes);
        assert!(m.view().find_exact(&p(0x0a010000, 16)).is_none());
        assert!(m.view().find_exact(&p(0x0a000000, 8)).is_some());
    }

    #[test]
    fn view_find_exact_value() {
        let bytes = into_bytes(&[(0x0a000000, 8, 1), (0x0a010000, 24, 4)]);
        let m = archive(&bytes);
        assert_eq!(m.view().find_exact_value(&p(0x0a010000, 16)), None);
        assert_eq!(
            m.view()
                .find_exact_value(&p(0x0a010000, 24))
                .map(|(p, v)| (p, v.to_native())),
            Some((p(0x0a010000, 24), 4))
        );
    }

    #[test]
    fn view_find_lpm() {
        let bytes = into_bytes(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 3)]);
        let m = archive(&bytes);
        let v = m.view().find_lpm(&p(0x0a010180, 25)).unwrap();
        assert_eq!(v.prefix(), p(0x0a010100, 24));
        assert_eq!(v.native_value(), Some(3));

        let v = m.view().find_lpm(&p(0x0a020000, 16)).unwrap();
        assert_eq!(v.prefix(), p(0x0a000000, 8));
        assert_eq!(v.native_value(), Some(1));
        assert!(m.view().find_lpm(&p(0x0b000000, 8)).is_none());
    }

    #[test]
    fn view_find_lpm_value() {
        let bytes = into_bytes(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 3)]);
        let m = archive(&bytes);
        assert_eq!(
            m.view()
                .find_lpm_value(&p(0x0a010180, 25))
                .map(|(p, v)| (p, v.to_native())),
            Some((p(0x0a010100, 24), 3))
        );
    }

    #[test]
    fn view_prefix_value_keys_values() {
        let bytes = into_bytes(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let m = archive(&bytes);
        assert_eq!(
            m.view()
                .find_exact(&p(0x0a010000, 16))
                .unwrap()
                .prefix_value()
                .map(|(p, v)| (p, v.to_native())),
            Some((p(0x0a010000, 16), 2))
        );
        assert_eq!(
            m.view().keys().collect::<Vec<_>>(),
            vec![p(0x0a000000, 8), p(0x0a010000, 16)]
        );
        assert_eq!(m.view().values().copied().collect::<Vec<_>>(), vec![1, 2]);
    }

    #[test]
    fn view_prefix_reconstruction() {
        let bytes = into_bytes(&[(0x0a010203, 32, 99)]);
        let m = archive(&bytes);
        let v = m.view().find_exact(&p(0x0a010203, 32)).unwrap();
        assert_eq!(v.prefix(), p(0x0a010203, 32));
        assert_eq!(v.native_value(), Some(99));
    }

    #[test]
    fn view_into_iter() {
        let bytes = into_bytes(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let m = archive(&bytes);
        // TrieRef: for loop via IntoIterator
        let from_for: Vec<(P, i32)> = m
            .view()
            .into_iter()
            .map(|(p, v)| (p, v.to_native()))
            .collect();
        let expected = vec![((0x0a000000, 8), 1), ((0x0a010000, 16), 2)];
        assert_eq!(from_for, expected);
    }

    // -- iter_from on views --

    #[test]
    fn view_iter_from_inclusive() {
        // 10.0.0.0/8, 10.1.0.0/16, 10.2.0.0/16, 10.3.0.0/16, 10.4.0.0/16
        let bytes = into_bytes(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a020000, 16, 3),
            (0x0a030000, 16, 4),
            (0x0a040000, 16, 5),
        ]);
        let m = archive(&bytes);

        // From first entry → everything
        let all: Vec<_> = m
            .view()
            .iter_from(&p(0x0a000000, 8), true)
            .map(|(p, v)| (p, v.to_native()))
            .collect();
        assert_eq!(
            all,
            vec![
                ((0x0a000000, 8), 1),
                ((0x0a010000, 16), 2),
                ((0x0a020000, 16), 3),
                ((0x0a030000, 16), 4),
                ((0x0a040000, 16), 5),
            ]
        );

        // From a middle entry
        let from_mid: Vec<_> = m
            .view()
            .iter_from(&p(0x0a020000, 16), true)
            .map(|(p, v)| (p, v.to_native()))
            .collect();
        assert_eq!(
            from_mid,
            vec![
                (p(0x0a020000, 16), 3),
                (p(0x0a030000, 16), 4),
                (p(0x0a040000, 16), 5)
            ]
        );

        // From last entry
        let last: Vec<_> = m
            .view()
            .iter_from(&p(0x0a040000, 16), true)
            .map(|(p, v)| (p, v.to_native()))
            .collect();
        assert_eq!(last, vec![(p(0x0a040000, 16), 5)]);
    }

    #[test]
    fn view_iter_from_exclusive() {
        let bytes = into_bytes(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a020000, 16, 3),
            (0x0a030000, 16, 4),
            (0x0a040000, 16, 5),
        ]);
        let m = archive(&bytes);

        let after_mid: Vec<_> = m
            .view()
            .iter_from(&p(0x0a020000, 16), false)
            .map(|(p, v)| (p, v.to_native()))
            .collect();
        assert_eq!(
            after_mid,
            vec![(p(0x0a030000, 16), 4), (p(0x0a040000, 16), 5)]
        );

        // Exclusive from last → empty
        let after_last: Vec<_> = m.view().iter_from(&p(0x0a040000, 16), false).collect();
        assert!(after_last.is_empty());

        // Pagination
        let page: Vec<_> = m
            .view()
            .iter_from(&p(0x0a010000, 16), false)
            .take(2)
            .map(|(p, v)| (p, v.to_native()))
            .collect();
        assert_eq!(page, vec![(p(0x0a020000, 16), 3), (p(0x0a030000, 16), 4)]);
    }

    #[test]
    fn view_iter_from_nonexistent() {
        let bytes = into_bytes(&[(0x0a000000, 8, 1), (0x0a020000, 16, 2), (0x0a040000, 16, 3)]);
        let m = archive(&bytes);

        // Non-existent prefix between entries
        let from: Vec<_> = m
            .view()
            .iter_from(&p(0x0a010000, 16), true)
            .map(|(p, v)| (p, v.to_native()))
            .collect();
        assert_eq!(from, vec![(p(0x0a020000, 16), 2), (p(0x0a040000, 16), 3)]);

        // Past all entries
        let from: Vec<_> = m.view().iter_from(&p(0x0b000000, 8), true).collect();
        assert!(from.is_empty());
    }

    #[test]
    fn view_iter_from_empty() {
        let bytes = into_bytes(&[]);
        let m = archive(&bytes);
        let from: Vec<_> = m.view().iter_from(&p(0x0a000000, 8), true).collect();
        assert!(from.is_empty());
    }

    #[test]
    fn view_iter_from_parent_child() {
        let bytes = into_bytes(&[
            (0x0a000000, 8, 1),
            (0x0a000000, 16, 2),
            (0x0a000000, 24, 3),
            (0x0a010000, 16, 4),
        ]);
        let m = archive(&bytes);

        // Exclusive from parent → children only
        let from: Vec<_> = m
            .view()
            .iter_from(&p(0x0a000000, 8), false)
            .map(|(p, v)| (p, v.to_native()))
            .collect();
        assert_eq!(
            from,
            vec![
                (p(0x0a000000, 16), 2),
                (p(0x0a000000, 24), 3),
                (p(0x0a010000, 16), 4)
            ]
        );
    }

    #[test]
    fn view_iter_from_subview() {
        let bytes = into_bytes(&[
            (0x0a000000, 8, 1),  // 10.0.0.0/8
            (0x0a010000, 16, 2), // 10.1.0.0/16
            (0x0a010000, 24, 3), // 10.1.0.0/24
            (0x0a020000, 16, 4), // 10.2.0.0/16
            (0x0b000000, 8, 5),  // 11.0.0.0/8  — outside sub-view
        ]);
        let m = archive(&bytes);

        // Sub-view at 10.1.0.0/16 excludes 10/8, 10.2/16, 11/8
        let sub = m.view_at(&p(0x0a010000, 16)).unwrap();
        let all: Vec<_> = sub.iter().map(|(p, v)| (p, v.to_native())).collect();
        assert_eq!(all, vec![(p(0x0a010000, 16), 2), (p(0x0a010000, 24), 3)]);

        // iter_from exclusive skips the root of the sub-view
        let from: Vec<_> = sub
            .iter_from(&p(0x0a010000, 16), false)
            .map(|(p, v)| (p, v.to_native()))
            .collect();
        assert_eq!(from, vec![(p(0x0a010000, 24), 3)]);
    }

    #[test]
    fn view_iter_from_outside_subview() {
        let bytes = into_bytes(&[
            (0x0a010000, 16, 1),
            (0x0a010000, 24, 2),
            (0x0a020000, 16, 3),
        ]);
        let m = archive(&bytes);

        // Sub-view at 10.1.0.0/16; target before sub-view → full iter
        let sub = m.view_at(&p(0x0a010000, 16)).unwrap();
        let from: Vec<_> = sub
            .iter_from(&p(0x09000000, 8), true)
            .map(|(p, v)| (p, *v))
            .collect();
        let all: Vec<_> = sub.iter().map(|(p, v)| (p, *v)).collect();
        assert_eq!(from, all);

        // Sub-view at 10.1.0.0/16; target after sub-view → empty
        let sub = m.view_at(&p(0x0a010000, 16)).unwrap();
        let from: Vec<_> = sub.iter_from(&p(0x0a020000, 16), true).collect();
        assert!(from.is_empty());
    }

    #[test]
    fn view_right_at_max_prefix_len() {
        // Calling right() on a view at prefix_len == num_bits (32 for u32) must
        // not panic. step() computes bit_pos = num_bits - prefix_len - 1 which
        // underflows when prefix_len == num_bits.
        let bytes = into_bytes(&[(0x01020304, 32, 1)]);
        let m = archive(&bytes);
        let v = m.view().find(&p(0x01020304, 32)).unwrap();
        assert_eq!(v.prefix_len(), 32);
        // This should return None (can't go deeper than /32), not panic.
        assert!(v.right().is_none());
        assert!(v.left().is_none());
    }

    #[test]
    fn view_find_exact_slash32() {
        let bytes = into_bytes(&[
            (0x01020300, 32, 1),
            (0x01020301, 32, 2),
            (0x01020302, 32, 3),
            (0x01020303, 32, 4),
        ]);
        let m = archive(&bytes);
        for repr in 0x01020300..=0x01020303u32 {
            let v = m.view().find_exact(&p(repr, 32)).unwrap();
            assert_eq!(v.prefix(), p(repr, 32));
            assert_eq!(v.native_value(), Some((repr - 0x01020300 + 1) as i32));
        }
        assert!(m.view().find_exact(&p(0x01020304, 32)).is_none());
    }

    #[test]
    fn view_find_lpm_slash32() {
        let bytes = into_bytes(&[(0x01020300, 24, 10), (0x01020304, 32, 42)]);
        let m = archive(&bytes);
        let v = m.view().find_lpm(&p(0x01020304, 32)).unwrap();
        assert_eq!(v.prefix(), p(0x01020304, 32));
        assert_eq!(v.native_value(), Some(42));

        // LPM for a /32 without an exact match should find the covering /24
        let v = m.view().find_lpm(&p(0x01020305, 32)).unwrap();
        assert_eq!(v.prefix(), p(0x01020300, 24));
        assert_eq!(v.native_value(), Some(10));
    }

    #[test]
    fn view_navigate_to_slash32() {
        let bytes = into_bytes(&[(0x01020304, 32, 1)]);
        let m = archive(&bytes);
        let v = m.view().find(&p(0x01020304, 32)).unwrap();
        assert_eq!(v.prefix_len(), 32);
        assert_eq!(v.prefix(), p(0x01020304, 32));
        assert_eq!(v.native_value(), Some(1));
    }

    #[test]
    fn view_iter_at_slash32() {
        // A view navigated to a /32 should iterate only that single entry.
        let bytes = into_bytes(&[
            (0x01020300, 24, 10),
            (0x01020304, 32, 42),
            (0x01020305, 32, 43),
        ]);
        let m = archive(&bytes);
        let v = m.view().find(&p(0x01020304, 32)).unwrap();
        let entries: Vec<_> = v.iter().map(|(k, v)| (k, v.to_native())).collect();
        assert_eq!(entries, vec![(p(0x01020304, 32), 42)]);
    }

    #[test]
    fn view_step_through_all_depths() {
        // Walk from root to a /32 via left()/right(), one bit at a time.
        // Key 0xAAAAAAAA = 1010_1010_... so we alternate right/left.
        let key = 0xAAAAAAAAu32;
        let bytes = into_bytes(&[(key, 32, 99)]);
        let m = archive(&bytes);
        let mut v = m.view();
        for bit in 0..32u32 {
            let go_right = (key >> (31 - bit)) & 1 == 1;
            v = if go_right {
                v.right()
                    .unwrap_or_else(|| panic!("right() failed at bit {bit}"))
            } else {
                v.left()
                    .unwrap_or_else(|| panic!("left() failed at bit {bit}"))
            };
        }
        assert_eq!(v.prefix_len(), 32);
        assert_eq!(v.prefix(), p(key, 32));
        assert_eq!(v.native_value(), Some(99));
        // One more step should return None
        assert!(v.left().is_none());
        assert!(v.right().is_none());
    }
}
