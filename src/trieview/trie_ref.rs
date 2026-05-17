//! Concrete [`TrieRef`] cursor implementing [`TrieView`].
//!
//! [`TrieRef`] is a lightweight, `Copy`able immutable cursor. All set-operation views
//! ([`IntersectionView`][super::IntersectionView], [`UnionView`][super::union::UnionView],
//! etc.) can be composed from `TrieRef` leaves.

use std::marker::PhantomData;

use num_traits::Zero;

use crate::{
    Prefix,
    {
        allocator::Loc,
        map::PrefixMap,
        node::{child_cover_mask, data_cover_mask, extend_repr},
        table::{DataIdx, Table, K},
    },
};

use super::{AsView, TrieView, ViewIter};

/// An immutable cursor implementing [`TrieView`].
///
/// # Invariant
///
/// `depth <= prefix_len < depth + K`, where `K` is the stride of a `MultiBitNode`.
/// `depth` is always a multiple of `K`.
/// `key` contains the accumulated bits (only the top `prefix_len` bits are significant).
pub struct TrieRef<'a, P: Prefix, T> {
    pub(super) table: &'a Table<T>,
    /// Location of the `MultiBitNode` that contains this view's root position.
    pub(super) node_loc: Loc,
    /// Depth of `node_loc`: always a multiple of `K`.
    pub(super) depth: u32,
    /// Accumulated key bits (only the top `prefix_len` bits are significant).
    pub(super) key: P::R,
    /// Binary-tree depth of this view's root position.
    pub(super) prefix_len: u32,
    pub(super) _marker: PhantomData<P>,
}

// `TrieRef` holds only a shared reference (`&'a Table<T>`) and a `Loc` + key bits,
// so it is always `Copy`/`Clone` regardless of whether `P` or `T` are.
impl<'a, P: Prefix, T> Clone for TrieRef<'a, P, T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<'a, P: Prefix, T> Copy for TrieRef<'a, P, T> {}

impl<'a, P: Prefix, T> TrieRef<'a, P, T> {
    /// Create a view at the root of the given table.
    pub(crate) fn new_root(table: &'a Table<T>) -> Self {
        Self {
            table,
            node_loc: Loc::root(),
            depth: 0,
            key: P::R::zero(),
            prefix_len: 0,
            _marker: PhantomData,
        }
    }
}

impl<'a, P: Prefix, T> TrieView<'a> for TrieRef<'a, P, T> {
    type P = P;
    type T = &'a T;

    #[inline]
    fn depth(&self) -> u32 {
        self.depth
    }

    #[inline]
    fn key(&self) -> P::R {
        self.key
    }

    #[inline]
    fn prefix_len(&self) -> u32 {
        self.prefix_len
    }

    #[inline]
    fn data_bitmap(&self) -> u32 {
        self.table.node(self.node_loc).data_bitmap()
            & data_cover_mask(self.depth, self.key, self.prefix_len)
    }

    #[inline]
    fn child_bitmap(&self) -> u32 {
        self.table.node(self.node_loc).child_bitmap()
            & child_cover_mask(self.depth, self.key, self.prefix_len)
    }

    #[inline]
    unsafe fn get_data(&mut self, data_bit: u32) -> &'a T {
        let idx = DataIdx {
            node: self.node_loc,
            bit: data_bit,
            depth: self.depth,
        };
        // Note: `resolve` re-reads the node's current AllocIdx and bitmap, which is strictly
        // unnecessary here: TrieView iterators never mutate node structure, so `idx.node` is
        // always a valid, stable location for the lifetime of this view. We use `resolve` for
        // uniformity with the rest of the codebase; the compiler should inline/optimize it away.
        //
        // SAFETY: caller guarantees data_bit is set in data_bitmap().
        unsafe { idx.resolve(self.table) }
            .expect("get_data: data_bit not set in bitmap")
            .get()
    }

    #[inline]
    unsafe fn get_child(&mut self, child_bit: u32) -> Self {
        // SAFETY: `self.node_loc` is maintained as a valid, live node location by the
        // `TrieView` invariant (no structural mutations during the view's lifetime).
        let child_loc = unsafe { self.table.child(self.node_loc, child_bit) }
            .expect("get_child: child_bit not set in bitmap");
        let new_key = extend_repr(self.key, self.depth, child_bit);
        Self {
            table: self.table,
            node_loc: child_loc,
            depth: self.depth + K,
            key: new_key,
            prefix_len: self.depth + K,
            _marker: PhantomData,
        }
    }

    #[inline]
    unsafe fn reposition(&mut self, key: P::R, prefix_len: u32) {
        let _old_prefix = self.prefix();
        self.key = key;
        self.prefix_len = prefix_len;
        // ensure that we always go deeper inside.
        debug_assert!(_old_prefix.contains(&self.prefix()));
    }
}

impl<'a, P: Prefix, T> IntoIterator for TrieRef<'a, P, T> {
    type Item = (P, &'a T);
    type IntoIter = ViewIter<'a, TrieRef<'a, P, T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, P: Prefix, T> AsView<'a> for &'a PrefixMap<P, T> {
    type P = P;
    type View = TrieRef<'a, P, T>;

    fn view(self) -> TrieRef<'a, P, T> {
        TrieRef::new_root(self.table())
    }
}

impl<'a, P: Prefix, T> AsView<'a> for TrieRef<'a, P, T> {
    type P = P;
    type View = TrieRef<'a, P, T>;

    fn view(self) -> TrieRef<'a, P, T> {
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

    #[test]
    fn view_iter_all() {
        let m = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a020000, 16, 3),
            (0x0a010000, 24, 4),
        ]);
        let expected: Vec<(P, i32)> = m.iter().map(|(p, v)| (p, *v)).collect();
        let from_view: Vec<(P, i32)> = m.view().iter().map(|(p, v)| (p, *v)).collect();
        assert_eq!(from_view, expected);
    }

    #[test]
    fn view_at_subtrie() {
        let m = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a020000, 16, 3),
            (0x0a010000, 24, 4),
        ]);
        let got: Vec<_> = m
            .view_at(&p(0x0a010000, 16))
            .map(|v| v.iter().map(|(p, x)| (p, *x)).collect::<Vec<_>>())
            .unwrap_or_default();
        assert_eq!(got, vec![(p(0x0a010000, 16), 2), (p(0x0a010000, 24), 4)]);
    }

    #[test]
    fn view_value() {
        let m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let v = m.view().find(&p(0x0a010000, 16)).unwrap();
        assert_eq!(v.value(), Some(&2));
        let v2 = m.view().find(&p(0x0a000000, 8)).unwrap();
        assert_eq!(v2.value(), Some(&1));
    }

    #[test]
    fn view_find_exact() {
        let m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 24, 4)]);
        assert!(m.view().find_exact(&p(0x0a010000, 16)).is_none());
        assert!(m.view().find_exact(&p(0x0a000000, 8)).is_some());
    }

    #[test]
    fn view_find_exact_value() {
        let m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 24, 4)]);
        assert_eq!(m.view().find_exact_value(&p(0x0a010000, 16)), None);
        assert_eq!(
            m.view()
                .find_exact_value(&p(0x0a010000, 24))
                .map(|(p, v)| (p, *v)),
            Some((p(0x0a010000, 24), 4))
        );
    }

    #[test]
    fn view_find_lpm() {
        let m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 3)]);
        let v = m.view().find_lpm(&p(0x0a010180, 25)).unwrap();
        assert_eq!(v.prefix(), p(0x0a010100, 24));
        assert_eq!(v.value(), Some(&3));

        let v = m.view().find_lpm(&p(0x0a020000, 16)).unwrap();
        assert_eq!(v.prefix(), p(0x0a000000, 8));
        assert_eq!(v.value(), Some(&1));
        assert!(m.view().find_lpm(&p(0x0b000000, 8)).is_none());
    }

    #[test]
    fn view_find_lpm_value() {
        let m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 3)]);
        assert_eq!(
            m.view()
                .find_lpm_value(&p(0x0a010180, 25))
                .map(|(p, v)| (p, *v)),
            Some((p(0x0a010100, 24), 3))
        );
    }

    #[test]
    fn view_prefix_value_keys_values() {
        let m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        assert_eq!(
            m.view()
                .find_exact(&p(0x0a010000, 16))
                .unwrap()
                .prefix_value()
                .map(|(p, v)| (p, *v)),
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
        let m = map_from(&[(0x0a010203, 32, 99)]);
        let v = m.view().find_exact(&p(0x0a010203, 32)).unwrap();
        assert_eq!(v.prefix(), p(0x0a010203, 32));
        assert_eq!(v.value(), Some(&99));
    }

    #[test]
    fn view_into_iter() {
        let m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        // TrieRef: for loop via IntoIterator
        let from_for: Vec<(P, i32)> = m.view().into_iter().map(|(p, v)| (p, *v)).collect();
        let expected: Vec<(P, i32)> = m.iter().map(|(p, v)| (p, *v)).collect();
        assert_eq!(from_for, expected);
    }

    // -- iter_from on views --

    #[test]
    fn view_iter_from_inclusive() {
        // 10.0.0.0/8, 10.1.0.0/16, 10.2.0.0/16, 10.3.0.0/16, 10.4.0.0/16
        let m = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a020000, 16, 3),
            (0x0a030000, 16, 4),
            (0x0a040000, 16, 5),
        ]);

        // From first entry → everything
        let all: Vec<_> = m
            .view()
            .iter_from(&p(0x0a000000, 8), true)
            .map(|(p, v)| (p, *v))
            .collect();
        assert_eq!(all, m.iter().map(|(p, v)| (p, *v)).collect::<Vec<_>>());

        // From a middle entry
        let from_mid: Vec<_> = m
            .view()
            .iter_from(&p(0x0a020000, 16), true)
            .map(|(p, v)| (p, *v))
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
            .map(|(p, v)| (p, *v))
            .collect();
        assert_eq!(last, vec![(p(0x0a040000, 16), 5)]);
    }

    #[test]
    fn view_iter_from_exclusive() {
        let m = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a020000, 16, 3),
            (0x0a030000, 16, 4),
            (0x0a040000, 16, 5),
        ]);

        let after_mid: Vec<_> = m
            .view()
            .iter_from(&p(0x0a020000, 16), false)
            .map(|(p, v)| (p, *v))
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
            .map(|(p, v)| (p, *v))
            .collect();
        assert_eq!(page, vec![(p(0x0a020000, 16), 3), (p(0x0a030000, 16), 4)]);
    }

    #[test]
    fn view_iter_from_nonexistent() {
        let m = map_from(&[(0x0a000000, 8, 1), (0x0a020000, 16, 2), (0x0a040000, 16, 3)]);

        // Non-existent prefix between entries
        let from: Vec<_> = m
            .view()
            .iter_from(&p(0x0a010000, 16), true)
            .map(|(p, v)| (p, *v))
            .collect();
        assert_eq!(from, vec![(p(0x0a020000, 16), 2), (p(0x0a040000, 16), 3)]);

        // Past all entries
        let from: Vec<_> = m.view().iter_from(&p(0x0b000000, 8), true).collect();
        assert!(from.is_empty());
    }

    #[test]
    fn view_iter_from_empty() {
        let m: PrefixMap<P, i32> = PrefixMap::new();
        let from: Vec<_> = m.view().iter_from(&p(0x0a000000, 8), true).collect();
        assert!(from.is_empty());
    }

    #[test]
    fn view_iter_from_parent_child() {
        let m = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a000000, 16, 2),
            (0x0a000000, 24, 3),
            (0x0a010000, 16, 4),
        ]);

        // Exclusive from parent → children only
        let from: Vec<_> = m
            .view()
            .iter_from(&p(0x0a000000, 8), false)
            .map(|(p, v)| (p, *v))
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
        let m = map_from(&[
            (0x0a000000, 8, 1),  // 10.0.0.0/8
            (0x0a010000, 16, 2), // 10.1.0.0/16
            (0x0a010000, 24, 3), // 10.1.0.0/24
            (0x0a020000, 16, 4), // 10.2.0.0/16
            (0x0b000000, 8, 5),  // 11.0.0.0/8  — outside sub-view
        ]);

        // Sub-view at 10.1.0.0/16 excludes 10/8, 10.2/16, 11/8
        let sub = m.view_at(&p(0x0a010000, 16)).unwrap();
        let all: Vec<_> = sub.iter().map(|(p, v)| (p, *v)).collect();
        assert_eq!(all, vec![(p(0x0a010000, 16), 2), (p(0x0a010000, 24), 3)]);

        // iter_from exclusive skips the root of the sub-view
        let from: Vec<_> = sub
            .iter_from(&p(0x0a010000, 16), false)
            .map(|(p, v)| (p, *v))
            .collect();
        assert_eq!(from, vec![(p(0x0a010000, 24), 3)]);
    }

    #[test]
    fn view_iter_from_outside_subview() {
        let m = map_from(&[
            (0x0a010000, 16, 1),
            (0x0a010000, 24, 2),
            (0x0a020000, 16, 3),
        ]);

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
        let m = map_from(&[(0x01020304, 32, 1)]);
        let v = m.view().find(&p(0x01020304, 32)).unwrap();
        assert_eq!(v.prefix_len(), 32);
        // This should return None (can't go deeper than /32), not panic.
        assert!(v.right().is_none());
        assert!(v.left().is_none());
    }

    #[test]
    fn view_find_exact_slash32() {
        let m = map_from(&[
            (0x01020300, 32, 1),
            (0x01020301, 32, 2),
            (0x01020302, 32, 3),
            (0x01020303, 32, 4),
        ]);
        for repr in 0x01020300..=0x01020303u32 {
            let v = m.view().find_exact(&p(repr, 32)).unwrap();
            assert_eq!(v.prefix(), p(repr, 32));
            assert_eq!(v.value(), Some(&((repr - 0x01020300 + 1) as i32)));
        }
        assert!(m.view().find_exact(&p(0x01020304, 32)).is_none());
    }

    #[test]
    fn view_find_lpm_slash32() {
        let m = map_from(&[(0x01020300, 24, 10), (0x01020304, 32, 42)]);
        let v = m.view().find_lpm(&p(0x01020304, 32)).unwrap();
        assert_eq!(v.prefix(), p(0x01020304, 32));
        assert_eq!(v.value(), Some(&42));

        // LPM for a /32 without an exact match should find the covering /24
        let v = m.view().find_lpm(&p(0x01020305, 32)).unwrap();
        assert_eq!(v.prefix(), p(0x01020300, 24));
        assert_eq!(v.value(), Some(&10));
    }

    #[test]
    fn view_navigate_to_slash32() {
        let m = map_from(&[(0x01020304, 32, 1)]);
        let v = m.view().find(&p(0x01020304, 32)).unwrap();
        assert_eq!(v.prefix_len(), 32);
        assert_eq!(v.prefix(), p(0x01020304, 32));
        assert_eq!(v.value(), Some(&1));
    }

    #[test]
    fn view_iter_at_slash32() {
        // A view navigated to a /32 should iterate only that single entry.
        let m = map_from(&[
            (0x01020300, 24, 10),
            (0x01020304, 32, 42),
            (0x01020305, 32, 43),
        ]);
        let v = m.view().find(&p(0x01020304, 32)).unwrap();
        let entries: Vec<_> = v.iter().map(|(k, v)| (k, *v)).collect();
        assert_eq!(entries, vec![(p(0x01020304, 32), 42)]);
    }

    #[test]
    fn view_step_through_all_depths() {
        // Walk from root to a /32 via left()/right(), one bit at a time.
        // Key 0xAAAAAAAA = 1010_1010_... so we alternate right/left.
        let key = 0xAAAAAAAAu32;
        let m = map_from(&[(key, 32, 99)]);
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
        assert_eq!(v.value(), Some(&99));
        // One more step should return None
        assert!(v.left().is_none());
        assert!(v.right().is_none());
    }
}
