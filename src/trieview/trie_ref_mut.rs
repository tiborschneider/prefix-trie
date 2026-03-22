//! Concrete [`TrieRefMut`] cursor implementing [`TrieView`].

use std::marker::PhantomData;

use num_traits::Zero;

use crate::{
    Prefix,
    {
        allocator::{Loc, RawPtr},
        node::{child_cover_mask, data_cover_mask, extend_repr},
        table::{Table, K},
        AsView, PrefixMap,
    },
};

use super::{TrieView, ViewIter};

/// A mutable cursor implementing [`TrieView`].
///
/// # Invariant
///
/// `depth <= prefix_len < depth + K`, where `K` is the stride of a `MultiBitNode`.
/// `depth` is always a multiple of `K`.
/// `key` contains the accumulated bits (only the top `prefix_len` bits are significant).
pub struct TrieRefMut<'a, P: Prefix, T> {
    pub(super) table: &'a Table<T>,
    /// a raw pointer into the data of the table used to access mutable references to data
    pub(super) raw: RawPtr<T>,
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

impl<'a, P: Prefix, T> TrieRefMut<'a, P, T> {
    /// Create a view at the root of the given table.
    pub(crate) fn new_root(table: &'a Table<T>, raw: RawPtr<T>) -> Self {
        Self {
            table,
            raw,
            node_loc: Loc::root(),
            depth: 0,
            key: P::R::zero(),
            prefix_len: 0,
            _marker: PhantomData,
        }
    }
}

impl<'a, P: Prefix, T> TrieView<'a> for TrieRefMut<'a, P, T> {
    type P = P;
    type T = &'a mut T;

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
    unsafe fn get_data(&mut self, data_bit: u32) -> &'a mut T {
        let node = self.table.node(self.node_loc);
        // SAFETY: caller guarantees data_bit is set in data_bitmap().
        let present = node
            .data_loc_if_present(self.node_loc, self.depth, data_bit)
            .expect("get_data: data_bit not set in bitmap");
        self.table.unsafe_get_mut(&mut self.raw, present)
    }

    #[inline]
    unsafe fn get_child(&mut self, child_bit: u32) -> Self {
        let child_loc = self
            .table
            .child(self.node_loc, child_bit)
            .expect("get_child: child_bit not set in bitmap");
        let new_key = extend_repr(self.key, self.depth, child_bit);
        Self {
            table: self.table,
            raw: self.raw,
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

impl<'a, P: Prefix, T> IntoIterator for TrieRefMut<'a, P, T> {
    type Item = (P, &'a mut T);
    type IntoIter = ViewIter<'a, TrieRefMut<'a, P, T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, P: Prefix, T> AsView<'a> for &'a mut PrefixMap<P, T> {
    type P = P;
    type View = TrieRefMut<'a, P, T>;

    fn view(self) -> TrieRefMut<'a, P, T> {
        let raw = self.table_mut().raw_cells();
        TrieRefMut::new_root(self.table(), raw)
    }
}

impl<'a, P: Prefix, T> AsView<'a> for TrieRefMut<'a, P, T> {
    type P = P;
    type View = TrieRefMut<'a, P, T>;

    fn view(self) -> TrieRefMut<'a, P, T> {
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
    fn view_mut_iter_all() {
        let mut m = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a020000, 16, 3),
            (0x0a010000, 24, 4),
        ]);
        let expected: Vec<(P, i32)> = m.iter_mut().map(|(p, v)| (p, *v)).collect();
        let from_view: Vec<(P, i32)> = (&mut m).view().iter().map(|(p, v)| (p, *v)).collect();
        assert_eq!(from_view, expected);
    }

    #[test]
    fn view_mut_at_subtrie() {
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
    fn view_mut_value() {
        let mut m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let v = (&mut m).view().find(&p(0x0a010000, 16)).unwrap();
        assert_eq!(v.value(), Some(&mut 2));
        let v2 = (&mut m).view().find(&p(0x0a000000, 8)).unwrap();
        assert_eq!(v2.value(), Some(&mut 1));
    }

    #[test]
    fn view_mut_find_exact() {
        let mut m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 24, 4)]);
        assert!((&mut m).view().find_exact(&p(0x0a010000, 16)).is_none());
        assert!((&mut m).view().find_exact(&p(0x0a000000, 8)).is_some());
    }

    #[test]
    fn view_mut_find_exact_value() {
        let mut m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 24, 4)]);
        assert_eq!((&mut m).view().find_exact_value(&p(0x0a010000, 16)), None);
        let got = (&mut m)
            .view()
            .find_exact_value(&p(0x0a010000, 24))
            .map(|(p, v)| {
                *v += 10;
                (p, *v)
            });
        assert_eq!(got, Some((p(0x0a010000, 24), 14)));
        assert_eq!(m.get(&p(0x0a010000, 24)), Some(&14));
    }

    #[test]
    fn view_mut_find_lpm_value() {
        let mut m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 3)]);
        let got = (&mut m)
            .view()
            .find_lpm_value(&p(0x0a010180, 25))
            .map(|(p, v)| {
                *v += 10;
                (p, *v)
            });
        assert_eq!(got, Some((p(0x0a010100, 24), 13)));
        assert_eq!(m.get(&p(0x0a010100, 24)), Some(&13));
    }

    #[test]
    fn view_mut_prefix_value_keys_values() {
        let mut m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let got = (&mut m)
            .view()
            .find_exact(&p(0x0a010000, 16))
            .unwrap()
            .prefix_value()
            .map(|(p, v)| {
                *v += 10;
                (p, *v)
            });
        assert_eq!(got, Some((p(0x0a010000, 16), 12)));
        assert_eq!(m.get(&p(0x0a010000, 16)), Some(&12));
        assert_eq!(
            m.view().keys().collect::<Vec<_>>(),
            vec![p(0x0a000000, 8), p(0x0a010000, 16)]
        );
        assert_eq!(m.view().values().copied().collect::<Vec<_>>(), vec![1, 12]);
    }

    #[test]
    fn view_mut_prefix_reconstruction() {
        let mut m = map_from(&[(0x0a010203, 32, 99)]);
        let v = (&mut m).view().find_exact(&p(0x0a010203, 32)).unwrap();
        assert_eq!(v.prefix(), p(0x0a010203, 32));
        assert_eq!(v.value(), Some(&mut 99));
    }

    #[test]
    fn view_mut_into_iter() {
        let mut m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        // TrieRef: for loop via IntoIterator
        let from_for: Vec<(P, i32)> = (&mut m).view().into_iter().map(|(p, v)| (p, *v)).collect();
        let expected: Vec<(P, i32)> = m.iter().map(|(p, v)| (p, *v)).collect();
        assert_eq!(from_for, expected);
    }
}
