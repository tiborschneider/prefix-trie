//! Covering-union set-operation view.
//!
//! [`CoveringUnionView`] yields every prefix present in either input view, like
//! [`UnionView`]. For prefixes present on only one side, the yielded item
//! also carries the longest prefix match from the opposite view, when one exists inside that
//! opposite input view.

use std::marker::PhantomData;

use crate::{
    prefix::mask_from_prefix_len,
    Prefix,
    {
        node::{child_bit as node_child_bit, data_lpm_mask},
        AsView,
    },
};

use super::{
    reconstruct_prefix,
    union::{UnionItem, UnionView},
    TrieView, ViewIter,
};

/// The item type yielded by iterating a [`CoveringUnionView`].
///
/// Prefixes present in both views yield [`Both`][CoveringUnionItem::Both]. Prefixes present on
/// only one side yield that side's value plus the longest prefix match from the opposite side,
/// if such a prefix exists inside the opposite input view.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoveringUnionItem<P, L, R> {
    /// Present only in the left view.
    Left {
        /// The exact value from the left view.
        left: L,
        /// The longest prefix match from the right view.
        right_lpm: Option<(P, R)>,
    },
    /// Present only in the right view.
    Right {
        /// The longest prefix match from the left view.
        left_lpm: Option<(P, L)>,
        /// The exact value from the right view.
        right: R,
    },
    /// Present in both views at the same prefix.
    Both {
        /// The exact value from the left view.
        left: L,
        /// The exact value from the right view.
        right: R,
    },
}

impl<P, L, R> CoveringUnionItem<P, L, R> {
    /// Get a reference to the left exact element, if present.
    pub fn left(&self) -> Option<&L> {
        match self {
            CoveringUnionItem::Left { left, .. } | CoveringUnionItem::Both { left, .. } => {
                Some(left)
            }
            CoveringUnionItem::Right { .. } => None,
        }
    }

    /// Get a reference to the right exact element, if present.
    pub fn right(&self) -> Option<&R> {
        match self {
            CoveringUnionItem::Right { right, .. } | CoveringUnionItem::Both { right, .. } => {
                Some(right)
            }
            CoveringUnionItem::Left { .. } => None,
        }
    }

    /// Get the left longest prefix match attached to a right-only item.
    pub fn left_lpm(&self) -> Option<(&P, &L)> {
        match self {
            CoveringUnionItem::Right {
                left_lpm: Some((prefix, value)),
                ..
            } => Some((prefix, value)),
            _ => None,
        }
    }

    /// Get the right longest prefix match attached to a left-only item.
    pub fn right_lpm(&self) -> Option<(&P, &R)> {
        match self {
            CoveringUnionItem::Left {
                right_lpm: Some((prefix, value)),
                ..
            } => Some((prefix, value)),
            _ => None,
        }
    }
}

/// An immutable view over the covering union of two [`TrieView`]s.
///
/// Returned by [`TrieView::covering_union`]. The exact union traversal is delegated to
/// [`UnionView`]. In parallel, each side keeps a cloneable LPM cursor for the opposite side. That
/// cursor is advanced as child views are produced, so LPM context is maintained along the traversal
/// path rather than recomputed from the root for every yielded item.
pub struct CoveringUnionView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    exact: UnionView<'a, L, R>,
    left_lpm: LpmState<'a, L>,
    right_lpm: LpmState<'a, R>,
    _phantom: PhantomData<&'a ()>,
}

impl<'a, L, R> Clone for CoveringUnionView<'a, L, R>
where
    L: TrieView<'a> + Clone,
    L::P: Clone,
    L::T: Clone,
    R: TrieView<'a, P = L::P> + Clone,
    R::T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            exact: self.exact.clone(),
            left_lpm: self.left_lpm.clone(),
            right_lpm: self.right_lpm.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<'a, L, R> CoveringUnionView<'a, L, R>
where
    L: TrieView<'a> + Clone,
    R: TrieView<'a, P = L::P> + Clone,
{
    /// Construct a `CoveringUnionView` from two views.
    pub(crate) fn new(left: L, right: R) -> Self {
        Self {
            exact: UnionView::new(left.clone(), right.clone()),
            left_lpm: LpmState::new(left),
            right_lpm: LpmState::new(right),
            _phantom: PhantomData,
        }
    }
}

impl<'a, L, R> TrieView<'a> for CoveringUnionView<'a, L, R>
where
    L: TrieView<'a> + Clone,
    L::P: Clone + 'a,
    L::T: Clone,
    R: TrieView<'a, P = L::P> + Clone,
    R::T: Clone,
{
    type P = L::P;
    type T = CoveringUnionItem<L::P, L::T, R::T>;

    #[inline]
    fn depth(&self) -> u32 {
        self.exact.depth()
    }

    #[inline]
    fn key(&self) -> <L::P as Prefix>::R {
        self.exact.key()
    }

    #[inline]
    fn prefix_len(&self) -> u32 {
        self.exact.prefix_len()
    }

    #[inline]
    fn data_bitmap(&self) -> u32 {
        self.exact.data_bitmap()
    }

    #[inline]
    fn child_bitmap(&self) -> u32 {
        self.exact.child_bitmap()
    }

    #[inline]
    unsafe fn get_data(&mut self, data_bit: u32) -> Self::T {
        let prefix = reconstruct_prefix::<L::P>(self.exact.depth(), self.exact.key(), data_bit);
        match unsafe { self.exact.get_data(data_bit) } {
            UnionItem::Left(left) => CoveringUnionItem::Left {
                left,
                right_lpm: self.right_lpm.lpm_for_prefix(&prefix),
            },
            UnionItem::Right(right) => CoveringUnionItem::Right {
                left_lpm: self.left_lpm.lpm_for_prefix(&prefix),
                right,
            },
            UnionItem::Both(left, right) => CoveringUnionItem::Both { left, right },
        }
    }

    unsafe fn get_child(&mut self, child_bit: u32) -> Self {
        let exact = unsafe { self.exact.get_child(child_bit) };
        let prefix = exact.prefix();
        let mut left_lpm = self.left_lpm.clone();
        let mut right_lpm = self.right_lpm.clone();
        left_lpm.advance_to_prefix(&prefix);
        right_lpm.advance_to_prefix(&prefix);
        Self {
            exact,
            left_lpm,
            right_lpm,
            _phantom: PhantomData,
        }
    }

    unsafe fn reposition(&mut self, key: <L::P as Prefix>::R, prefix_len: u32) {
        unsafe { self.exact.reposition(key, prefix_len) };
        let prefix = self.exact.prefix();
        self.left_lpm.advance_to_prefix(&prefix);
        self.right_lpm.advance_to_prefix(&prefix);
    }
}

impl<'a, L, R> IntoIterator for CoveringUnionView<'a, L, R>
where
    L: TrieView<'a> + Clone,
    L::P: Clone + 'a,
    L::T: Clone,
    R: TrieView<'a, P = L::P> + Clone,
    R::T: Clone,
{
    type Item = (L::P, CoveringUnionItem<L::P, L::T, R::T>);
    type IntoIter = ViewIter<'a, CoveringUnionView<'a, L, R>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, L, R> AsView<'a> for CoveringUnionView<'a, L, R>
where
    L: TrieView<'a> + Clone,
    L::P: Clone + 'a,
    L::T: Clone,
    R: TrieView<'a, P = L::P> + Clone,
    R::T: Clone,
{
    type P = L::P;
    type View = Self;

    fn view(self) -> Self {
        self
    }
}

struct LpmState<'a, V>
where
    V: TrieView<'a>,
{
    lpm_view: Option<V>,
    best: Option<(V::P, V::T)>,
}

impl<'a, V> Clone for LpmState<'a, V>
where
    V: TrieView<'a> + Clone,
    V::P: Clone,
    V::T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            lpm_view: self.lpm_view.clone(),
            best: self.best.clone(),
        }
    }
}

impl<'a, V> LpmState<'a, V>
where
    V: TrieView<'a>,
{
    fn new(view: V) -> Self {
        Self {
            lpm_view: Some(view),
            best: None,
        }
    }
}

impl<'a, V> LpmState<'a, V>
where
    V: TrieView<'a> + Clone,
    V::P: Clone,
    V::T: Clone,
{
    fn advance_to_prefix(&mut self, prefix: &V::P) {
        let target_key = prefix.mask();
        let target_len = prefix.prefix_len() as u32;
        let Some(view) = self.lpm_view.take() else {
            return;
        };
        self.lpm_view = self.advance_view(view, target_key, target_len);
    }

    fn lpm_for_prefix(&self, prefix: &V::P) -> Option<(V::P, V::T)> {
        let target_key = prefix.mask();
        let target_len = prefix.prefix_len() as u32;
        let mut best = self
            .best
            .as_ref()
            .filter(|(best_prefix, _)| best_prefix.contains(prefix))
            .cloned();

        if let Some(view) = self.lpm_view.as_ref() {
            if let Some(candidate) = lpm_in_view(view, target_key, target_len) {
                remember_best(&mut best, candidate);
            }
        }

        best
    }

    fn advance_view(
        &mut self,
        mut view: V,
        target_key: <V::P as Prefix>::R,
        target_len: u32,
    ) -> Option<V> {
        if !same_path::<V::P>(view.key(), view.prefix_len(), target_key, target_len) {
            return None;
        }

        if view.prefix_len() > target_len {
            return Some(view);
        }

        loop {
            if let Some(candidate) = lpm_in_view(&view, target_key, target_len) {
                remember_best(&mut self.best, candidate);
            }

            if target_len < view.depth() + crate::table::K {
                return Some(view);
            }

            let child_bit = node_child_bit(view.depth(), target_key);
            if (view.child_bitmap() >> child_bit) & 1 == 0 {
                return None;
            }

            view = unsafe { view.get_child(child_bit) };
        }
    }
}

fn lpm_in_view<'a, V>(
    view: &V,
    target_key: <V::P as Prefix>::R,
    target_len: u32,
) -> Option<(V::P, V::T)>
where
    V: TrieView<'a> + Clone,
{
    if view.prefix_len() > target_len {
        return None;
    }
    if !same_path::<V::P>(view.key(), view.prefix_len(), target_key, target_len) {
        return None;
    }

    let data_bits = view.data_bitmap() & data_lpm_mask(view.depth(), target_key, target_len);
    if data_bits == 0 {
        return None;
    }

    let data_bit = u32::BITS - 1 - data_bits.leading_zeros();
    let prefix = reconstruct_prefix::<V::P>(view.depth(), view.key(), data_bit);
    let mut cloned = view.clone();
    Some((prefix, unsafe { cloned.get_data(data_bit) }))
}

fn same_path<P: Prefix>(left_key: P::R, left_len: u32, right_key: P::R, right_len: u32) -> bool {
    let prefix_len = left_len.min(right_len);
    let mask = mask_from_prefix_len(prefix_len as u8);
    left_key & mask == right_key & mask
}

fn remember_best<P: Prefix, T>(best: &mut Option<(P, T)>, candidate: (P, T)) {
    if match best.as_ref() {
        None => true,
        Some((prefix, _)) => candidate.0.prefix_len() >= prefix.prefix_len(),
    } {
        *best = Some(candidate);
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

    use super::CoveringUnionItem;

    type P = (u32, u8);

    #[derive(Debug, PartialEq, Eq)]
    enum Got {
        Left(P, i32, Option<(P, i32)>),
        Right(P, Option<(P, i32)>, i32),
        Both(P, i32, i32),
    }

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

    fn collect<'a>(
        iter: impl Iterator<Item = (P, CoveringUnionItem<P, &'a i32, &'a i32>)>,
    ) -> Vec<Got> {
        iter.map(|(prefix, item)| match item {
            CoveringUnionItem::Left { left, right_lpm } => {
                Got::Left(prefix, *left, right_lpm.map(|(p, r)| (p, *r)))
            }
            CoveringUnionItem::Right { left_lpm, right } => {
                Got::Right(prefix, left_lpm.map(|(p, l)| (p, *l)), *right)
            }
            CoveringUnionItem::Both { left, right } => Got::Both(prefix, *left, *right),
        })
        .collect()
    }

    #[test]
    fn covering_union_adds_opposite_lpm_context() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0b000000, 8, 3)]);
        let b = map_from(&[
            (0x0a000000, 8, 10),
            (0x0a010100, 24, 30),
            (0x0c000000, 8, 40),
        ]);

        let got = collect(a.view().covering_union(b.view()).into_iter());
        assert_eq!(
            got,
            vec![
                Got::Both(p(0x0a000000, 8), 1, 10),
                Got::Left(p(0x0a010000, 16), 2, Some((p(0x0a000000, 8), 10))),
                Got::Right(p(0x0a010100, 24), Some((p(0x0a010000, 16), 2)), 30),
                Got::Left(p(0x0b000000, 8), 3, None),
                Got::Right(p(0x0c000000, 8), None, 40),
            ]
        );
    }

    #[test]
    fn covering_union_lpm_context_is_limited_to_input_views() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 3)]);
        let b = map_from(&[(0x0a000000, 8, 10), (0x0a010200, 24, 20)]);
        let a_sub = a.view_at(&p(0x0a010000, 16)).unwrap();
        let b_sub = b.view_at(&p(0x0a010000, 16)).unwrap();

        let got = collect(a_sub.covering_union(b_sub).into_iter());
        assert_eq!(
            got,
            vec![
                Got::Left(p(0x0a010000, 16), 2, None),
                Got::Left(p(0x0a010100, 24), 3, None),
                Got::Right(p(0x0a010200, 24), Some((p(0x0a010000, 16), 2)), 20),
            ]
        );
    }

    #[test]
    fn covering_union_right_deeper_than_left_view() {
        let a = map_from(&[
            (0x09000000, 8, 9),
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a010100, 24, 3),
            (0x0b000000, 8, 11),
        ]);
        let b = map_from(&[(0x0a010000, 16, 20), (0x0a010200, 24, 30)]);
        let b_sub = b.view_at(&p(0x0a010000, 16)).unwrap();

        let got = collect(a.view().covering_union(b_sub).into_iter());
        assert_eq!(
            got,
            vec![
                Got::Left(p(0x09000000, 8), 9, None),
                Got::Left(p(0x0a000000, 8), 1, None),
                Got::Both(p(0x0a010000, 16), 2, 20),
                Got::Left(p(0x0a010100, 24), 3, Some((p(0x0a010000, 16), 20))),
                Got::Right(p(0x0a010200, 24), Some((p(0x0a010000, 16), 2)), 30),
                Got::Left(p(0x0b000000, 8), 11, None),
            ]
        );
    }

    #[test]
    fn covering_union_left_deep_right_shallow_keeps_best_after_child_missing() {
        let a = map_from(&[(0x0a010100, 24, 1), (0x0a010180, 25, 2)]);
        let b = map_from(&[(0x0a000000, 8, 10)]);
        let a_sub = a.view_at(&p(0x0a010100, 24)).unwrap();

        let got = collect(a_sub.covering_union(b.view()).into_iter());
        assert_eq!(
            got,
            vec![
                Got::Right(p(0x0a000000, 8), None, 10),
                Got::Left(p(0x0a010100, 24), 1, Some((p(0x0a000000, 8), 10))),
                Got::Left(p(0x0a010180, 25), 2, Some((p(0x0a000000, 8), 10))),
            ]
        );
    }

    #[test]
    fn covering_union_different_depth_views_prefer_most_specific_lpm() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 3)]);
        let b = map_from(&[
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 20),
            (0x0a010180, 25, 30),
        ]);
        let a_sub = a.view_at(&p(0x0a010000, 16)).unwrap();

        let got = collect(a_sub.covering_union(b.view()).into_iter());
        assert_eq!(
            got,
            vec![
                Got::Right(p(0x0a000000, 8), None, 10),
                Got::Both(p(0x0a010000, 16), 2, 20),
                Got::Left(p(0x0a010100, 24), 3, Some((p(0x0a010000, 16), 20))),
                Got::Right(p(0x0a010180, 25), Some((p(0x0a010100, 24), 3)), 30),
            ]
        );
    }

    #[test]
    fn covering_union_find_lpm_value_on_composed_view() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a010100, 24, 30)]);

        let got = a
            .view()
            .covering_union(b.view())
            .find_lpm_value(&p(0x0a010180, 25))
            .map(|(prefix, item)| match item {
                CoveringUnionItem::Right { left_lpm, right } => {
                    (prefix, left_lpm.map(|(p, l)| (p, *l)), *right)
                }
                other => panic!("expected right-only item, got {other:?}"),
            });

        assert_eq!(
            got,
            Some((p(0x0a010100, 24), Some((p(0x0a010000, 16), 2)), 30))
        );
    }
}
