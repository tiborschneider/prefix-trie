//! Covering-difference set-operation view: L minus entries covered by R.
//!
//! [`CoveringDifferenceView`] yields every prefix present in the left view for which there
//! is no *covering* prefix in the right view. A prefix `P_r` in R covers `P_l` in L iff
//! `P_r.len ≤ P_l.len` and `P_r` matches the leading bits of `P_l` (i.e. `P_r` is an
//! ancestor of, or exactly equal to, `P_l`).
//!
//! ## Intra-node coverage
//!
//! For each set bit `r_b` in R's data bitmap, `data_cover_mask_for_bit` and
//! `child_cover_mask_for_bit` give the data and child slots it covers within the node.
//! The unions of these masks are precomputed once (in `new` / `get_child`) into `cov_data`
//! and `cov_child`, making `data_bitmap` / `child_bitmap` O(1) bitwise operations.
//!
//! ## Depth handling
//!
//! - **Right shallower**: navigated step-by-step toward left's depth, checking at each
//!   intermediate node whether R has an ancestor (via `data_lpm_mask`) that covers all
//!   of L's subtrie. If found the entire subtrie is marked as covered.
//! - **Right same depth**: coverage precomputed at construction / `get_child`.
//! - **Right deeper**: carried along until left's traversal reaches right's depth.

use std::marker::PhantomData;

use crate::{
    prefix::mask_from_prefix_len,
    Prefix,
    {
        node::{
            child_bit as node_child_bit, child_cover_mask_for_bit, data_cover_mask_for_bit,
            data_lpm_mask,
        },
        AsView,
    },
};

use super::{iter::ViewIter, TrieView};

/// An immutable view over the covering difference of two [`TrieView`]s.
///
/// Returned by [`TrieView::covering_difference`]. Iterates over every prefix `P_l`
/// in the left view for which there is no prefix `P_r` in the right view satisfying
/// `P_r.len ≤ P_l.len` and `P_r` matching `P_l`'s leading bits.
///
/// Coverage is encoded directly in `cov_data` / `cov_child`: **a set bit means that L
/// slot is covered by R and must not be yielded**. `data_bitmap` and `child_bitmap` are
/// computed as `left_bitmap & !cov_bitmap`. The special case where an ancestor R covers
/// the entire subtrie is represented by `cov_data = 0x7FFFFFFF, cov_child = 0xFFFFFFFF`
/// (all 31 data bits and all 32 child bits), which drives both bitmaps to zero.
#[derive(Clone)]
pub struct CoveringDifferenceView<'a, L, R> {
    left: L,
    right: Option<R>,
    /// Mask of data bits covered by R. **A set bit is excluded from `data_bitmap`.**
    /// `0` means nothing is covered (all left data bits may be yielded).
    /// `0x7FFFFFFF` means the entire subtrie is covered (nothing yielded).
    cov_data: u32,
    /// Mask of child bits covered by R. **A set bit is excluded from `child_bitmap`.**
    /// `0` means nothing is covered; `0xFFFFFFFF` means all children are covered.
    cov_child: u32,
    _phantom: PhantomData<&'a ()>,
}

impl<'a, L, R> CoveringDifferenceView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    pub(crate) fn new(left: L, right: R) -> Self {
        let (right, covered) = align_right(&left, right);
        let (cov_data, cov_child) = r_coverage_masks(&left, right.as_ref(), covered);
        Self {
            left,
            right,
            cov_data,
            cov_child,
            _phantom: PhantomData,
        }
    }
}

/// Align right toward left's position, checking for covering ancestors along the way.
///
/// Returns `(Some(r), false)` when aligned without finding a covering ancestor,
/// `(None, false)` when right has no path to left's subtrie, and `(None, true)` when
/// a covering ancestor in right was found (the entire L subtrie must be excluded).
fn align_right<'a, L, R>(left: &L, mut right: R) -> (Option<R>, bool)
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    let min_prefix_len = left.prefix_len().min(right.prefix_len());
    let mask = mask_from_prefix_len(min_prefix_len as u8);
    if left.key() & mask != right.key() & mask {
        return (None, false); // diverging keys -> no overlap
    }

    match right.depth().cmp(&left.depth()) {
        std::cmp::Ordering::Greater => (Some(right), false),
        std::cmp::Ordering::Equal => (Some(right), false),
        std::cmp::Ordering::Less => {
            // Navigate right toward left one K-level at a time, checking at each node
            // whether R has an ancestor that covers all of L's subtrie.
            loop {
                // data_lpm_mask gives data bits in this node that are ancestors of
                // (left.key(), left.depth). If any are set in R, L's subtrie is covered.
                let lpm = data_lpm_mask(right.depth(), left.key(), left.depth());
                if right.data_bitmap() & lpm != 0 {
                    return (None, true);
                }
                if right.depth() == left.depth() {
                    return (Some(right), false);
                }
                let cb = node_child_bit(right.depth(), left.key());
                if (right.child_bitmap() >> cb) & 1 == 0 {
                    return (None, false);
                }
                // SAFETY: we are replacing right with that child; won't call get_child on the old
                // right ever again (and didn't do so yet)
                right = unsafe { right.get_child(cb) };
            }
        }
    }
}

/// Compute the coverage masks from R's data bitmap.
///
/// **A set bit in the returned masks means that the corresponding L data/child slot is
/// covered by R and must be excluded from iteration.**
///
/// - If `covered` is `true` (an R ancestor covers the entire subtrie), returns
///   `(0x7FFFFFFF, 0xFFFFFFFF)` -> all 31 data bits and all 32 child bits set, so that
///   `left_bitmap & !cov` drives both effective bitmaps to zero.
/// - If `right` is `None` or at a greater depth than `left` (no intra-node coverage
///   applies yet), returns `(0, 0)` -> nothing is covered, all left entries are kept.
/// - Otherwise iterates each set bit in `right.data_bitmap()` and ORs in the data and
///   child slots it covers via [`data_cover_mask_for_bit`] / [`child_cover_mask_for_bit`].
fn r_coverage_masks<'a, L, R>(left: &L, right: Option<&R>, covered: bool) -> (u32, u32)
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    if covered {
        return (0x7FFF_FFFF, 0xFFFF_FFFF);
    }
    let Some(r) = right else { return (0, 0) };
    if r.depth() != left.depth() {
        return (0, 0);
    }
    let mut cov_data = 0u32;
    let mut cov_child = 0u32;
    let mut bits = r.data_bitmap();
    while bits != 0 {
        let r_b = bits.trailing_zeros();
        bits &= bits - 1;
        cov_data |= data_cover_mask_for_bit(r_b);
        cov_child |= child_cover_mask_for_bit(r_b);
    }
    (cov_data, cov_child)
}

impl<'a, L, R> TrieView<'a> for CoveringDifferenceView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    type P = L::P;
    type T = L::T;

    #[inline]
    fn depth(&self) -> u32 {
        self.left.depth()
    }

    #[inline]
    fn key(&self) -> <L::P as Prefix>::R {
        self.left.key()
    }

    #[inline]
    fn prefix_len(&self) -> u32 {
        self.left.prefix_len()
    }

    /// Effective data bitmap: left's bitmap minus any bits covered by R.
    ///
    /// When the entire subtrie is covered (`cov_data = 0x7FFFFFFF`), this returns 0
    /// because `left.data_bitmap()` only uses bits 0-30 and `!0x7FFFFFFF = 0x80000000`.
    #[inline]
    fn data_bitmap(&self) -> u32 {
        self.left.data_bitmap() & !self.cov_data
    }

    /// Effective child bitmap: left's bitmap minus any children fully covered by R.
    ///
    /// When the entire subtrie is covered (`cov_child = 0xFFFFFFFF`), this returns 0.
    #[inline]
    fn child_bitmap(&self) -> u32 {
        self.left.child_bitmap() & !self.cov_child
    }

    #[inline]
    unsafe fn get_data(&mut self, data_bit: u32) -> L::T {
        self.left.get_data(data_bit)
    }

    unsafe fn get_child(&mut self, child_bit: u32) -> Self {
        let l_child = self.left.get_child(child_bit);
        let r_child = match &mut self.right {
            None => None,
            Some(r) => {
                if r.depth() == self.left.depth() {
                    if (r.child_bitmap() >> child_bit) & 1 == 1 {
                        Some(r.get_child(child_bit))
                    } else {
                        None
                    }
                } else {
                    // R is deeper -> carry it along only if this child leads toward R.
                    let toward_r = node_child_bit(self.left.depth(), r.key());
                    if child_bit == toward_r {
                        Some(self.right.take().unwrap())
                    } else {
                        None
                    }
                }
            }
        };
        let (cov_data, cov_child) = r_coverage_masks(&l_child, r_child.as_ref(), false);
        CoveringDifferenceView {
            left: l_child,
            right: r_child,
            cov_data,
            cov_child,
            _phantom: PhantomData,
        }
    }

    unsafe fn reposition(&mut self, key: <L::P as Prefix>::R, prefix_len: u32) {
        let left_depth = self.left.depth();
        unsafe {
            self.left.reposition(key, prefix_len);
            if let Some(r) = self.right.as_mut() {
                if r.depth() == left_depth {
                    r.reposition(key, prefix_len)
                }
            }
        }
    }
}

impl<'a, L, R> IntoIterator for CoveringDifferenceView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    type Item = (L::P, L::T);
    type IntoIter = ViewIter<'a, CoveringDifferenceView<'a, L, R>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, L, R> AsView<'a> for CoveringDifferenceView<'a, L, R>
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

    fn collect<'a>(iter: impl Iterator<Item = (P, &'a i32)>) -> Vec<(P, i32)> {
        iter.map(|(p, v)| (p, *v)).collect()
    }

    // -- Same-depth tests ------------------------------------------------------

    /// Basic: R has a shorter prefix that covers some L entries.
    ///
    /// A = {/22=1, /24=2, /23_2=3}, B = {/23}
    ///   - /24 is covered by /23 in B -> excluded
    ///   - /22 is shorter than /23 -> kept
    ///   - /23_2 (different subtrie) -> kept
    #[test]
    fn covering_diff_basic() {
        let a = map_from(&[
            (0x0a000000, 22, 1), // 10.0.0.0/22
            (0x0a000000, 24, 2), // 10.0.0.0/24 -> covered by /23
            (0x0a000200, 23, 3), // 10.0.2.0/23 -> different /23, not covered
        ]);
        let b = map_from(&[(0x0a000000, 23, 99)]); // 10.0.0.0/23
        let got = collect(a.view().covering_difference(b.view()).into_iter());
        assert_eq!(got, vec![(p(0x0a000000, 22), 1), (p(0x0a000200, 23), 3),]);
    }

    /// R has no overlap with L -> all L entries kept.
    #[test]
    fn covering_diff_no_overlap() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0b000000, 8, 99)]);
        let got = collect(a.view().covering_difference(b.view()).into_iter());
        assert_eq!(got, vec![(p(0x0a000000, 8), 1), (p(0x0a010000, 16), 2),]);
    }

    /// R has exact same prefix as an L entry -> excluded (same = covered).
    #[test]
    fn covering_diff_exact_match_excluded() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a020000, 16, 3)]);
        let b = map_from(&[(0x0a010000, 16, 99)]);
        let got = collect(a.view().covering_difference(b.view()).into_iter());
        assert_eq!(got, vec![(p(0x0a000000, 8), 1), (p(0x0a020000, 16), 3),]);
    }

    /// R's covering prefix covers all L entries in the overlapping subtrie.
    #[test]
    fn covering_diff_r_covers_everything() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a000000, 8, 99)]);
        assert!(a
            .view()
            .covering_difference(b.view())
            .into_iter()
            .next()
            .is_none());
    }

    /// R is empty -> all L entries kept.
    #[test]
    fn covering_diff_r_empty() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b: PrefixMap<P, i32> = PrefixMap::new();
        let got = collect(a.view().covering_difference(b.view()).into_iter());
        assert_eq!(got, vec![(p(0x0a000000, 8), 1), (p(0x0a010000, 16), 2),]);
    }

    /// L is empty -> result is empty.
    #[test]
    fn covering_diff_l_empty() {
        let a: PrefixMap<P, i32> = PrefixMap::new();
        let b = map_from(&[(0x0a000000, 8, 99)]);
        assert!(a
            .view()
            .covering_difference(b.view())
            .into_iter()
            .next()
            .is_none());
    }

    /// R covers part of L's entries via a shorter prefix; deeper entries are excluded.
    #[test]
    fn covering_diff_partial_coverage() {
        let a = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a010100, 24, 3), // covered by 10.1/16 in b
            (0x0a020000, 16, 4),
            (0x0b000000, 8, 5),
        ]);
        let b = map_from(&[(0x0a010000, 16, 99)]);
        let got = collect(a.view().covering_difference(b.view()).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x0a000000, 8), 1),
                // 10.1/16 excluded (exact match)
                // 10.1.1/24 excluded (covered by 10.1/16)
                (p(0x0a020000, 16), 4),
                (p(0x0b000000, 8), 5),
            ]
        );
    }

    /// Large same-depth test with multiple subtries.
    #[test]
    fn covering_diff_large_same_depth() {
        let a = map_from(&[
            (0x01000000, 8, 1),
            (0x0a000000, 8, 10),
            (0x0a000000, 16, 11),
            (0x0a010000, 16, 12),
            (0x0a010100, 24, 13),
            (0x0a020000, 16, 14),
            (0x0b000000, 8, 20),
            (0x0b010000, 16, 21),
            (0x64000000, 8, 100),
        ]);
        let b = map_from(&[
            (0x0a000000, 8, 99),  // covers all 10.x entries
            (0x0b010000, 16, 99), // covers 11.1/16
        ]);
        let got = collect(a.view().covering_difference(b.view()).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x01000000, 8), 1),
                // all 10.x entries excluded
                (p(0x0b000000, 8), 20),
                // 11.1/16 excluded
                (p(0x64000000, 8), 100),
            ]
        );
    }

    // -- find / find_lpm --------------------------------------------------------

    #[test]
    fn covering_diff_find_then_iter() {
        let a = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a010100, 24, 3), // covered
            (0x0a020000, 16, 4),
        ]);
        let b = map_from(&[(0x0a010000, 16, 99)]);
        let sub = a
            .view()
            .covering_difference(b.view())
            .find(&p(0x0a000000, 8));
        assert!(sub.is_some());
        let got = collect(sub.unwrap().into_iter());
        assert_eq!(got, vec![(p(0x0a000000, 8), 1), (p(0x0a020000, 16), 4),]);
    }

    #[test]
    fn covering_diff_mut_find_lpm_value_does_not_require_clone() {
        let mut a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 3)]);
        let b = map_from(&[(0x0a010100, 24, 30)]);

        let got = (&mut a)
            .view()
            .covering_difference(b.view())
            .find_lpm_value(&p(0x0a010180, 25))
            .map(|(prefix, value)| {
                *value += 10;
                (prefix, *value)
            });

        assert_eq!(got, Some((p(0x0a010000, 16), 12)));
        assert_eq!(a.get(&p(0x0a010000, 16)), Some(&12));
    }

    // -- Depth-difference cases ------------------------------------------------

    /// Right shallower, has a covering ancestor found during navigation -> all excluded.
    #[test]
    fn covering_diff_right_shallower_covers() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a000000, 8, 99)]);
        let a_sub = a.view_at(&p(0x0a000000, 8)).unwrap();
        let b_root = b.view();
        assert!(a_sub
            .covering_difference(b_root)
            .into_iter()
            .next()
            .is_none());
    }

    /// Right shallower but has no covering prefix along the path -> all kept.
    #[test]
    fn covering_diff_right_shallower_no_cover() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0b000000, 8, 99)]);
        let a_sub = a.view_at(&p(0x0a000000, 8)).unwrap();
        let b_root = b.view();
        let got = collect(a_sub.covering_difference(b_root).into_iter());
        assert_eq!(got, vec![(p(0x0a000000, 8), 1), (p(0x0a010000, 16), 2),]);
    }

    /// Right shallower, navigates to left's depth with partial coverage.
    #[test]
    fn covering_diff_right_shallower_partial() {
        let a = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2), // will be covered
            (0x0a020000, 16, 3),
        ]);
        let b = map_from(&[(0x0a010000, 16, 99), (0x0b000000, 8, 99)]);
        let a_sub = a.view_at(&p(0x0a000000, 8)).unwrap();
        let b_root = b.view();
        let got = collect(a_sub.covering_difference(b_root).into_iter());
        assert_eq!(got, vec![(p(0x0a000000, 8), 1), (p(0x0a020000, 16), 3),]);
    }

    /// Left shallower than right: entries not toward R's subtrie are kept entirely.
    /// R's /16 doesn't cover L's /8 (shorter prefix).
    #[test]
    fn covering_diff_left_shallower_right_deeper() {
        let a = map_from(&[
            (0x09000000, 8, 1),
            (0x0a000000, 8, 2),
            (0x0a010000, 16, 3), // exact match in b_sub -> excluded
            (0x0b000000, 8, 4),
        ]);
        let b = map_from(&[(0x0a010000, 16, 99)]);
        let a_root = a.view();
        let b_sub = b.view_at(&p(0x0a010000, 16)).unwrap();
        let got = collect(a_root.covering_difference(b_sub).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x09000000, 8), 1),
                (p(0x0a000000, 8), 2), // kept: /8 is shorter than b_sub's /16
                // 10.1/16 excluded
                (p(0x0b000000, 8), 4),
            ]
        );
    }

    // -- Composition -----------------------------------------------------------

    #[test]
    fn covering_diff_composed_with_difference() {
        let a = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a010100, 24, 3), // covered
            (0x0b000000, 8, 4),
        ]);
        let b = map_from(&[(0x0a010000, 16, 99)]);
        let c = map_from(&[(0x0a000000, 8, 99)]);

        // covering_diff = {10/8, 11/8}; diff c removes 10/8
        let got = collect(
            a.view()
                .covering_difference(b.view())
                .difference(c.view())
                .into_iter(),
        );
        assert_eq!(got, vec![(p(0x0b000000, 8), 4)]);
    }

    #[test]
    fn covering_diff_composed_with_intersection() {
        let a = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a010100, 24, 3), // covered
            (0x0b000000, 8, 4),
        ]);
        let b = map_from(&[(0x0a010000, 16, 99)]);
        let c = map_from(&[(0x0a000000, 8, 100), (0x0b000000, 8, 200)]);

        // covering_diff = {10/8, 11/8}; ∩ c = {10/8, 11/8}
        let got: Vec<_> = a
            .view()
            .covering_difference(b.view())
            .intersection(c.view())
            .unwrap()
            .into_iter()
            .map(|(p, (l, r))| (p, *l, *r))
            .collect();
        assert_eq!(
            got,
            vec![(p(0x0a000000, 8), 1, 100), (p(0x0b000000, 8), 4, 200),]
        );
    }

    #[test]
    fn covering_diff_into_iter_for_loop() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a010000, 16, 99)]);
        let mut count = 0;
        for _ in a.view().covering_difference(b.view()) {
            count += 1;
        }
        assert_eq!(count, 1); // only 10/8 kept
    }

    #[test]
    fn view_into_right_child() {
        let a = map_from(&[(0x00000000, 0, 0), (0x00000000, 1, 1), (0x00000000, 2, 2)]);
        let b = map_from(&[(0x00000000, 0, 0), (0x00000000, 2, 2)]);
        let b_view = b.view_at(&p(0x00000000, 1)).unwrap();
        let got = a
            .view()
            .covering_difference(b_view)
            .iter()
            .collect::<Vec<_>>();
        let want = vec![(p(0x00000000, 0), &0), (p(0x00000000, 1), &1)];
        assert_eq!(got, want);
    }

    #[test]
    fn view_into_left_child() {
        let a = map_from(&[(0x00000000, 0, 0), (0x00000000, 1, 1), (0x00000000, 2, 2)]);
        let b = map_from(&[(0x00000000, 2, 2)]);
        let a_view = a.view_at(&p(0x00000000, 1)).unwrap();
        let got = a_view
            .covering_difference(b.view())
            .iter()
            .collect::<Vec<_>>();
        let want = vec![(p(0x00000000, 1), &1)];
        assert_eq!(got, want);
    }

    #[test]
    fn view_into_right_child_deep() {
        let a = map_from(&[(0x00000000, 0, 0), (0x00000000, 5, 5), (0x00000000, 6, 6)]);
        let b = map_from(&[(0x00000000, 0, 0), (0x00000000, 6, 6)]);
        let b_view = b.view_at(&p(0x00000000, 5)).unwrap();
        let got = a
            .view()
            .covering_difference(b_view)
            .iter()
            .collect::<Vec<_>>();
        let want = vec![(p(0x00000000, 0), &0), (p(0x00000000, 5), &5)];
        assert_eq!(got, want);
    }

    #[test]
    fn view_into_left_child_deep() {
        let a = map_from(&[(0x00000000, 0, 0), (0x00000000, 5, 5), (0x00000000, 6, 6)]);
        let b = map_from(&[(0x00000000, 6, 6)]);
        let a_view = a.view_at(&p(0x00000000, 5)).unwrap();
        let got = a_view
            .covering_difference(b.view())
            .iter()
            .collect::<Vec<_>>();
        let want = vec![(p(0x00000000, 5), &5)];
        assert_eq!(got, want);
    }
}
