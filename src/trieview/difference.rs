//! Difference set-operation view: L minus R.
//!
//! [`DifferenceView`] yields every prefix present in the left view but **not** in the right.
//!
//! `right` is `Option<R>` internally:
//! - `None`: no right-side filter; all of left's entries are in the difference.
//! - `Some`: right is at the same depth as left (maintained by `get_child`).
//!
//! At the same depth:
//! - `data_bitmap  = left & !right`: entries in left but not right
//! - `child_bitmap = left`: must visit all left children; some subtrees may be fully absent from
//!   right
//! - `get_data     = left.get_data(bit)`: `T = L::T`, same type as left
//! - `get_child`   = descend both; if right lacks the child, pass None for right
//!
//! If right starts deeper than left (e.g. user-supplied view_at), it is carried
//! along until left's traversal descends to right's depth, at which point they align.

use std::marker::PhantomData;

use crate::AsView;
use crate::{node::child_bit as node_child_bit, prefix::mask_from_prefix_len, Prefix};

use super::iter::ViewIter;
use super::TrieView;

/// An immutable view over the difference of two [`TrieView`]s.
///
/// Returned by [`TrieView::difference`]. Iterates over every prefix present
/// in the left view but **not** in the right view, yielding values from the left side.
///
/// The right side is `Option<R>` internally: once the traversal enters a subtree
/// that the right view does not cover, the right side becomes `None` and all
/// remaining left entries in that subtree are yielded unconditionally.
#[derive(Clone)]
pub struct DifferenceView<'a, L, R> {
    left: L,
    right: Option<R>,
    _phantom: PhantomData<&'a ()>,
}

impl<'a, L, R> DifferenceView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    /// Construct a `DifferenceView`, aligning the right side to the left's position.
    ///
    /// - If right is shallower, it is navigated toward left's position.  If the path
    ///   diverges or a required child is absent, `right` becomes `None` (all left
    ///   entries are kept for that subtree).
    /// - If right is deeper, it is stored as-is and will be aligned during traversal
    ///   as `get_child` descends toward right's depth.
    pub(crate) fn new(left: L, right: R) -> Self {
        let right = align_right(&left, right);
        Self {
            left,
            right,
            _phantom: PhantomData,
        }
    }
}

/// Navigate `right` to match `left`'s position as closely as possible.
///
/// Returns `None` if keys diverge (the right subtrie has no overlap with left).
fn align_right<'a, L, R>(left: &L, right: R) -> Option<R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    // Check key agreement at the shallower prefix_len.
    let min_prefix_len = left.prefix_len().min(right.prefix_len());
    let mask = mask_from_prefix_len(min_prefix_len as u8);
    if left.key() & mask != right.key() & mask {
        return None; // diverging keys -> R has no overlap with L's subtrie
    }

    match right.depth().cmp(&left.depth()) {
        std::cmp::Ordering::Less => {
            // R is shallower: navigate toward L's depth/key.
            right.navigate_to(left.key(), left.prefix_len())
        }
        std::cmp::Ordering::Equal => {
            // Same depth
            Some(right)
        }
        std::cmp::Ordering::Greater => {
            // R is deeper: keep as-is; handled during traversal via get_child.
            Some(right)
        }
    }
}

impl<'a, L, R> TrieView<'a> for DifferenceView<'a, L, R>
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

    #[inline]
    fn data_bitmap(&self) -> u32 {
        match &self.right {
            None => self.left.data_bitmap(),
            Some(r) => {
                if r.depth() == self.left.depth() {
                    // Right is at the same level -> mask out entries present in right.
                    self.left.data_bitmap() & !r.data_bitmap()
                } else {
                    // Right is deeper -> it doesn't have data at left's current depth.
                    self.left.data_bitmap()
                }
            }
        }
    }

    #[inline]
    fn child_bitmap(&self) -> u32 {
        // Always use left's child bitmap: we must visit every left child because
        // some subtrees may be absent from right, making all their entries eligible.
        self.left.child_bitmap()
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
                    // Both at the same depth; descend both together.
                    if (r.child_bitmap() >> child_bit) & 1 == 1 {
                        Some(r.get_child(child_bit))
                    } else {
                        None // right has no child here -> all left entries kept
                    }
                } else {
                    // Right is deeper (right.depth > left.depth).
                    // Only carry right along if this child leads toward right's subtrie.
                    let toward_r = node_child_bit(self.left.depth(), r.key());
                    if child_bit == toward_r {
                        Some(self.right.take().unwrap())
                    } else {
                        None
                    }
                }
            }
        };
        DifferenceView {
            left: l_child,
            right: r_child,
            _phantom: PhantomData,
        }
    }

    unsafe fn reposition(&mut self, key: <L::P as Prefix>::R, prefix_len: u32) {
        self.left.reposition(key, prefix_len);
        // right does not need repositioning. It is anyways just used as a filter.
    }
}

impl<'a, L, R> IntoIterator for DifferenceView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    type Item = (L::P, L::T);
    type IntoIter = ViewIter<'a, DifferenceView<'a, L, R>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, L, R> AsView<'a> for DifferenceView<'a, L, R>
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

    fn collect_diff<'a>(iter: impl Iterator<Item = (P, &'a i32)>) -> Vec<(P, i32)> {
        iter.map(|(p, v)| (p, *v)).collect()
    }

    // -- Same-depth cases ------------------------------------------------------

    #[test]
    fn diff_basic() {
        // a \ b removes only shared prefixes; unshared left entries are kept.
        let a = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a020000, 16, 3),
            (0x0b000000, 8, 4),
        ]);
        let b = map_from(&[
            (0x0a000000, 8, 10),  // shared with a -> removed from result
            (0x0a020000, 16, 30), // shared with a -> removed from result
            (0x0c000000, 8, 99),  // not in a -> irrelevant
        ]);
        let got = collect_diff(a.view().difference(b.view()).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x0a010000, 16), 2), // kept: not in b
                (p(0x0b000000, 8), 4),  // kept: not in b
            ]
        );
    }

    #[test]
    fn diff_no_overlap() {
        // b has completely different prefixes -> all of a is kept.
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0b000000, 8, 10), (0x0c000000, 8, 20)]);
        let got = collect_diff(a.view().difference(b.view()).into_iter());
        assert_eq!(got, vec![(p(0x0a000000, 8), 1), (p(0x0a010000, 16), 2),]);
    }

    #[test]
    fn diff_b_superset() {
        // b contains every prefix in a -> result is empty.
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 20),
            (0x0b000000, 8, 99),
        ]);
        let got = collect_diff(a.view().difference(b.view()).into_iter());
        assert!(got.is_empty());
    }

    #[test]
    fn diff_b_empty() {
        // Empty b -> all of a is returned.
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b: PrefixMap<P, i32> = PrefixMap::new();
        let got = collect_diff(a.view().difference(b.view()).into_iter());
        assert_eq!(got, vec![(p(0x0a000000, 8), 1), (p(0x0a010000, 16), 2),]);
    }

    #[test]
    fn diff_a_empty() {
        let a: PrefixMap<P, i32> = PrefixMap::new();
        let b = map_from(&[(0x0a000000, 8, 10)]);
        assert!(a.view().difference(b.view()).into_iter().next().is_none());
    }

    /// Large same-depth test covering multiple subtries and levels.
    #[test]
    fn diff_large_same_depth() {
        let a = map_from(&[
            (0x01000000, 8, 1),
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 11),
            (0x0a010100, 24, 12),
            (0x0a020000, 16, 13),
            (0x0b000000, 8, 20),
            (0x0b010000, 16, 21),
            (0x64000000, 8, 100),
            (0xc0a80000, 16, 200),
        ]);
        let b = map_from(&[
            (0x0a000000, 8, 99),  // removes 10/8
            (0x0a010100, 24, 99), // removes 10.1.1/24
            (0x0b000000, 8, 99),  // removes 11/8
            (0x64000000, 8, 99),  // removes 100/8
            (0xc0a80100, 24, 99), // not in a -> no effect
        ]);
        let got = collect_diff(a.view().difference(b.view()).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x01000000, 8), 1),    // kept: not in b
                (p(0x0a010000, 16), 11),  // kept: 10.1/16 is not in b (only /24 is)
                (p(0x0a020000, 16), 13),  // kept: not in b
                (p(0x0b010000, 16), 21),  // kept: 11.1/16 not in b (only /8 is)
                (p(0xc0a80000, 16), 200), // kept: 192.168/16 not in b
            ]
        );
    }

    // -- find / find_lpm --------------------------------------------------------

    #[test]
    fn diff_find_then_iter() {
        let a = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a010100, 24, 3),
            (0x0b000000, 8, 4),
        ]);
        let b = map_from(&[
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 20), // removes 10.1/16 from difference
        ]);
        // diff: {10.1.1/24, 11/8}; find 10.1/16 subtrie in diff -> only 10.1.1/24
        let got = collect_diff(
            a.view()
                .difference(b.view())
                .find(&p(0x0a010000, 16))
                .unwrap()
                .into_iter(),
        );
        assert_eq!(got, vec![(p(0x0a010100, 24), 3)]);
    }

    #[test]
    fn diff_mut_find_lpm_value_does_not_require_clone() {
        let mut a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 3)]);
        let b = map_from(&[(0x0a010100, 24, 30)]);

        let got = (&mut a)
            .view()
            .difference(b.view())
            .find_lpm_value(&p(0x0a010180, 25))
            .map(|(prefix, value)| {
                *value += 10;
                (prefix, *value)
            });

        assert_eq!(got, Some((p(0x0a010000, 16), 12)));
        assert_eq!(a.get(&p(0x0a010000, 16)), Some(&12));
    }

    // -- Depth-difference cases ------------------------------------------------
    //
    // With K=5, `view_at(&p(addr, len))` lands at depth = floor(len/K)*K.
    //   len=8  -> depth 5    len=16 -> depth 15

    /// Right is shallower: right is navigated to left's depth at construction.
    /// Entries in left's subtrie that are also in right's navigated position are removed.
    #[test]
    fn diff_right_shallower_navigated_to_left() {
        // a_sub = 10.x subtrie (depth 5); b_root = root (depth 0).
        // align_right navigates b_root to depth 5 via the 10.x child.
        // At depth 5, b has {10/8, 10.1/16}; a has {10/8, 10.1/16, 10.2/16}.
        // Difference: {10.2/16}.
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a020000, 16, 3)]);
        let b = map_from(&[
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 20),
            (0x0b000000, 8, 30), // irrelevant -> outside a_sub
        ]);
        let a_sub = a.view_at(&p(0x0a000000, 8)).unwrap(); // depth 5
        let b_root = b.view(); // depth 0

        let got = collect_diff(a_sub.difference(b_root).into_iter());
        assert_eq!(got, vec![(p(0x0a020000, 16), 3)]);
    }

    /// Right navigated to left, but right diverges (no path to left's key).
    /// align_right returns None -> all left entries are kept.
    #[test]
    fn diff_right_shallower_diverges() {
        // a_sub = 10.x subtrie (depth 5); b has no entries in 10.x at all.
        // Right navigates toward 10.x but finds no child -> right = None -> all kept.
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[
            (0x0b000000, 8, 10), // 11.x -> completely different subtrie
            (0x0c000000, 8, 20),
        ]);
        let a_sub = a.view_at(&p(0x0a000000, 8)).unwrap(); // depth 5
        let b_root = b.view(); // depth 0

        let got = collect_diff(a_sub.difference(b_root).into_iter());
        // No path from b_root to 10.x -> right = None -> all of a_sub kept
        assert_eq!(got, vec![(p(0x0a000000, 8), 1), (p(0x0a010000, 16), 2),]);
    }

    /// Left is shallower than right (right is positioned deeper in the trie).
    /// Left leads; right is carried toward its depth via get_child.
    /// Left's entries in subtries NOT leading toward right are kept unconditionally.
    #[test]
    fn diff_left_shallower_right_deeper() {
        // a_root (depth 0) minus b_sub at 10.x (depth 5).
        // a has: 9/8, 10/8, 10.1/16, 11/8.
        // b_sub covers: 10/8, 10.1/16, 10.2/16 (within 10.x).
        //
        // Expected difference:
        //   9/8  -> kept (not in b_sub's subtrie)
        //   10/8 -> removed (b_sub has it)
        //   10.1/16 -> removed
        //   11/8 -> kept (not in b_sub's subtrie)
        let a = map_from(&[
            (0x09000000, 8, 1),
            (0x0a000000, 8, 2),
            (0x0a010000, 16, 3),
            (0x0b000000, 8, 4),
        ]);
        let b = map_from(&[
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 20),
            (0x0a020000, 16, 30),
        ]);
        let a_root = a.view();
        let b_sub = b.view_at(&p(0x0a000000, 8)).unwrap(); // depth 5

        let got = collect_diff(a_root.difference(b_sub).into_iter());
        assert_eq!(
            got,
            vec![
                (p(0x09000000, 8), 1), // kept: 9/8 not toward b_sub
                (p(0x0b000000, 8), 4), // kept: 11/8 not toward b_sub
            ]
        );
    }

    /// Left has entries in many subtries; right (deeper) only covers one of them.
    /// Entries in subtries NOT leading toward right are kept entirely.
    #[test]
    fn diff_left_multiple_subtries_right_covers_one() {
        let a = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0b000000, 8, 3),
            (0x0b010000, 16, 4),
            (0x0c000000, 8, 5),
        ]);
        let b = map_from(&[
            (0x0a000000, 8, 10),  // covers 10/8
            (0x0a010000, 16, 20), // covers 10.1/16
        ]);
        let a_root = a.view();
        let b_sub = b.view_at(&p(0x0a000000, 8)).unwrap(); // depth 5

        let got = collect_diff(a_root.difference(b_sub).into_iter());
        assert_eq!(
            got,
            vec![
                // 10.x entries: 10/8 and 10.1/16 both in b_sub -> removed
                (p(0x0b000000, 8), 3), // not toward b_sub -> kept entirely
                (p(0x0b010000, 16), 4),
                (p(0x0c000000, 8), 5),
            ]
        );
    }

    // -- Composition -----------------------------------------------------------

    #[test]
    fn diff_composed_with_intersection() {
        // (a \ b) ∩ c -> DifferenceView implements TrieView so it composes.
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0b000000, 8, 3)]);
        let b = map_from(&[(0x0a000000, 8, 99)]); // removes 10/8 from a
        let c = map_from(&[(0x0a010000, 16, 100), (0x0b000000, 8, 200)]);
        // a \ b = {10.1/16, 11/8}; ∩ c = {10.1/16, 11/8} (both in c)
        let got: Vec<_> = a
            .view()
            .difference(b.view())
            .intersection(c.view())
            .unwrap()
            .into_iter()
            .map(|(p, (l, r))| (p, *l, *r))
            .collect();
        assert_eq!(
            got,
            vec![(p(0x0a010000, 16), 2, 100), (p(0x0b000000, 8), 3, 200),]
        );
    }

    #[test]
    fn diff_composed_difference_of_differences() {
        // (a \ b) \ c
        let a = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0b000000, 8, 3),
            (0x0c000000, 8, 4),
        ]);
        let b = map_from(&[(0x0a000000, 8, 99)]); // removes 10/8
        let c = map_from(&[(0x0b000000, 8, 99)]); // removes 11/8

        // a \ b = {10.1/16, 11/8, 12/8}; \ c = {10.1/16, 12/8}
        let got = collect_diff(
            a.view()
                .difference(b.view())
                .difference(c.view())
                .into_iter(),
        );
        assert_eq!(got, vec![(p(0x0a010000, 16), 2), (p(0x0c000000, 8), 4),]);
    }

    #[test]
    fn view_into_right_child() {
        let a = map_from(&[(0x00000000, 0, 0), (0x00000000, 1, 1), (0x00000000, 2, 2)]);
        let b = map_from(&[(0x00000000, 0, 0), (0x00000000, 2, 2)]);
        let b_view = b.view_at(&p(0x00000000, 1)).unwrap();
        let got = a.view().difference(b_view).iter().collect::<Vec<_>>();
        let want = vec![(p(0x00000000, 0), &0), (p(0x00000000, 1), &1)];
        assert_eq!(got, want);
    }

    #[test]
    fn view_into_left_child() {
        let a = map_from(&[(0x00000000, 0, 0), (0x00000000, 1, 1), (0x00000000, 2, 2)]);
        let b = map_from(&[(0x00000000, 0, 0), (0x00000000, 2, 2)]);
        let a_view = a.view_at(&p(0x00000000, 1)).unwrap();
        let got = a_view.difference(b.view()).iter().collect::<Vec<_>>();
        let want = vec![(p(0x00000000, 1), &1)];
        assert_eq!(got, want);
    }

    #[test]
    fn view_into_right_child_deep() {
        let a = map_from(&[(0x00000000, 0, 0), (0x00000000, 5, 5), (0x00000000, 6, 6)]);
        let b = map_from(&[(0x00000000, 0, 0), (0x00000000, 6, 6)]);
        let b_view = b.view_at(&p(0x00000000, 5)).unwrap();
        let got = a.view().difference(b_view).iter().collect::<Vec<_>>();
        let want = vec![(p(0x00000000, 0), &0), (p(0x00000000, 5), &5)];
        assert_eq!(got, want);
    }

    #[test]
    fn view_into_left_child_deep() {
        let a = map_from(&[(0x00000000, 0, 0), (0x00000000, 5, 5), (0x00000000, 6, 6)]);
        let b = map_from(&[(0x00000000, 0, 0), (0x00000000, 6, 6)]);
        let a_view = a.view_at(&p(0x00000000, 5)).unwrap();
        let got = a_view.difference(b.view()).iter().collect::<Vec<_>>();
        let want = vec![(p(0x00000000, 5), &5)];
        assert_eq!(got, want);
    }

    // -- iter_from on difference views ------------------------------------------

    #[test]
    fn diff_iter_from_inclusive() {
        let a = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a020000, 16, 3),
            (0x0a030000, 16, 4),
        ]);
        let b = map_from(&[(0x0a010000, 16, 20)]);

        // diff: 10/8, 10.2/16, 10.3/16
        let from = collect_diff(
            a.view()
                .difference(b.view())
                .iter_from(&p(0x0a020000, 16), true),
        );
        assert_eq!(from, vec![(p(0x0a020000, 16), 3), (p(0x0a030000, 16), 4)]);
    }

    #[test]
    fn diff_iter_from_exclusive() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a020000, 16, 3)]);
        let b = map_from(&[(0x0a010000, 16, 20)]);

        // diff: 10/8, 10.2/16
        let from = collect_diff(
            a.view()
                .difference(b.view())
                .iter_from(&p(0x0a000000, 8), false),
        );
        assert_eq!(from, vec![(p(0x0a020000, 16), 3)]);
    }

    #[test]
    fn diff_iter_from_subview() {
        let a = map_from(&[
            (0x0a000000, 8, 1), // excluded by sub-view
            (0x0a020000, 16, 2),
            (0x0a030000, 16, 3),
            (0x0b000000, 8, 4), // excluded by sub-view
        ]);
        let b = map_from(&[(0x0a020000, 16, 20)]);

        // Sub-view at 10.2.0.0/15 covers 10.2–10.3, excludes 10/8, 11/8
        // a sub-view entries: 10.2/16, 10.3/16
        // diff removes 10.2/16 → only 10.3/16 remains
        let diff = a.view_at(&p(0x0a020000, 15)).unwrap().difference(b.view());
        let all = collect_diff(diff.clone().iter());
        assert_eq!(all, vec![(p(0x0a030000, 16), 3)]);

        // iter_from inclusive at 10.3/16 → same single result
        let from = collect_diff(diff.iter_from(&p(0x0a030000, 16), true));
        assert_eq!(from, vec![(p(0x0a030000, 16), 3)]);
    }
}
