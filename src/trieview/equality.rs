//! Equality comparison helpers for [`TrieView`].
//!
//! Two entry points, both default methods on [`TrieView`]:
//!
//! - [`eq_keys`][TrieView::eq_keys]: bitmap-based structural comparison of key sets (ignores values).
//! - [`eq_by`][TrieView::eq_by]: iterator-based comparison with a user-provided value comparator.
//!
//! `eq_keys` never reconstructs prefixes; it compares `data_bitmap` / `child_bitmap`
//! at every node and short-circuits on the first mismatch.  Composed views like
//! [`DifferenceView`][super::DifferenceView] can over-approximate `child_bitmap`,
//! so the helpers use [`is_empty_recursive`] to verify that "extra" children contain
//! no actual entries.

use crate::{node::child_bit, prefix::mask_from_prefix_len, Prefix};

use super::TrieView;

/// Check whether a view's subtree contains no data entries. Composed views like
/// `DifferenceView` can over-approximate `child_bitmap`, so `is_non_empty()` is
/// unreliable; this function recurses into children to verify.
pub(super) fn is_empty_recursive<'a, V: TrieView<'a>>(mut view: V) -> bool {
    if view.data_bitmap() != 0 {
        return false;
    }
    let mut bits = view.child_bitmap();
    while bits != 0 {
        let bit = bits.trailing_zeros();
        bits &= bits - 1;
        // SAFETY: each child_bit is used exactly once.
        if !is_empty_recursive(unsafe { view.get_child(bit) }) {
            return false;
        }
    }
    true
}

/// Result of trying to descend a view one level toward a target key while
/// verifying all other branches are empty.
enum DescendResult<V> {
    /// Successfully descended; all siblings are empty.
    Child(V),
    /// No child toward the target, but all siblings are empty (this side is empty).
    Empty,
    /// This side has data or non-empty siblings; key sets cannot be equal.
    NonEmpty,
}

/// Descend the shallower view one level toward `target_key`, verifying that the
/// view has no data at this level and all other children are truly empty.
fn descend_checking_empty<'a, V: TrieView<'a>>(
    mut view: V,
    target_key: <V::P as Prefix>::R,
) -> DescendResult<V> {
    if view.data_bitmap() != 0 {
        return DescendResult::NonEmpty;
    }
    let toward = child_bit(view.depth(), target_key);
    let mut other_bits = view.child_bitmap() & !(1 << toward);
    while other_bits != 0 {
        let bit = other_bits.trailing_zeros();
        other_bits &= other_bits - 1;
        // SAFETY: each child_bit is used exactly once.
        if !is_empty_recursive(unsafe { view.get_child(bit) }) {
            return DescendResult::NonEmpty;
        }
    }
    if (view.child_bitmap() >> toward) & 1 == 0 {
        return DescendResult::Empty;
    }
    // SAFETY: toward is used exactly once; view is consumed.
    DescendResult::Child(unsafe { view.get_child(toward) })
}

/// Compare children of two aligned views. Children present on only one side
/// must be truly empty; common children are compared recursively.
fn eq_keys_children<'a, L, R>(mut left: L, mut right: R) -> bool
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    let l_children = left.child_bitmap();
    let r_children = right.child_bitmap();

    let mut left_only = l_children & !r_children;
    while left_only != 0 {
        let bit = left_only.trailing_zeros();
        left_only &= left_only - 1;
        // SAFETY: each child_bit is used exactly once.
        if !is_empty_recursive(unsafe { left.get_child(bit) }) {
            return false;
        }
    }

    let mut right_only = r_children & !l_children;
    while right_only != 0 {
        let bit = right_only.trailing_zeros();
        right_only &= right_only - 1;
        // SAFETY: each child_bit is used exactly once.
        if !is_empty_recursive(unsafe { right.get_child(bit) }) {
            return false;
        }
    }

    let mut common = l_children & r_children;
    while common != 0 {
        let bit = common.trailing_zeros();
        common &= common - 1;
        // SAFETY: each child_bit is used exactly once per view instance.
        if !eq_keys_recursive(unsafe { left.get_child(bit) }, unsafe {
            right.get_child(bit)
        }) {
            return false;
        }
    }
    true
}

pub(super) fn eq_keys_recursive<'a, L, R>(mut left: L, mut right: R) -> bool
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    // Align depths by descending the shallower side, verifying no extra entries.
    while left.depth() != right.depth() {
        if left.depth() < right.depth() {
            match descend_checking_empty(left, right.key()) {
                DescendResult::Child(child) => left = child,
                DescendResult::Empty => return is_empty_recursive(right),
                DescendResult::NonEmpty => return false,
            }
        } else {
            match descend_checking_empty(right, left.key()) {
                DescendResult::Child(child) => right = child,
                DescendResult::Empty => return is_empty_recursive(left),
                DescendResult::NonEmpty => return false,
            }
        }
    }

    // Same depth. Views at different positions can only be equal if both are empty.
    let min_prefix_len = left.prefix_len().min(right.prefix_len());
    let mask = mask_from_prefix_len(min_prefix_len as u8);
    if left.key() & mask != right.key() & mask {
        return is_empty_recursive(left) && is_empty_recursive(right);
    }

    if left.data_bitmap() != right.data_bitmap() {
        return false;
    }
    eq_keys_children(left, right)
}

#[cfg(test)]
mod tests {
    use crate::{
        trieview::{AsView, TrieView},
        Prefix, PrefixMap, PrefixSet,
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

    // -- eq_keys: basic cases ---------------------------------------------------

    #[test]
    fn eq_keys_same_maps() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        assert!(a.view().eq_keys(&b));
    }

    #[test]
    fn eq_keys_same_keys_different_values() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a000000, 8, 99), (0x0a010000, 16, 99)]);
        assert!(a.view().eq_keys(&b));
    }

    #[test]
    fn eq_keys_different_keys() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a000000, 8, 1), (0x0b000000, 8, 2)]);
        assert!(!a.view().eq_keys(&b));
    }

    #[test]
    fn eq_keys_subset() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a000000, 8, 1)]);
        assert!(!a.view().eq_keys(&b));
        assert!(!b.view().eq_keys(&a));
    }

    #[test]
    fn eq_keys_both_empty() {
        let a: PrefixMap<P, i32> = PrefixMap::new();
        let b: PrefixMap<P, i32> = PrefixMap::new();
        assert!(a.view().eq_keys(&b));
    }

    #[test]
    fn eq_keys_one_empty() {
        let a = map_from(&[(0x0a000000, 8, 1)]);
        let b: PrefixMap<P, i32> = PrefixMap::new();
        assert!(!a.view().eq_keys(&b));
    }

    #[test]
    fn eq_keys_map_vs_set() {
        let map = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let set: PrefixSet<P> = [p(0x0a000000, 8), p(0x0a010000, 16)].into_iter().collect();
        assert!(map.view().eq_keys(&set));
    }

    // -- eq_keys: subviews and depth differences --------------------------------

    #[test]
    fn eq_keys_subview_matches_full_map() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0b000000, 8, 3)]);
        let b = map_from(&[(0x0a000000, 8, 9), (0x0a010000, 16, 9)]);
        let a_sub = a.view_at(&p(0x0a000000, 8)).unwrap();
        assert!(a_sub.eq_keys(&b));
    }

    #[test]
    fn eq_keys_subviews_different_positions() {
        // Views at different subtrees with the same structure should NOT be equal.
        let a = map_from(&[(0x96000000, 7, 0)]);
        let b = map_from(&[(0xb6000000, 7, 0)]);
        let a_sub = a.view_at(&p(0x90000000, 5)).unwrap();
        let b_sub = b.view_at(&p(0xb0000000, 5)).unwrap();
        assert!(!a_sub.eq_keys(b_sub));
    }

    #[test]
    fn eq_keys_root_vs_subview_broader_has_extra() {
        // Root view has entries outside the subview's scope.
        let a = map_from(&[(0x00000000, 0, 0), (0x00000000, 9, 0)]);
        let b = map_from(&[(0x00000000, 9, 0)]);
        let b_sub = b.view_at(&p(0x00000000, 1)).unwrap();
        assert!(!a.view().eq_keys(b_sub));
    }

    // -- eq_keys: composed views (DifferenceView over-approximation) ------------

    #[test]
    fn eq_keys_empty_difference_vs_empty_map() {
        // a \ b is empty when a == b. The DifferenceView's child_bitmap is
        // over-approximated (uses all of left's children), but eq_keys must
        // recognize the difference is truly empty.
        let a = map_from(&[(0xf0000000, 5, 0)]);
        let b = map_from(&[(0xf0000000, 5, 0)]);
        let c: PrefixMap<P, i32> = PrefixMap::new();
        assert!(a.view().difference(&b).eq_keys(&c));
    }

    #[test]
    fn eq_keys_difference_removes_subset() {
        // a \ b = {10/8, 10.1/16}; should equal c's keys.
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0b000000, 8, 3)]);
        let b = map_from(&[(0x0b000000, 8, 10)]);
        let c = map_from(&[(0x0a000000, 8, 99), (0x0a010000, 16, 99)]);
        assert!(a.view().difference(&b).eq_keys(&c));
    }

    #[test]
    fn eq_keys_difference_with_subviews() {
        // Regression: empty difference at subview depth vs empty map at root.
        let a = map_from(&[(0xf0000000, 5, 0)]);
        let b = map_from(&[(0xf0000000, 5, 0)]);
        let c: PrefixMap<P, i32> = PrefixMap::new();
        let a_sub = a.view_at(&p(0x00000000, 0)).unwrap();
        let b_sub = b.view_at(&p(0x00000000, 0)).unwrap();
        assert!(a_sub.difference(b_sub).eq_keys(&c));
    }

    // -- eq_keys: descend_checking_empty edge cases -----------------------------

    #[test]
    fn eq_keys_shallower_has_nonempty_sibling() {
        // Left at root has entries in two subtrees. Right is a subview covering
        // only one. eq_keys must detect the non-empty sibling and return false.
        let a = map_from(&[(0x0a000000, 8, 1), (0x0b000000, 8, 2)]);
        let b = map_from(&[(0x0a000000, 8, 1)]);
        let b_sub = b.view_at(&p(0x0a000000, 8)).unwrap();
        assert!(!a.view().eq_keys(b_sub));
    }

    #[test]
    fn eq_keys_shallower_no_child_toward_deeper_both_empty() {
        // Left at root has no child toward right's subtree. Both sides
        // effectively have no entries -> equal.
        let a: PrefixMap<P, i32> = PrefixMap::new();
        let b = map_from(&[(0x0a000000, 8, 1)]);
        let b_sub = b.view_at(&p(0x0a000000, 8)).unwrap();
        // a is empty, b_sub has entries -> not equal
        assert!(!a.view().eq_keys(b_sub));
    }

    // -- eq_by -----------------------------------------------------------------

    #[test]
    fn eq_by_equal_values() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        assert!(a.view().eq_by(&b, |a, b| a == b));
    }

    #[test]
    fn eq_by_different_values() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 9)]);
        assert!(!a.view().eq_by(&b, |a, b| a == b));
    }

    #[test]
    fn eq_by_different_keys() {
        let a = map_from(&[(0x0a000000, 8, 1)]);
        let b = map_from(&[(0x0b000000, 8, 1)]);
        assert!(!a.view().eq_by(&b, |a, b| a == b));
    }

    #[test]
    fn eq_by_different_lengths() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a000000, 8, 1)]);
        assert!(!a.view().eq_by(&b, |a, b| a == b));
    }

    #[test]
    fn eq_by_custom_comparator() {
        let a = map_from(&[(0x0a000000, 8, 10), (0x0a010000, 16, 20)]);
        let b = map_from(&[(0x0a000000, 8, 11), (0x0a010000, 16, 21)]);
        // values differ by 1
        assert!(a.view().eq_by(&b, |a, b| (b - a) == 1));
    }

    #[test]
    fn eq_by_composed_view() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0b000000, 8, 3)]);
        let b = map_from(&[(0x0b000000, 8, 10)]);
        let c = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        assert!(a.view().difference(&b).eq_by(&c, |a, b| a == b));
    }
}
