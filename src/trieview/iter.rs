//! Generic iterator over all `(prefix, value)` pairs in a [`TrieView`] sub-trie.
//!
//! [`ViewIter`] works for all view types: [`TrieRef`][super::TrieRef],
//! [`IntersectionView`][super::IntersectionView], [`UnionView`][super::union::UnionView],
//! [`DifferenceView`][super::DifferenceView], etc. (through a single generic implementation).

use crate::{
    node::{child_bit, data_bit, lex_after_child, lex_after_data, lex_order},
    prefix::mask_from_prefix_len,
    Prefix,
};

use super::{reconstruct_prefix, TrieView, K};

/// Iterator over all `(prefix, value)` pairs in a [`TrieView`] sub-trie.
///
/// Yields entries in lexicographic (DFS pre-order) order. The single generic implementation
/// works for all view types: [`TrieRef`][super::TrieRef], `IntersectionView`, etc.
pub struct ViewIter<'a, V: TrieView<'a>> {
    stack: Vec<IterElem<'a, V>>,
}

/// An entry on the iterator's internal stack.
enum IterElem<'a, V: TrieView<'a>> {
    /// A node whose data and children have not yet been expanded.
    Node(V),
    /// A ready-to-yield item.
    Item(V::P, V::T),
}

impl<'a, V: TrieView<'a>> ViewIter<'a, V> {
    pub(super) fn new(root: V) -> Self {
        let mut stack = Vec::new();
        expand_node(&mut stack, root);
        Self { stack }
    }

    pub(super) fn new_from(view: V, prefix: &V::P, inclusive: bool) -> Self {
        let target_key = prefix.mask();
        let target_len = prefix.prefix_len() as u32;
        let mut stack = Vec::new();
        build_iter_from_stack(&mut stack, view, target_key, target_len, inclusive);
        Self { stack }
    }
}

/// Iterator over all prefixes in a [`TrieView`] sub-trie.
pub struct ViewKeys<'a, V: TrieView<'a>>(ViewIter<'a, V>);

impl<'a, V: TrieView<'a>> ViewKeys<'a, V> {
    pub(super) fn new(root: V) -> Self {
        Self(ViewIter::new(root))
    }
}

impl<'a, V: TrieView<'a>> Iterator for ViewKeys<'a, V> {
    type Item = V::P;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(prefix, _)| prefix)
    }
}

/// Iterator over all values in a [`TrieView`] sub-trie.
pub struct ViewValues<'a, V: TrieView<'a>>(ViewIter<'a, V>);

impl<'a, V: TrieView<'a>> ViewValues<'a, V> {
    pub(super) fn new(root: V) -> Self {
        Self(ViewIter::new(root))
    }
}

impl<'a, V: TrieView<'a>> Iterator for ViewValues<'a, V> {
    type Item = V::T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, value)| value)
    }
}

/// Expand `view` into its data items and child nodes, pushing them onto `stack`
/// in **reverse** lexicographic order so that popping yields the correct lex order.
#[inline]
fn expand_node<'a, V: TrieView<'a>>(stack: &mut Vec<IterElem<'a, V>>, view: V) {
    expand_node_masked(stack, view, !0, !0)
}

/// Like [`expand_node`], but additionally masks data and child bits with the given masks.
#[inline]
fn expand_node_masked<'a, V: TrieView<'a>>(
    stack: &mut Vec<IterElem<'a, V>>,
    mut view: V,
    data_mask: u32,
    child_mask: u32,
) {
    let effective_data = view.data_bitmap() & data_mask;
    let effective_children = view.child_bitmap() & child_mask;

    for elem in lex_order().rev() {
        match elem {
            Ok(data_bit) => {
                if (effective_data >> data_bit) & 1 == 0 {
                    continue;
                }
                let prefix = reconstruct_prefix::<V::P>(view.depth(), view.key(), data_bit);
                // SAFETY: each data_bit is visited at most once per expand_node call;
                // the effective bitmap is a subset of data_bitmap(), and we iterate
                // each set bit exactly once.
                let value = unsafe { view.get_data(data_bit) };
                stack.push(IterElem::Item(prefix, value));
            }
            Err(child_bit) => {
                if (effective_children >> child_bit) & 1 == 0 {
                    continue;
                }
                // SAFETY: each child_bit is visited at most once per expand_node call.
                stack.push(IterElem::Node(unsafe { view.get_child(child_bit) }));
            }
        }
    }
}

/// Build an iterator stack starting from `current` that yields entries at or after
/// `(target_key, target_len)` in lexicographic order.
fn build_iter_from_stack<'a, V: TrieView<'a>>(
    stack: &mut Vec<IterElem<'a, V>>,
    mut current: V,
    target_key: <V::P as Prefix>::R,
    target_len: u32,
    inclusive: bool,
) {
    // Check containment: does the target share the view's prefix?
    let view_mask = mask_from_prefix_len(current.prefix_len() as u8);
    let view_prefix = current.key() & view_mask;
    let target_at_view_len = target_key & view_mask;

    if view_prefix != target_at_view_len {
        // Target is outside this view's sub-trie.
        // All entries share view_prefix; compare to determine before/after.
        if view_prefix > target_at_view_len {
            // All entries come after target → full iter
            expand_node(stack, current);
        }
        // else: all entries come before target → empty iter
        return;
    }

    // Target is within this view's sub-trie (or is the view's prefix itself).

    if target_len <= current.prefix_len() {
        // Target encompasses the view's position.
        if target_len == current.prefix_len() && !inclusive {
            // Skip the exact root value, include everything else.
            let db = data_bit(current.key(), current.prefix_len());
            expand_node_masked(stack, current, !(1u32 << db), !0);
        } else {
            expand_node(stack, current);
        }
        return;
    }

    // Target is deeper than the view's position. Navigate toward it.
    loop {
        if target_len < current.depth() + K {
            // Target falls within this node as a data slot.
            let db = data_bit(target_key, target_len);
            let (data_mask, child_mask) = lex_after_data(db);
            let data_mask = if inclusive {
                data_mask
            } else {
                data_mask & !(1 << db)
            };
            expand_node_masked(stack, current, data_mask, child_mask);
            break;
        }

        // Target is deeper; follow the child pointer.
        let cb = child_bit(current.depth(), target_key);
        let (data_mask, child_mask) = lex_after_child(cb);

        let has_child = (current.child_bitmap() >> cb) & 1 == 1;
        let child = if has_child {
            // SAFETY: cb is not in child_mask (lex_after_child excludes it),
            // so it won't be accessed again in expand_node_masked below.
            Some(unsafe { current.get_child(cb) })
        } else {
            None
        };

        expand_node_masked(stack, current, data_mask, child_mask);

        match child {
            Some(c) => current = c,
            None => break,
        }
    }
}

impl<'a, V: TrieView<'a>> Iterator for ViewIter<'a, V> {
    type Item = (V::P, V::T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.stack.pop()? {
                IterElem::Item(prefix, value) => return Some((prefix, value)),
                IterElem::Node(view) => expand_node(&mut self.stack, view),
            }
        }
    }
}
