//! Generic iterator over all `(prefix, value)` pairs in a [`TrieView`] sub-trie.
//!
//! [`ViewIter`] works for all view types: [`TrieRef`][super::TrieRef],
//! [`IntersectionView`][super::IntersectionView], [`UnionView`][super::union::UnionView],
//! [`DifferenceView`][super::DifferenceView], etc. (through a single generic implementation).

use crate::node::lex_order;

use super::{reconstruct_prefix, TrieView};

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
fn expand_node<'a, V: TrieView<'a>>(stack: &mut Vec<IterElem<'a, V>>, mut view: V) {
    for elem in lex_order().rev() {
        match elem {
            Ok(data_bit) => {
                if (view.data_bitmap() >> data_bit) & 1 == 0 {
                    continue;
                }
                let prefix = reconstruct_prefix::<V::P>(view.depth(), view.key(), data_bit);
                // SAFETY: each data_bit is visited at most once per expand_node call;
                // the bitmap is read before any get_data calls, and we iterate each
                // set bit exactly once.
                let value = unsafe { view.get_data(data_bit) };
                stack.push(IterElem::Item(prefix, value));
            }
            Err(child_bit) => {
                if (view.child_bitmap() >> child_bit) & 1 == 0 {
                    continue;
                }
                // SAFETY: each child_bit is visited at most once per expand_node call.
                stack.push(IterElem::Node(unsafe { view.get_child(child_bit) }));
            }
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
