//! Lexicographic slot ordering and bitmap conversion.

use crate::{
    allocator::Loc,
    node::{Key, MultiBitNode, extend_repr},
    table::{DataIdx, K, NUM_CHILDREN, NUM_DATA},
};
use array_const_fn_init::array_const_fn_init;

/// A single element of a lexicographic iterator (either a child or data).
#[derive(Clone, Copy)]
pub(crate) enum LexIterElem<R> {
    Data(DataIdx),
    Child(Loc, u32, R),
}

/// A raw slot pointing to a specific data or child bit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Slot {
    Data(u8),
    Child(u8),
}

/// Mapping from the lexicographic iteration position to the data / child cell.
const LEX_ORDER: [Slot; NUM_DATA + NUM_CHILDREN] = array_const_fn_init![const_lex_iter; 63];

#[cfg_attr(coverage_nightly, coverage(off))]
const fn const_lex_iter(i: usize) -> Slot {
    let mut i = i as u32;
    let mut node: u32 = 0;
    let mut depth: u32 = 0;

    loop {
        if depth == K {
            return Slot::Child((node - ((1 << K) - 1)) as u8);
        }

        // This position in the traversal is the current node
        if i == 0 {
            return Slot::Data(node as u8);
        }

        // Skip current node, descend into children
        i -= 1;

        // Size of each child's subtree in the traversal
        let child_subtree_size = (1 << (K - depth)) - 1;

        if i < child_subtree_size {
            // Go left
            node = 2 * node + 1;
        } else {
            // Skip left subtree, go right
            i -= child_subtree_size;
            node = 2 * node + 2;
        }
        depth += 1;
    }
}

/// Position of each data bit in `LEX_ORDER`.
const DATA_LEX_POS: [u8; NUM_DATA] = {
    let mut table = [0u8; NUM_DATA];
    let mut i = 0;
    while i < NUM_DATA + NUM_CHILDREN {
        if let Slot::Data(db) = LEX_ORDER[i] {
            table[db as usize] = i as u8;
        }
        i += 1;
    }
    table
};

/// Position of each child bit in `LEX_ORDER`.
const CHILD_LEX_POS: [u8; NUM_CHILDREN] = {
    let mut table = [0u8; NUM_CHILDREN];
    let mut i = 0;
    while i < NUM_DATA + NUM_CHILDREN {
        if let Slot::Child(cb) = LEX_ORDER[i] {
            table[cb as usize] = i as u8;
        }
        i += 1;
    }
    table
};

/// Map each set bit of `bitmap` to its position in `LEX_ORDER` using `positions`.
#[inline(always)]
fn to_lex_part(mut bitmap: u32, positions: &[u8]) -> u64 {
    let mut mask = 0u64;
    while bitmap != 0 {
        mask |= 1 << positions[bitmap.trailing_zeros() as usize];
        bitmap &= bitmap - 1;
    }
    mask
}

/// Convert both occupancy bitmaps into `LEX_ORDER` positions, ignoring unused data bits.
#[inline(always)]
fn to_lex(data_bitmap: u32, child_bitmap: u32) -> u64 {
    let data_bitmap = data_bitmap & ((1u64 << NUM_DATA) - 1) as u32;
    to_lex_part(data_bitmap, &DATA_LEX_POS) | to_lex_part(child_bitmap, &CHILD_LEX_POS)
}

/// Storage-independent iterator over occupied data and child bit numbers in lexicographic
/// order. Each item identifies a data or child bit. Either end can be consumed
/// without visiting absent slots, and each occupied slot is yielded at most once.
#[derive(Clone, Default)]
pub(crate) struct LexSlotIter {
    // Bit positions are indices into LEX_ORDER, not raw data/child bitmap positions.
    remaining: u64,
}

impl LexSlotIter {
    /// Construct from occupancy bitmaps containing only valid data/child bits.
    #[inline]
    pub(crate) fn new(data_bitmap: u32, child_bitmap: u32) -> Self {
        Self {
            remaining: to_lex(data_bitmap, child_bitmap),
        }
    }

    /// Retain only the supplied valid data/child bits; never restore consumed slots.
    #[inline]
    pub(crate) fn apply_masks(&mut self, data_mask: u32, child_mask: u32) {
        self.remaining &= to_lex(data_mask, child_mask);
    }
}

impl Iterator for LexSlotIter {
    type Item = Slot;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let pos = self.remaining.trailing_zeros();
        self.remaining &= self.remaining - 1;
        Some(LEX_ORDER[pos as usize])
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl DoubleEndedIterator for LexSlotIter {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let pos = u64::BITS - 1 - self.remaining.leading_zeros();
        self.remaining &= !(1u64 << pos);
        Some(LEX_ORDER[pos as usize])
    }
}

impl ExactSizeIterator for LexSlotIter {
    fn len(&self) -> usize {
        self.remaining.count_ones() as usize
    }
}

impl std::iter::FusedIterator for LexSlotIter {}

/// Wraps [`LexSlotIter`] with the node information to compute the popcount.
#[derive(Clone)]
pub(crate) struct LexNodeIter<R> {
    loc: Loc,
    depth: u32,
    key: R,
    // Original (unmasked) node: kept for correct POPCNT slot computation.
    node: MultiBitNode,
    slots: LexSlotIter,
}

impl<R: Key> Default for LexNodeIter<R> {
    fn default() -> Self {
        Self {
            loc: Loc::root(),
            depth: Default::default(),
            key: R::zero(),
            node: Default::default(),
            slots: LexSlotIter::default(),
        }
    }
}

impl<R> LexNodeIter<R> {
    pub(crate) fn new(loc: Loc, depth: u32, key: R, node: MultiBitNode) -> Self {
        Self {
            loc,
            depth,
            key,
            slots: LexSlotIter::new(node.data_bitmap, node.child_bitmap),
            node,
        }
    }

    pub(crate) fn key(&self) -> &R {
        &self.key
    }

    /// Location of the data slot at `data_bit`, computed from the node snapshot.
    #[inline(always)]
    pub(crate) fn data_loc(&self, data_bit: u32) -> Loc {
        Loc::new(self.node.data_idx, data_bit, self.node.data_bitmap)
    }

    /// Restrict both kinds of slots without changing the original node bitmaps,
    /// which are still needed for POPCNT slot computation.
    pub(crate) fn apply_masks(&mut self, data_mask: u32, child_mask: u32) {
        self.slots.apply_masks(
            data_mask & self.node.data_bitmap,
            child_mask & self.node.child_bitmap,
        );
    }
}

impl<R: Key> Iterator for LexNodeIter<R> {
    type Item = LexIterElem<R>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.slots.next()? {
            Slot::Data(data_bit) => LexIterElem::Data(DataIdx {
                node: self.loc,
                bit: data_bit as u32,
                depth: self.depth,
            }),
            Slot::Child(child_bit) => LexIterElem::Child(
                Loc::new(
                    self.node.children_idx,
                    child_bit as u32,
                    self.node.child_bitmap,
                ),
                self.depth + K,
                extend_repr(self.key, self.depth, child_bit as u32),
            ),
        })
    }
}

/// Returns `(data_mask, child_mask)` of all entries at or after `data_bit` in lex order.
#[inline(always)]
pub(crate) fn masks_from_data(data_bit: u32) -> (u32, u32) {
    LEX_AFTER_DATA[data_bit as usize]
}

/// Returns `(data_mask, child_mask)` of all entries strictly after `child_bit` in lex order.
#[inline(always)]
pub(crate) fn masks_after_child(child_bit: u32) -> (u32, u32) {
    LEX_AFTER_CHILD[child_bit as usize]
}

/// For data_bit `b`, returns `(data_mask, child_mask)` of all entries at or after `b` in lex
/// order (inclusive of `b` itself).
const LEX_AFTER_DATA: [(u32, u32); NUM_DATA] = {
    let mut table = [(0u32, 0u32); NUM_DATA];
    let mut i = NUM_DATA;
    while i > 0 {
        i -= 1;
        // Walk LEX_ORDER from the end, accumulating bits. For each data_bit position,
        // record the accumulated mask at the point where we encounter that data_bit.
        let mut data_mask = 0u32;
        let mut child_mask = 0u32;
        let mut j = NUM_DATA + NUM_CHILDREN;
        while j > 0 {
            j -= 1;
            let elem = LEX_ORDER[j];
            match elem {
                Slot::Data(db) => {
                    data_mask |= 1 << db;
                    if db as usize == i {
                        break;
                    }
                }
                Slot::Child(cb) => {
                    child_mask |= 1 << cb;
                }
            }
        }
        table[i] = (data_mask, child_mask);
    }
    table
};

/// For child_bit `b`, returns `(data_mask, child_mask)` of all entries strictly after `b` in
/// lex order (excludes `b` itself from the child_mask).
const LEX_AFTER_CHILD: [(u32, u32); NUM_CHILDREN] = {
    let mut table = [(0u32, 0u32); NUM_CHILDREN];
    let mut i = NUM_CHILDREN;
    while i > 0 {
        i -= 1;
        let mut data_mask = 0u32;
        let mut child_mask = 0u32;
        let mut j = NUM_DATA + NUM_CHILDREN;
        while j > 0 {
            j -= 1;
            let elem = LEX_ORDER[j];
            match elem {
                Slot::Data(db) => {
                    data_mask |= 1 << db;
                }
                Slot::Child(cb) => {
                    if cb as usize == i {
                        break;
                    }
                    child_mask |= 1 << cb;
                }
            }
        }
        table[i] = (data_mask, child_mask);
    }
    table
};

#[cfg(test)]
mod tests {
    use super::*;
    use Slot::{Child, Data};

    #[test]
    fn sparse_slots_in_lexicographic_order() {
        let data = (1 << 0) | (1 << 1) | (1 << 2) | (1 << 15) | (1 << 30);
        let children = (1 << 0) | (1 << 1) | (1 << 15) | (1 << 16) | (1 << 31);
        let expected = [
            Data(0), Data(1), Data(15), Child(0), Child(1),
            Child(15), Data(2), Child(16), Data(30), Child(31),
        ];
        assert_eq!(LexSlotIter::new(data, children).collect::<Vec<_>>(), expected);
        assert_eq!(
            LexSlotIter::new(data, children).rev().collect::<Vec<_>>(),
            expected.into_iter().rev().collect::<Vec<_>>(),
        );
    }

    #[test]
    fn mixed_ends_and_exact_size() {
        let mut slots = LexSlotIter::new((1 << 0) | (1 << 30), (1 << 0) | (1 << 31));
        assert_eq!(slots.len(), 4);
        assert_eq!(slots.size_hint(), (4, Some(4)));
        assert_eq!(slots.next(), Some(Data(0)));
        assert_eq!(slots.next_back(), Some(Child(31)));
        assert_eq!(slots.len(), 2);
        assert_eq!(slots.next_back(), Some(Data(30)));
        assert_eq!(slots.next(), Some(Child(0)));
        assert_eq!(slots.size_hint(), (0, Some(0)));
        assert_eq!(slots.next(), None);
        assert_eq!(slots.next_back(), None);
        assert_eq!(slots.next(), None);
    }

    #[test]
    fn unused_data_bit_is_ignored_but_last_child_is_valid() {
        assert_eq!(LexSlotIter::new(1 << 31, 0).count(), 0);
        assert_eq!(
            LexSlotIter::new(1 << 31, 1 << 31).collect::<Vec<_>>(),
            [Child(31)],
        );
        assert_eq!(LexSlotIter::new(!0, !0).count(), 63);
        let mut slots = LexSlotIter::new(!0, 1 << 31);
        slots.apply_masks(1 << 31, !0);
        assert_eq!(slots.collect::<Vec<_>>(), [Child(31)]);
    }

    #[test]
    fn masks_do_not_restore_consumed_or_filtered_slots() {
        let mut slots = LexSlotIter::new((1 << 0) | (1 << 1) | (1 << 2), (1 << 0) | (1 << 31));
        assert_eq!(slots.next(), Some(Data(0)));
        assert_eq!(slots.next_back(), Some(Child(31)));
        slots.apply_masks((1 << 0) | (1 << 2), !0);
        slots.apply_masks(!0, !0);
        assert_eq!(slots.clone().collect::<Vec<_>>(), [Child(0), Data(2)]);
        slots.apply_masks(0, 0);
        slots.apply_masks(!0, !0);
        assert_eq!(slots.next(), None);
        assert_eq!(slots.next_back(), None);
    }

    #[test]
    fn start_masks_include_data_but_exclude_children() {
        let mut slots = LexSlotIter::new(!0, !0);
        let (data, children) = masks_from_data(30);
        slots.apply_masks(data, children);
        assert_eq!(slots.collect::<Vec<_>>(), [Data(30), Child(30), Child(31)]);

        let mut slots = LexSlotIter::new(!0, !0);
        let (data, children) = masks_after_child(30);
        slots.apply_masks(data, children);
        assert_eq!(slots.collect::<Vec<_>>(), [Child(31)]);

        assert_eq!(masks_from_data(0), (0x7fffffff, u32::MAX));
        assert_eq!(masks_after_child(31), (0, 0));
    }

    #[test]
    fn node_masks_preserve_physical_offsets() {
        let node = MultiBitNode {
            data_bitmap: 1 | (1 << 2) | (1 << 30),
            child_bitmap: 1 | (1 << 31),
            ..Default::default()
        };
        let mut iter = LexNodeIter::new(Loc::root(), 5, 0u32, node);
        iter.apply_masks(1 << 30, 1 << 31);

        let Some(LexIterElem::Data(idx)) = iter.next() else {
            panic!("expected data bit 30");
        };
        assert_eq!(idx.bit, 30);
        assert_eq!(idx.depth, 5);
        assert_eq!(idx.node, Loc::root());
        // Filtering must not compact the original storage: bit 30 is still slot 2.
        assert_eq!(iter.data_loc(idx.bit).slot, 2);

        let Some(LexIterElem::Child(loc, depth, key)) = iter.next() else {
            panic!("expected child bit 31");
        };
        assert_eq!(loc.bit, 31);
        assert_eq!(loc.slot, 1);
        assert_eq!(depth, 10);
        assert_eq!(key, 0x07c00000);
        assert!(iter.next().is_none());
    }

    #[test]
    fn default_iterators_are_empty() {
        assert_eq!(LexSlotIter::default().next(), None);
        assert_eq!(LexSlotIter::default().next_back(), None);
        assert!(LexNodeIter::<u32>::default().next().is_none());
    }
}
