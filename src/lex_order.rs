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

/// Temporary representation for `LEX_ORDER`.
#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
pub(crate) struct LexElem(u8);

const CHILD_FLAG: u8 = 1 << 7;

impl LexElem {
    #[cfg_attr(coverage_nightly, coverage(off))]
    const fn data(x: u8) -> Self {
        Self(x)
    }

    #[cfg_attr(coverage_nightly, coverage(off))]
    const fn child(x: u8) -> Self {
        Self(x + CHILD_FLAG)
    }
    /// Decodes the element.
    /// Returns `Ok(data_bit)` if this is a data slot, or `Err(child_bit)` if this is a child slot.
    pub(crate) const fn decode(self) -> Result<u32, u32> {
        if self.0 >= CHILD_FLAG {
            Err((self.0 - CHILD_FLAG) as u32)
        } else {
            Ok(self.0 as u32)
        }
    }
}

/// Mapping from the lexicographic iteration position to the data / child cell.
pub(crate) const LEX_ORDER: [LexElem; NUM_DATA + NUM_CHILDREN] =
    array_const_fn_init![const_lex_iter; 63];

#[cfg_attr(coverage_nightly, coverage(off))]
const fn const_lex_iter(i: usize) -> LexElem {
    let mut i = i as u32;
    let mut node: u32 = 0;
    let mut depth: u32 = 0;

    loop {
        if depth == K {
            return LexElem::child((node - ((1 << K) - 1)) as u8);
        }

        // This position in the traversal is the current node
        if i == 0 {
            return LexElem::data(node as u8);
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
        if let Ok(db) = LEX_ORDER[i].decode() {
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
        if let Err(cb) = LEX_ORDER[i].decode() {
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

/// Convert both occupancy bitmaps into `LEX_ORDER` positions.
#[inline(always)]
fn to_lex(data_bitmap: u32, child_bitmap: u32) -> u64 {
    to_lex_part(data_bitmap, &DATA_LEX_POS) | to_lex_part(child_bitmap, &CHILD_LEX_POS)
}

/// Storage-independent iterator over occupied data and child bit numbers in lexicographic
/// order. `Ok(bit)` denotes data and `Err(bit)` denotes a child. Either end can be consumed
/// without visiting absent slots, and each occupied slot is yielded at most once.
#[derive(Clone, Default)]
pub(crate) struct LexSlots {
    // Bit positions are indices into LEX_ORDER, not raw data/child bitmap positions.
    remaining: u64,
}

impl LexSlots {
    /// Construct from occupancy bitmaps containing only valid data/child bits.
    #[inline]
    pub(crate) fn new(data_bitmap: u32, child_bitmap: u32) -> Self {
        Self {
            remaining: to_lex(data_bitmap, child_bitmap),
        }
    }

    /// Retain only the supplied valid data/child bits; never restore consumed slots.
    #[inline]
    pub(crate) fn apply_masks(&mut self, data_bitmap: u32, child_bitmap: u32) {
        self.remaining &= to_lex(data_bitmap, child_bitmap);
    }
}

impl Iterator for LexSlots {
    type Item = Result<u32, u32>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let pos = self.remaining.trailing_zeros();
        self.remaining &= self.remaining - 1;
        Some(LEX_ORDER[pos as usize].decode())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl DoubleEndedIterator for LexSlots {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let pos = u64::BITS - 1 - self.remaining.leading_zeros();
        self.remaining &= !(1u64 << pos);
        Some(LEX_ORDER[pos as usize].decode())
    }
}

impl ExactSizeIterator for LexSlots {
    fn len(&self) -> usize {
        self.remaining.count_ones() as usize
    }
}

impl std::iter::FusedIterator for LexSlots {}

/// Map-specific wrapper resolving ordered slots against an original node snapshot.
#[derive(Clone)]
pub(crate) struct MaskedLexIter<R> {
    loc: Loc,
    depth: u32,
    key: R,
    // Original (unmasked) node: kept for correct POPCNT slot computation.
    node: MultiBitNode,
    slots: LexSlots,
}

impl<R: Key> Default for MaskedLexIter<R> {
    fn default() -> Self {
        Self {
            loc: Loc::root(),
            depth: Default::default(),
            key: R::zero(),
            node: Default::default(),
            slots: LexSlots::default(),
        }
    }
}

impl<R> MaskedLexIter<R> {
    pub(crate) fn new(loc: Loc, depth: u32, key: R, node: MultiBitNode) -> Self {
        Self {
            loc,
            depth,
            key,
            slots: LexSlots::new(node.data_bitmap, node.child_bitmap),
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

impl<R: Key> Iterator for MaskedLexIter<R> {
    type Item = LexIterElem<R>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.slots.next()? {
            Ok(data_bit) => LexIterElem::Data(DataIdx {
                node: self.loc,
                bit: data_bit,
                depth: self.depth,
            }),
            Err(child_bit) => LexIterElem::Child(
                Loc::new(self.node.children_idx, child_bit, self.node.child_bitmap),
                self.depth + K,
                extend_repr(self.key, self.depth, child_bit),
            ),
        })
    }
}

/// Returns `(data_mask, child_mask)` of all entries at or after `data_bit` in lex order.
#[inline(always)]
pub(crate) fn lex_after_data(data_bit: u32) -> (u32, u32) {
    LEX_AFTER_DATA[data_bit as usize]
}

/// Returns `(data_mask, child_mask)` of all entries strictly after `child_bit` in lex order.
#[inline(always)]
pub(crate) fn lex_after_child(child_bit: u32) -> (u32, u32) {
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
            match elem.decode() {
                Ok(db) => {
                    data_mask |= 1 << db;
                    if db as usize == i {
                        break;
                    }
                }
                Err(cb) => {
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
            match elem.decode() {
                Ok(db) => {
                    data_mask |= 1 << db;
                }
                Err(cb) => {
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
