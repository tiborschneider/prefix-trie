//! The inner node implementation.

use array_const_fn_init::array_const_fn_init;
use num_traits::{CheckedShr, One, PrimInt, Unsigned, Zero};

use super::table::{Present, K, NUM_CHILDREN, NUM_DATA};
use crate::{
    allocator::{AllocIdx, Loc},
    prefix::mask_from_prefix_len,
};

pub(crate) trait Key: Unsigned + PrimInt + Zero + One + CheckedShr {}
impl<R: Unsigned + PrimInt + Zero + One + CheckedShr> Key for R {}

/// A single node for the dense TreeBitMap
#[derive(Clone, Copy, Default)]
pub(crate) struct MultiBitNode {
    pub(super) data_bitmap: u32,
    pub(super) child_bitmap: u32,
    // The index at which all children are located in the table.
    pub(super) children_idx: AllocIdx,
    pub(super) data_idx: AllocIdx,
}

impl std::fmt::Debug for MultiBitNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MultiBitNode")
            .field(
                "data_bitmap",
                &format!("  {:#0width$b}", self.data_bitmap, width = NUM_DATA),
            )
            .field(
                "child_bitmap",
                &format!("{:#0width$b}", self.child_bitmap, width = NUM_CHILDREN),
            )
            .field("children_idx", &self.children_idx)
            .field("cell_idx", &self.data_idx)
            .finish()
    }
}

impl MultiBitNode {
    /****** DATA HANDLING *******/

    #[inline(always)]
    pub(crate) fn has_data_bit(&self, bit: u32) -> bool {
        self.data_bitmap & (1 << bit) != 0
    }

    /// If the data bit is set, return the `Present` for that data slot; otherwise `None`.
    #[inline(always)]
    pub(crate) fn data_loc_if_present(
        &self,
        node_loc: Loc,
        depth: u32,
        bit: u32,
    ) -> Option<Present> {
        if self.has_data_bit(bit) {
            let data_loc = Loc::new(self.data_idx, bit, self.data_bitmap);
            // SAFETY: has_data_bit confirmed the bit is set; slot = compute_slot(data_bitmap, bit).
            Some(unsafe { Present::new(node_loc, data_loc, depth) })
        } else {
            None
        }
    }

    #[inline(always)]
    pub(crate) fn data_bitmap(&self) -> u32 {
        self.data_bitmap
    }

    #[inline(always)]
    pub(crate) fn child_bitmap(&self) -> u32 {
        self.child_bitmap
    }

    #[inline(always)]
    pub(crate) fn set_data_bit(&mut self, bit: u32) {
        self.data_bitmap |= 1 << bit;
    }

    #[inline(always)]
    pub(crate) fn unset_data_bit(&mut self, bit: u32) {
        self.data_bitmap &= !(1 << bit);
    }

    /// Get an iterator over all internal offsets that are set.
    /// Yields Loc structs with bit (bitmap position) and computed slot for data access.
    #[inline(always)]
    pub(crate) fn data_locs(&self) -> impl DoubleEndedIterator<Item = Loc> + 'static {
        let data_idx = self.data_idx;
        let data_bitmap = self.data_bitmap;
        (0..NUM_DATA as u32)
            .filter(move |&raw| data_bitmap & (1 << raw) != 0)
            .map(move |raw| Loc::new(data_idx, raw, data_bitmap))
    }

    /****** CHILD HANDLING *******/

    #[inline(always)]
    pub(crate) fn has_child_bit(&self, bit: u32) -> bool {
        self.child_bitmap & (1 << bit) != 0
    }

    #[inline(always)]
    pub(crate) fn set_child_bit(&mut self, bit: u32) {
        self.child_bitmap |= 1 << bit;
    }

    #[inline(always)]
    pub(crate) fn unset_child_bit(&mut self, bit: u32) {
        self.child_bitmap &= !(1 << bit);
    }

    /// Get an iterator over all children.
    /// Yields Loc with bit set to the child bitmap position (for operations like unset_child_bit).
    #[inline(always)]
    pub(crate) fn child_locs(&self) -> impl Iterator<Item = Loc> + 'static {
        let idx = self.children_idx;
        let child_bitmap = self.child_bitmap;
        (0..NUM_CHILDREN as u32)
            .filter(move |&raw| child_bitmap & (1 << raw) != 0)
            .map(move |raw| Loc::new(idx, raw, child_bitmap))
    }

    /****** COVER STUFF *******/

    /// Iterator over all data locations that are covered by the prefix. This includes the
    /// prefix itself. Each Loc includes the bit (bitmap position) and computed slot.
    ///
    /// Safety: This iterator only yields indixes that are set in the internal bitmap.
    #[inline(always)]
    pub(crate) fn data_cover_locs<R: Key>(
        &self,
        depth: u32,
        key: R,
        prefix_len: u32,
    ) -> impl DoubleEndedIterator<Item = Loc> + 'static {
        let filtered = data_cover_mask(depth, key, prefix_len) & self.data_bitmap;
        let data_idx = self.data_idx;
        let data_bitmap = self.data_bitmap;
        (0..NUM_DATA as u32)
            .filter(move |&raw| filtered & (1 << raw) != 0)
            .map(move |raw| Loc::new(data_idx, raw, data_bitmap))
    }

    /// Iterator over the indices of all children that of that node that are covered within the
    /// prefix itself. Important: The function returns no entries if the prefix length is not part
    /// of this node.
    ///
    /// The function does check if these nodes actually exist, and only returns those indixes
    #[inline(always)]
    pub(crate) fn child_cover_locs<R: Key>(
        &self,
        depth: u32,
        key: R,
        prefix_len: u32,
    ) -> impl Iterator<Item = Loc> + 'static {
        let filtered = child_cover_mask(depth, key, prefix_len) & self.child_bitmap;
        let children_idx = self.children_idx;
        let child_bitmap = self.child_bitmap;
        (0..NUM_CHILDREN as u32)
            .filter(move |&raw| filtered & (1 << raw) != 0)
            .map(move |raw| Loc::new(children_idx, raw, child_bitmap))
    }

    /****** DATA LPM *******/

    /// Iterator over all internal node indices that cover a given prefix
    ///
    /// Safety: This iterator only yields indixes that are set in the internal bitmap.
    #[inline(always)]
    pub(crate) fn data_lpm_locs<R: Key>(
        &self,
        depth: u32,
        key: R,
        prefix_len: u32,
    ) -> impl Iterator<Item = Loc> + 'static {
        let filtered = data_lpm_mask(depth, key, prefix_len) & self.data_bitmap;
        let data_idx = self.data_idx;
        let data_bitmap = self.data_bitmap;
        (0..NUM_DATA as u32)
            .filter(move |&raw| filtered & (1 << raw) != 0)
            .map(move |raw| Loc::new(data_idx, raw, data_bitmap))
    }

    /// Get the data loc of the longest prefix match in this node (if it exists).
    /// Returns Loc with bit (bitmap position) and computed slot.
    pub(crate) fn data_lpm_loc<R: Key>(&self, depth: u32, key: R, prefix_len: u32) -> Option<Loc> {
        let nodes_present = self.data_bitmap & data_lpm_mask(depth, key, prefix_len);
        if nodes_present == 0 {
            return None;
        }
        let msb_raw = u32::BITS - 1 - nodes_present.leading_zeros();
        Some(Loc::new(self.data_idx, msb_raw, self.data_bitmap))
    }

    /// Get the data loc of the shortest prefix match in this node (if it exists).
    /// Returns Loc with bit (bitmap position) and computed slot.
    pub(crate) fn data_spm_loc<R: Key>(&self, depth: u32, key: R, prefix_len: u32) -> Option<Loc> {
        let nodes_present = self.data_bitmap & data_lpm_mask(depth, key, prefix_len);
        if nodes_present == 0 {
            return None;
        }
        let lsb_raw = nodes_present.trailing_zeros();
        Some(Loc::new(self.data_idx, lsb_raw, self.data_bitmap))
    }
}

#[inline(always)]
pub(crate) fn data_bit<R: Key>(key: R, prefix_len: u32) -> u32 {
    // prefix must be in this node.
    let depth = (prefix_len / K) * K;
    let num_bits = R::zero().count_zeros();
    let mask = R::one().unsigned_shl(K).sub(R::one());
    // Extract the K-bit block starting at `depth` (from MSB).  When `depth + K > num_bits`
    // the window extends past the key width, so we left-shift instead of right-shifting to
    // avoid u32 underflow (e.g. depth=30, K=5, num_bits=32 -> shift would be −3).
    let pattern = if depth + K <= num_bits {
        key.unsigned_shr(num_bits - depth - K).bitand(mask)
    } else {
        key.unsigned_shl(depth + K - num_bits).bitand(mask)
    };
    let level = prefix_len - depth;
    let offset = (1u32 << level) - 1;
    pattern.unsigned_shr(K - level).to_u32().unwrap() + offset
}

const LEVEL_SIZE: usize = 1 << (K - 1);
const PATTERN_SIZE: usize = (K as usize) * LEVEL_SIZE;
type Pattern = [u32; PATTERN_SIZE];

const DATA_LPM_PATTERN: Pattern = array_const_fn_init![const_data_lpm_pattern; 80];
const fn const_data_lpm_pattern(i: usize) -> u32 {
    let lvl = i / LEVEL_SIZE;
    let pos = i % LEVEL_SIZE;
    let mut result: u32 = 1;
    let mut j: u32 = 1;
    while j <= lvl as u32 {
        let field_offset = (1usize << j) - 1;
        let top_j = pos >> (K - 1 - j);
        result |= 1u32 << (top_j + field_offset);
        j += 1;
    }
    result
}

const DATA_COVER_PATTERN: Pattern = array_const_fn_init![const_data_cover_pattern; 80];
const fn const_data_cover_pattern(i: usize) -> u32 {
    let i = i as u32;
    let lvl = i / LEVEL_SIZE as u32;
    let pos = i % LEVEL_SIZE as u32;

    if lvl == 0 {
        return (1u32 << ((1usize << K) - 1)) - 1;
    }

    // Which node at this level does `pos` belong to?
    let node = pos >> (K - 1 - lvl);

    let mut result: u32 = 0;
    let mut j = lvl;
    while j < K {
        let field_offset = (1usize << j) - 1;
        let start = node << (j - lvl);
        let block_size = 1usize << (j - lvl);
        let mask = ((1u32 << block_size) - 1) << start;
        result |= mask << field_offset;
        j += 1;
    }

    result
}

const CHILD_COVER_PATTERN: Pattern = array_const_fn_init![const_child_cover_pattern; 80];
const fn const_child_cover_pattern(i: usize) -> u32 {
    let k = K as usize;
    let lvl = i / LEVEL_SIZE;
    let pos = i % LEVEL_SIZE;

    let node = pos >> (k - 1 - lvl);
    let block_size = k - lvl; // log2 of actual block size
    let start = node << block_size;
    let mask = ((1usize << (1usize << block_size)) - 1) << start;

    mask as u32
}

#[inline(always)]
fn get_mask<R: Key>(depth: u32, key: R, prefix_len: u32, patterns: &Pattern) -> u32 {
    // prefix length must be at least as large as the current depth of the node.
    debug_assert!(prefix_len >= depth);
    let num_bits = R::zero().count_zeros();
    // Extract the (K-1)-bit block starting at `depth` (from MSB).  When `depth + K > num_bits + 1`
    // the window extends past the key width, so we left-shift to avoid u32 underflow.
    let mask = R::one().unsigned_shl(K - 1).sub(R::one());
    let pattern = if depth + K <= num_bits + 1 {
        key.unsigned_shr(num_bits - depth - K + 1).bitand(mask)
    } else {
        key.unsigned_shl(depth + K - num_bits - 1).bitand(mask)
    }
    .to_usize()
    .unwrap();
    let max_level = (prefix_len - depth).min(K - 1) as usize;
    let pattern_idx = pattern + max_level * (1 << (K - 1));
    // SAFETY: pattern_idx is always within the max pattern, because we mask the pattern (and then offset it).
    debug_assert!(pattern_idx < patterns.len());
    unsafe { *patterns.get_unchecked(pattern_idx) }
}

#[inline(always)]
pub(crate) fn data_lpm_mask<R: Key>(depth: u32, key: R, prefix_len: u32) -> u32 {
    get_mask(depth, key, prefix_len, &DATA_LPM_PATTERN)
}

#[inline(always)]
pub(crate) fn data_cover_mask<R: Key>(depth: u32, key: R, prefix_len: u32) -> u32 {
    get_mask(depth, key, prefix_len, &DATA_COVER_PATTERN)
}

#[inline(always)]
pub(crate) fn child_cover_mask<R: Key>(depth: u32, key: R, prefix_len: u32) -> u32 {
    get_mask(depth, key, prefix_len, &CHILD_COVER_PATTERN)
}

/// Given a data bit `b`, return the mask of all data bits in the same node covered by it.
///
/// This includes `b` itself and all its heap descendants (`2b+1`, `2b+2`, etc.).
/// Equivalent to `data_cover_mask(depth, key_for_b, depth + level_b)` but without
/// requiring key reconstruction.
#[inline(always)]
pub(crate) fn data_cover_mask_for_bit(b: u32) -> u32 {
    let (offset, level) = DATA_BIT_TO_PREFIX[b as usize];
    DATA_COVER_PATTERN[offset as usize + level as usize * LEVEL_SIZE]
}

/// Given a data bit `b`, return the mask of child bits covered by it.
///
/// Equivalent to `child_cover_mask(depth, key_for_b, depth + level_b)` but without
/// requiring key reconstruction.
#[inline(always)]
pub(crate) fn child_cover_mask_for_bit(b: u32) -> u32 {
    let (offset, level) = DATA_BIT_TO_PREFIX[b as usize];
    CHILD_COVER_PATTERN[offset as usize + level as usize * LEVEL_SIZE]
}

#[inline(always)]
pub(crate) fn child_bit<R: Key>(depth: u32, key: R) -> u32 {
    let mask = R::one().unsigned_shl(K).sub(R::one());
    let pattern = key
        .unsigned_shr(R::zero().count_zeros() - depth - K)
        .bitand(mask);
    pattern.to_u32().unwrap()
}

#[derive(Clone, Copy)]
pub(crate) enum LexIterElem<R> {
    Data(Present),
    Child(Loc, u32, R),
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
struct LexElem(u8);

const CHILD_FLAG: u8 = 1 << 7;

impl LexElem {
    const fn data(x: u8) -> Self {
        Self(x)
    }

    const fn child(x: u8) -> Self {
        Self(x + CHILD_FLAG)
    }
    /// Decodes the element.
    /// Returns `Ok(data_bit)` if this is a data slot, or `Err(child_bit)` if this is a child slot.
    const fn decode(self) -> Result<u32, u32> {
        if self.0 >= CHILD_FLAG {
            Err((self.0 - CHILD_FLAG) as u32)
        } else {
            Ok(self.0 as u32)
        }
    }
}

const LEX_ORDER: [LexElem; NUM_DATA + NUM_CHILDREN] = array_const_fn_init![const_lex_iter; 63];
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

#[derive(Clone)]
pub(crate) struct MaskedLexIter<R> {
    iter: std::slice::Iter<'static, LexElem>,
    loc: Loc,
    depth: u32,
    key: R,
    // Original (unmasked) node: kept for correct POPCNT slot computation.
    node: MultiBitNode,
    // Separate filter fields: apply_*_mask modifies these, not the node bitmaps.
    data_filter: u32,
    child_filter: u32,
}

impl<R: Key> Default for MaskedLexIter<R> {
    fn default() -> Self {
        Self {
            iter: Default::default(),
            loc: Loc::root(),
            depth: Default::default(),
            key: R::zero(),
            node: Default::default(),
            data_filter: u32::MAX,
            child_filter: u32::MAX,
        }
    }
}

impl<R> MaskedLexIter<R> {
    pub(crate) fn new(loc: Loc, depth: u32, key: R, node: MultiBitNode) -> Self {
        Self {
            iter: LEX_ORDER.iter(),
            loc,
            depth,
            key,
            node,
            data_filter: u32::MAX,
            child_filter: u32::MAX,
        }
    }

    pub(crate) fn key(&self) -> &R {
        &self.key
    }

    pub(crate) fn apply_data_mask(&mut self, mask: u32) {
        // Only reduce the set of offsets to yield; keep node.data_bitmap intact for POPCNT.
        self.data_filter &= mask;
    }

    pub(crate) fn apply_child_mask(&mut self, mask: u32) {
        self.child_filter &= mask;
    }
}

impl<R: Key> Iterator for MaskedLexIter<R> {
    type Item = LexIterElem<R>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let next = *self.iter.next()?;
            match next.decode() {
                Ok(data_bit) => {
                    // Check original bitmap (for existence) AND filter (for masking).
                    if self.node.has_data_bit(data_bit) && (self.data_filter & (1 << data_bit)) != 0
                    {
                        let data_loc =
                            Loc::new(self.node.data_idx, data_bit, self.node.data_bitmap);
                        return Some(LexIterElem::Data(
                            // SAFETY:
                            // - `has_data_bit` confirmed the bitmap bit at `data_bit` is set,
                            //   so the element at that position is initialized.
                            // - `slot` = compute_slot(self.node.data_bitmap, data_bit), which is
                            //   the correct physical index of the initialized entry.
                            // - `self.node` is a snapshot taken when MaskedLexIter was constructed,
                            //   and the bitmap has not been modified since.
                            unsafe { Present::new(self.loc, data_loc, self.depth) },
                        ));
                    }
                }
                Err(child_bit) => {
                    if self.node.has_child_bit(child_bit)
                        && (self.child_filter & (1 << child_bit)) != 0
                    {
                        return Some(LexIterElem::Child(
                            Loc::new(self.node.children_idx, child_bit, self.node.child_bitmap),
                            self.depth + K,
                            extend_repr(self.key, self.depth, child_bit),
                        ));
                    }
                }
            }
        }
    }
}

/// Iterate over all data and child slot positions in lexicographic (DFS pre-order) order.
/// Yields `Ok(data_bit)` for data positions and `Err(child_bit)` for child positions.
/// Supports reverse iteration, which is needed to push stack entries in reverse lex order.
pub(crate) fn lex_order() -> impl DoubleEndedIterator<Item = Result<u32, u32>> {
    LEX_ORDER.iter().copied().map(LexElem::decode)
}

pub(crate) fn extend_repr<R: Key>(key: R, depth: u32, offset: u32) -> R {
    let mask = mask_from_prefix_len(depth as u8);
    let root = key & mask;

    let offset = <R as num_traits::cast::NumCast>::from(offset).unwrap();
    let offset_bits = K;
    let total_width = R::zero().count_zeros();
    let shifted_offset = if total_width > depth + offset_bits {
        offset << (total_width - (depth + offset_bits)) as usize
    } else {
        offset >> (depth + offset_bits - total_width) as usize
    };

    root | shifted_offset
}

#[rustfmt::skip]
pub(crate) const DATA_BIT_TO_PREFIX: [(u8, u8); NUM_DATA] = [
    (0b0000, 0),
    (0b0000, 1),                                     (0b1000, 1),
    (0b0000, 2), (0b0100, 2),                         (0b1000, 2),             (0b1100, 2),
    (0b0000, 3), (0b0010, 3), (0b0100, 3), (0b0110, 3), (0b1000, 3), (0b1010, 3), (0b1100, 3), (0b1110, 3),
    (0b0000, 4), (0b0001, 4), (0b0010, 4), (0b0011, 4), (0b0100, 4), (0b0101, 4), (0b0110, 4), (0b0111, 4), (0b1000, 4), (0b1001, 4), (0b1010, 4), (0b1011, 4), (0b1100, 4), (0b1101, 4), (0b1110, 4), (0b1111, 4),
];

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn internal_idx_test() {
        // Test cases updated for K=5
        let test_cases: [(u32, u32, u32); _] = [
            // prefix_len 0: level=0, offset=0, max_idx=0
            (0xdeadbeef, 0, 0),
            (0xffffffff, 0, 0),
            (0x00000000, 0, 0),
            // prefix_len 1-4: level=1-4, offset=1,3,7,15
            (0x7eadbeef, 1, 1),
            (0xaeadbeef, 1, 2),
            (0x3eadbeef, 2, 3),
            (0x4eadbeef, 2, 4),
            (0xbeadbeef, 2, 5),
            (0xfeadbeef, 2, 6),
            (0x0eadbeef, 3, 7),
            (0x2eadbeef, 3, 8),
            (0x4eadbeef, 3, 9),
            (0x6eadbeef, 3, 10),
            (0x8eadbeef, 3, 11),
            (0xaeadbeef, 3, 12),
            (0xceadbeef, 3, 13),
            (0xeeadbeef, 3, 14),
            // prefix_len 4: level=4, offset=15
            (0xddadbeef, 4, 28),
            // prefix_len 5+: moves to next tier
            (0xd7adbeef, 5, 0),
            (0xdaadbeef, 5, 0),
            (0xd3adbeef, 6, 1),
            (0xd4adbeef, 6, 2),
            (0xdbadbeef, 6, 1),
            (0xdfadbeef, 6, 2),
            (0xd0adbeef, 7, 3),
            (0xd2adbeef, 7, 4),
            (0xd4adbeef, 7, 5),
            (0xd6adbeef, 7, 6),
            (0xd8adbeef, 7, 3),
            (0xdaadbeef, 7, 4),
        ];
        for (key, prefix_len, want) in test_cases {
            assert_eq!(
                data_bit::<u32>(key, prefix_len),
                want,
                "data_bit mismatch for key={:#x}, prefix_len={}",
                key,
                prefix_len
            )
        }
    }

    #[test]
    fn lpm_pattern() {
        assert_eq!(DATA_LPM_PATTERN[0 + 00], 0b1);
        assert_eq!(DATA_LPM_PATTERN[0 + 08], 0b1);
        assert_eq!(DATA_LPM_PATTERN[0 + 15], 0b1);

        assert_eq!(DATA_LPM_PATTERN[16 + 00], 0b01_1);
        assert_eq!(DATA_LPM_PATTERN[16 + 07], 0b01_1);
        assert_eq!(DATA_LPM_PATTERN[16 + 08], 0b10_1);
        assert_eq!(DATA_LPM_PATTERN[16 + 15], 0b10_1);

        assert_eq!(DATA_LPM_PATTERN[32 + 00], 0b0001_01_1);
        assert_eq!(DATA_LPM_PATTERN[32 + 03], 0b0001_01_1);
        assert_eq!(DATA_LPM_PATTERN[32 + 04], 0b0010_01_1);
        assert_eq!(DATA_LPM_PATTERN[32 + 07], 0b0010_01_1);
        assert_eq!(DATA_LPM_PATTERN[32 + 08], 0b0100_10_1);
        assert_eq!(DATA_LPM_PATTERN[32 + 11], 0b0100_10_1);
        assert_eq!(DATA_LPM_PATTERN[32 + 12], 0b1000_10_1);
        assert_eq!(DATA_LPM_PATTERN[32 + 15], 0b1000_10_1);

        assert_eq!(DATA_LPM_PATTERN[48 + 00], 0b00000001_0001_01_1);
        assert_eq!(DATA_LPM_PATTERN[48 + 03], 0b00000010_0001_01_1);
        assert_eq!(DATA_LPM_PATTERN[48 + 04], 0b00000100_0010_01_1);
        assert_eq!(DATA_LPM_PATTERN[48 + 07], 0b00001000_0010_01_1);
        assert_eq!(DATA_LPM_PATTERN[48 + 08], 0b00010000_0100_10_1);
        assert_eq!(DATA_LPM_PATTERN[48 + 11], 0b00100000_0100_10_1);
        assert_eq!(DATA_LPM_PATTERN[48 + 12], 0b01000000_1000_10_1);
        assert_eq!(DATA_LPM_PATTERN[48 + 15], 0b10000000_1000_10_1);

        assert_eq!(
            DATA_LPM_PATTERN[64 + 00],
            0b0000000000000001_00000001_0001_01_1
        );
        assert_eq!(
            DATA_LPM_PATTERN[64 + 03],
            0b0000000000001000_00000010_0001_01_1
        );
        assert_eq!(
            DATA_LPM_PATTERN[64 + 04],
            0b0000000000010000_00000100_0010_01_1
        );
        assert_eq!(
            DATA_LPM_PATTERN[64 + 07],
            0b0000000010000000_00001000_0010_01_1
        );
        assert_eq!(
            DATA_LPM_PATTERN[64 + 08],
            0b0000000100000000_00010000_0100_10_1
        );
        assert_eq!(
            DATA_LPM_PATTERN[64 + 11],
            0b0000100000000000_00100000_0100_10_1
        );
        assert_eq!(
            DATA_LPM_PATTERN[64 + 12],
            0b0001000000000000_01000000_1000_10_1
        );
        assert_eq!(
            DATA_LPM_PATTERN[64 + 15],
            0b1000000000000000_10000000_1000_10_1
        );
    }

    #[test]
    #[rustfmt::skip]
    fn internal_cover_pattern() {
        assert_eq!(DATA_COVER_PATTERN[0 + 00], 0b1111111111111111_11111111_1111_11_1);
        assert_eq!(DATA_COVER_PATTERN[0 + 08], 0b1111111111111111_11111111_1111_11_1);
        assert_eq!(DATA_COVER_PATTERN[0 + 15], 0b1111111111111111_11111111_1111_11_1);

        assert_eq!(DATA_COVER_PATTERN[16 + 00], 0b0000000011111111_00001111_0011_01_0);
        assert_eq!(DATA_COVER_PATTERN[16 + 07], 0b0000000011111111_00001111_0011_01_0);
        assert_eq!(DATA_COVER_PATTERN[16 + 08], 0b1111111100000000_11110000_1100_10_0);
        assert_eq!(DATA_COVER_PATTERN[16 + 15], 0b1111111100000000_11110000_1100_10_0);

        assert_eq!(DATA_COVER_PATTERN[32 + 00], 0b0000000000001111_00000011_0001_00_0);
        assert_eq!(DATA_COVER_PATTERN[32 + 03], 0b0000000000001111_00000011_0001_00_0);
        assert_eq!(DATA_COVER_PATTERN[32 + 04], 0b0000000011110000_00001100_0010_00_0);
        assert_eq!(DATA_COVER_PATTERN[32 + 07], 0b0000000011110000_00001100_0010_00_0);
        assert_eq!(DATA_COVER_PATTERN[32 + 08], 0b0000111100000000_00110000_0100_00_0);
        assert_eq!(DATA_COVER_PATTERN[32 + 11], 0b0000111100000000_00110000_0100_00_0);
        assert_eq!(DATA_COVER_PATTERN[32 + 12], 0b1111000000000000_11000000_1000_00_0);
        assert_eq!(DATA_COVER_PATTERN[32 + 15], 0b1111000000000000_11000000_1000_00_0);

        assert_eq!(DATA_COVER_PATTERN[48 + 00], 0b0000000000000011_00000001_0000_00_0);
        assert_eq!(DATA_COVER_PATTERN[48 + 03], 0b0000000000001100_00000010_0000_00_0);
        assert_eq!(DATA_COVER_PATTERN[48 + 04], 0b0000000000110000_00000100_0000_00_0);
        assert_eq!(DATA_COVER_PATTERN[48 + 07], 0b0000000011000000_00001000_0000_00_0);
        assert_eq!(DATA_COVER_PATTERN[48 + 08], 0b0000001100000000_00010000_0000_00_0);
        assert_eq!(DATA_COVER_PATTERN[48 + 11], 0b0000110000000000_00100000_0000_00_0);
        assert_eq!(DATA_COVER_PATTERN[48 + 12], 0b0011000000000000_01000000_0000_00_0);
        assert_eq!(DATA_COVER_PATTERN[48 + 15], 0b1100000000000000_10000000_0000_00_0);

        assert_eq!(DATA_COVER_PATTERN[64 + 00], 0b0000000000000001_00000000_0000_00_0);
        assert_eq!(DATA_COVER_PATTERN[64 + 03], 0b0000000000001000_00000000_0000_00_0);
        assert_eq!(DATA_COVER_PATTERN[64 + 04], 0b0000000000010000_00000000_0000_00_0);
        assert_eq!(DATA_COVER_PATTERN[64 + 07], 0b0000000010000000_00000000_0000_00_0);
        assert_eq!(DATA_COVER_PATTERN[64 + 08], 0b0000000100000000_00000000_0000_00_0);
        assert_eq!(DATA_COVER_PATTERN[64 + 11], 0b0000100000000000_00000000_0000_00_0);
        assert_eq!(DATA_COVER_PATTERN[64 + 12], 0b0001000000000000_00000000_0000_00_0);
        assert_eq!(DATA_COVER_PATTERN[64 + 15], 0b1000000000000000_00000000_0000_00_0);
    }

    #[test]
    #[rustfmt::skip]
    fn external_cover_pattern() {
        assert_eq!(CHILD_COVER_PATTERN[00 + 00], 0b11111111_11111111__11111111_11111111);
        assert_eq!(CHILD_COVER_PATTERN[00 + 08], 0b11111111_11111111__11111111_11111111);
        assert_eq!(CHILD_COVER_PATTERN[00 + 15], 0b11111111_11111111__11111111_11111111);

        assert_eq!(CHILD_COVER_PATTERN[16 + 00], 0b00000000_00000000__11111111_11111111);
        assert_eq!(CHILD_COVER_PATTERN[16 + 07], 0b00000000_00000000__11111111_11111111);
        assert_eq!(CHILD_COVER_PATTERN[16 + 08], 0b11111111_11111111__00000000_00000000);
        assert_eq!(CHILD_COVER_PATTERN[16 + 15], 0b11111111_11111111__00000000_00000000);

        assert_eq!(CHILD_COVER_PATTERN[32 + 00], 0b00000000_00000000__00000000_11111111);
        assert_eq!(CHILD_COVER_PATTERN[32 + 03], 0b00000000_00000000__00000000_11111111);
        assert_eq!(CHILD_COVER_PATTERN[32 + 04], 0b00000000_00000000__11111111_00000000);
        assert_eq!(CHILD_COVER_PATTERN[32 + 07], 0b00000000_00000000__11111111_00000000);
        assert_eq!(CHILD_COVER_PATTERN[32 + 08], 0b00000000_11111111__00000000_00000000);
        assert_eq!(CHILD_COVER_PATTERN[32 + 11], 0b00000000_11111111__00000000_00000000);
        assert_eq!(CHILD_COVER_PATTERN[32 + 12], 0b11111111_00000000__00000000_00000000);
        assert_eq!(CHILD_COVER_PATTERN[32 + 15], 0b11111111_00000000__00000000_00000000);

        assert_eq!(CHILD_COVER_PATTERN[48 + 00], 0b00000000_00000000__00000000_00001111);
        assert_eq!(CHILD_COVER_PATTERN[48 + 03], 0b00000000_00000000__00000000_11110000);
        assert_eq!(CHILD_COVER_PATTERN[48 + 04], 0b00000000_00000000__00001111_00000000);
        assert_eq!(CHILD_COVER_PATTERN[48 + 07], 0b00000000_00000000__11110000_00000000);
        assert_eq!(CHILD_COVER_PATTERN[48 + 08], 0b00000000_00001111__00000000_00000000);
        assert_eq!(CHILD_COVER_PATTERN[48 + 11], 0b00000000_11110000__00000000_00000000);
        assert_eq!(CHILD_COVER_PATTERN[48 + 12], 0b00001111_00000000__00000000_00000000);
        assert_eq!(CHILD_COVER_PATTERN[48 + 15], 0b11110000_00000000__00000000_00000000);

        assert_eq!(CHILD_COVER_PATTERN[64 + 00], 0b00000000_00000000__00000000_00000011);
        assert_eq!(CHILD_COVER_PATTERN[64 + 03], 0b00000000_00000000__00000000_11000000);
        assert_eq!(CHILD_COVER_PATTERN[64 + 04], 0b00000000_00000000__00000011_00000000);
        assert_eq!(CHILD_COVER_PATTERN[64 + 07], 0b00000000_00000000__11000000_00000000);
        assert_eq!(CHILD_COVER_PATTERN[64 + 08], 0b00000000_00000011__00000000_00000000);
        assert_eq!(CHILD_COVER_PATTERN[64 + 11], 0b00000000_11000000__00000000_00000000);
        assert_eq!(CHILD_COVER_PATTERN[64 + 12], 0b00000011_00000000__00000000_00000000);
        assert_eq!(CHILD_COVER_PATTERN[64 + 15], 0b11000000_00000000__00000000_00000000);
    }
}
