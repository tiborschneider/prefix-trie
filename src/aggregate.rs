//! Aggregation for the multibit TreeBitMap.
//!
//! "Aggregation" collapses a trie into a smaller, equivalent one. This module hosts both the
//! value-free **set** variant ([`Table::aggregate_set`], implemented here) and, eventually, the
//! value-aware **map** (ORTC) variant. They share the bitmap primitives below.
//!
//! # The bit primitives
//!
//! Each [`MultiBitNode`](crate::node::MultiBitNode) holds a 31-bit data heap (bit `b`'s heap
//! children are `2b+1`/`2b+2`; levels: `0`=bit 0, `1`=bits 1..2, `2`=bits 3..6, `3`=bits 7..14,
//! `4`=bits 15..30) and 32 child sub-tries (a level-4 bit `15+j` has child sub-tries `2j`,`2j+1`).
//! Walking coverage up and down this heap in parallel is done with two mirrored `const fn`
//! families:
//!
//! * **fold-up** (children → parent): AND adjacent pairs, then compact toward the parent level.
//! * **push-down** (parent → children): spread the parent level, then duplicate into the children.
//!
//! Each primitive returns *only its contribution*; the caller accumulates. The leading `>>` and
//! trailing `<<` are merged into the constant masks (the scatter `&`/`|` between the two shifts
//! blocks the compiler's peephole, so we cannot rely on it). Fold-up needs no input mask (the AND
//! of an adjacent pair can never fabricate a bit outside the pair); push-down **does** need one,
//! since its global `<<` would otherwise drag deeper levels up into the target range.

use crate::{
    allocator::Loc,
    table::{DataIdx, EmptyMut, Table, K, NUM_CHILDREN, NUM_DATA},
};

// ===========================================================================
// FOLD-UP: AND adjacent pairs, compact toward the parent level.
// ===========================================================================

/// 32 child bits → level 4 (bits 15..30): child pair `(2j, 2j+1)` covers parent bit `15+j`.
#[inline(always)]
pub(crate) const fn fold_children(cc: u32) -> u32 {
    let p = cc & (cc >> 1) & 0x5555_5555;
    let p = (p | (p >> 1)) & 0x3333_3333;
    let p = (p | (p >> 2)) & 0x0F0F_0F0F;
    let p = (p | (p >> 4)) & 0x00FF_00FF;
    ((p | (p >> 8)) & 0x0000_FFFF) << 15
}

/// Level 4 (bits 15..30) → level 3 (bits 7..14).
#[inline(always)]
pub(crate) const fn fold_l4(cov: u32) -> u32 {
    let s = cov >> 8;
    let p = s & (s >> 1) & (0x5555 << 7);
    let p = (p | (p >> 1)) & (0x3333 << 7);
    let p = (p | (p >> 2)) & (0x0F0F << 7);
    (p | (p >> 4)) & (0x00FF << 7)
}

/// Level 3 (bits 7..14) → level 2 (bits 3..6).
#[inline(always)]
pub(crate) const fn fold_l3(cov: u32) -> u32 {
    let s = cov >> 4;
    let p = s & (s >> 1) & (0x55 << 3);
    let p = (p | (p >> 1)) & (0x33 << 3);
    (p | (p >> 2)) & (0x0F << 3)
}

/// Level 2 (bits 3..6) → level 1 (bits 1..2).
#[inline(always)]
pub(crate) const fn fold_l2(cov: u32) -> u32 {
    let s = cov >> 2;
    let p = s & (s >> 1) & (0x5 << 1);
    (p | (p >> 1)) & (0x3 << 1)
}

/// Level 1 (bits 1..2) → level 0 (bit 0).
#[inline(always)]
pub(crate) const fn fold_l1(cov: u32) -> u32 {
    (cov >> 1) & (cov >> 2) & 1
}

// ===========================================================================
// PUSH-DOWN: spread the parent level, duplicate into the children.
// The input is masked to the parent level first (see module docs).
// ===========================================================================

/// Bit 0 → bits 1..2.
#[inline(always)]
pub(crate) const fn push_l0(m: u32) -> u32 {
    let s = (m & 0b1) << 1;
    s | (s << 1)
}

/// Bits 1..2 → bits 3..6.
#[inline(always)]
pub(crate) const fn push_l1(m: u32) -> u32 {
    let s = (m & 0b110) << 2;
    let e = (s | (s << 1)) & (0x5 << 3);
    e | (e << 1)
}

/// Bits 3..6 → bits 7..14.
#[inline(always)]
pub(crate) const fn push_l2(m: u32) -> u32 {
    let s = (m & (0xF << 3)) << 4;
    let e = (s | (s << 2)) & (0x33 << 7);
    let e = (e | (e << 1)) & (0x55 << 7);
    e | (e << 1)
}

/// Bits 7..14 → bits 15..30.
#[inline(always)]
pub(crate) const fn push_l3(m: u32) -> u32 {
    let s = (m & (0xFF << 7)) << 8;
    let e = (s | (s << 4)) & (0x0F0F << 15);
    let e = (e | (e << 2)) & (0x3333 << 15);
    let e = (e | (e << 1)) & (0x5555 << 15);
    e | (e << 1)
}

/// Bits 15..30 → 32 child slots: parent bit `15+j` covers child pair `(2j, 2j+1)`.
#[inline(always)]
pub(crate) const fn push_l4(m: u32) -> u32 {
    let p = m >> 15;
    let e = (p | (p << 8)) & 0x00FF_00FF;
    let e = (e | (e << 4)) & 0x0F0F_0F0F;
    let e = (e | (e << 2)) & 0x3333_3333;
    let e = (e | (e << 1)) & 0x5555_5555;
    e | (e << 1)
}

impl Table<()> {
    /// Aggregate the sub-trie rooted at `loc` (a node at binary-tree `depth`) into its minimal
    /// prefix cover, in place.
    ///
    /// The minimal cover preserves the invariant that, for any prefix `p`,
    /// `before.get_lpm(p).is_some() == after.get_lpm(p).is_some()`: it (1) drops any prefix covered
    /// by an ancestor in the set, and (2) merges sibling pairs into their parent, cascading upward.
    ///
    /// Returns `(node_fully_covered, count_delta)`: whether this node's entire range is covered
    /// after aggregation (used by the parent's fold-up), and the signed change in the number of
    /// stored elements (so the map can fix up its cached `count`).
    ///
    /// # Safety
    /// `loc` must be a valid, live node location.
    pub(crate) unsafe fn aggregate_set(&mut self, loc: Loc, depth: u32) -> (bool, i64) {
        let node = *self.node(loc);
        let data_bitmap = node.data_bitmap();
        let mut count_delta: i64 = 0;

        // Push every member's coverage down through the heap. `covered_by_member` holds the data
        // bits whose strict ancestor in this node is a member, and `children_under_member` holds
        // the child slots sitting under such a member. A child under a member is redundant, so it
        // is never recursed into. Nothing is mutated here; this is pure analysis.
        let mut covered_by_member = 0u32;
        covered_by_member |= push_l0(data_bitmap | covered_by_member);
        covered_by_member |= push_l1(data_bitmap | covered_by_member);
        covered_by_member |= push_l2(data_bitmap | covered_by_member);
        covered_by_member |= push_l3(data_bitmap | covered_by_member);
        let children_under_member = push_l4(data_bitmap | covered_by_member);

        // Recurse into the children that are not already covered by a member, collecting which of
        // them end up fully covered.
        let mut child_coverage = 0u32;
        for child in node.child_locs() {
            let child_bit = child.bit;
            if children_under_member & (1 << child_bit) != 0 {
                continue;
            }
            // SAFETY: `child` comes from the snapshot of `loc`; recursing into a sibling only
            // touches that sibling's own sub-trie, never `loc`'s children allocation, so every
            // `child` location (and `loc` itself) stays valid across iterations.
            let (child_covered, child_delta) = unsafe { self.aggregate_set(child, depth + K) };
            count_delta += child_delta;
            if child_covered {
                child_coverage |= 1 << child_bit;
            }
        }

        // Fold coverage upward: `coverage` bit `b` means the whole range of `b` is covered, with
        // merges of adjacent siblings cascading up the levels.
        let mut coverage = data_bitmap;
        coverage |= fold_children(child_coverage);
        coverage |= fold_l4(coverage);
        coverage |= fold_l3(coverage);
        coverage |= fold_l2(coverage);
        coverage |= fold_l1(coverage);

        // Keep a covered bit only if no ancestor covers it. A covering ancestor is either
        // merge-covered, in which case its coverage reaches contiguously down to the immediate
        // parent (`parent_coverage`), or a member (`covered_by_member`).
        let parent_coverage =
            push_l0(coverage) | push_l1(coverage) | push_l2(coverage) | push_l3(coverage);
        let keep = coverage & !parent_coverage & !covered_by_member;

        // Drop the members that are no longer kept, highest bit first so lower bits keep their raw
        // offset while the data allocation compacts.
        let bits_to_remove = data_bitmap & !keep;
        for bit in (0..NUM_DATA as u32).rev() {
            if bits_to_remove & (1 << bit) != 0 {
                let data_idx = DataIdx {
                    node: loc,
                    bit,
                    depth,
                };
                // SAFETY: `bit` is set in the current bitmap, and data removals touch only `loc`'s
                // data allocation, leaving `loc` (in the parent's children allocation) valid.
                unsafe { data_idx.resolve_mut(self) }
                    .expect("aggregate_set: data bit not set")
                    .take();
                count_delta -= 1;
            }
        }

        // Add the merged prefixes that are kept but were not present before.
        let bits_to_insert = keep & !data_bitmap;
        for bit in 0..NUM_DATA as u32 {
            if bits_to_insert & (1 << bit) != 0 {
                EmptyMut {
                    table: self,
                    node: loc,
                    data_bit: bit,
                    depth,
                }
                .insert(());
                count_delta += 1;
            }
        }

        // Free every sub-trie that now sits under a kept prefix, whether covered by a member
        // (`children_under_member`) or by a merge (`push_l4(coverage)`). Each child is re-resolved
        // fresh because `remove_child_at` reallocates `loc`'s children allocation.
        let absorbed_children = (children_under_member | push_l4(coverage)) & node.child_bitmap();
        for child_bit in 0..NUM_CHILDREN as u32 {
            if absorbed_children & (1 << child_bit) != 0 {
                // SAFETY: `loc` is valid; `child` re-reads the current bitmap, so `child_location`
                // points into the live children allocation even after prior removals.
                unsafe {
                    if let Some(child_location) = self.child(loc, child_bit) {
                        count_delta -= self.clear_node_and_children(child_location) as i64;
                        self.remove_child_at(loc, child_bit);
                    }
                }
            }
        }

        (coverage & 1 != 0, count_delta)
    }
}

#[cfg(test)]
mod test {
    #![allow(clippy::unusual_byte_groupings)]
    use super::*;

    /// Build a bitmap from a list of set bits.
    fn bits(set: &[u32]) -> u32 {
        set.iter().fold(0, |acc, &b| acc | (1 << b))
    }

    #[test]
    fn fold_up_single_pairs() {
        // Each adjacent heap pair folds into its parent bit.
        assert_eq!(fold_l1(bits(&[1, 2])), bits(&[0]));
        assert_eq!(fold_l1(bits(&[1])), 0);
        assert_eq!(fold_l1(bits(&[2])), 0);

        assert_eq!(fold_l2(bits(&[3, 4])), bits(&[1]));
        assert_eq!(fold_l2(bits(&[5, 6])), bits(&[2]));
        assert_eq!(fold_l2(bits(&[3])), 0);

        assert_eq!(fold_l3(bits(&[7, 8])), bits(&[3]));
        assert_eq!(fold_l3(bits(&[13, 14])), bits(&[6]));
        assert_eq!(fold_l3(bits(&[7])), 0);

        assert_eq!(fold_l4(bits(&[15, 16])), bits(&[7]));
        assert_eq!(fold_l4(bits(&[29, 30])), bits(&[14]));
        assert_eq!(fold_l4(bits(&[15])), 0);

        // child pair (2j, 2j+1) -> data bit 15 + j
        assert_eq!(fold_children(bits(&[0, 1])), bits(&[15]));
        assert_eq!(fold_children(bits(&[2, 3])), bits(&[16]));
        assert_eq!(fold_children(bits(&[30, 31])), bits(&[30]));
        assert_eq!(fold_children(bits(&[0])), 0);
    }

    #[test]
    fn push_down_single_parents() {
        // Each parent bit pushes to its two heap children.
        assert_eq!(push_l0(bits(&[0])), bits(&[1, 2]));
        assert_eq!(push_l1(bits(&[1])), bits(&[3, 4]));
        assert_eq!(push_l1(bits(&[2])), bits(&[5, 6]));
        assert_eq!(push_l2(bits(&[3])), bits(&[7, 8]));
        assert_eq!(push_l2(bits(&[6])), bits(&[13, 14]));
        assert_eq!(push_l3(bits(&[7])), bits(&[15, 16]));
        assert_eq!(push_l3(bits(&[14])), bits(&[29, 30]));
        // data bit 15 + j -> child pair (2j, 2j+1)
        assert_eq!(push_l4(bits(&[15])), bits(&[0, 1]));
        assert_eq!(push_l4(bits(&[16])), bits(&[2, 3]));
        assert_eq!(push_l4(bits(&[30])), bits(&[30, 31]));
    }

    #[test]
    fn push_down_ignores_other_levels() {
        // A push function must only react to its own input level (masked input).
        assert_eq!(push_l0(bits(&[1, 2, 3])), 0);
        assert_eq!(push_l1(bits(&[0, 3, 4])), 0);
        assert_eq!(push_l2(bits(&[1, 2, 7])), 0);
        assert_eq!(push_l3(bits(&[0, 6, 15])), 0);
        assert_eq!(push_l4(bits(&[0, 7, 14])), 0);
    }

    #[test]
    fn fold_up_cascades_two_levels() {
        // Four level-2 siblings (bits 3,4,5,6) cascade to bit 0 via two folds.
        let cov = bits(&[3, 4, 5, 6]);
        let cov = cov | fold_l2(cov); // adds bits 1, 2
        assert_eq!(cov & bits(&[1, 2]), bits(&[1, 2]));
        let cov = cov | fold_l1(cov); // adds bit 0
        assert_eq!(cov & 1, 1);
    }

    #[test]
    fn fold_and_push_are_inverse_on_full_coverage() {
        // Folding a fully covered pair up and pushing it back down returns the pair.
        for j in 0..16u32 {
            let pair = bits(&[2 * j, 2 * j + 1]);
            let parent = fold_children(pair); // data bit 15 + j
            assert_eq!(push_l4(parent), pair);
        }
    }

    #[test]
    fn keep_drops_member_covered_bit() {
        // `{/22, /24}` in one node: bit 1 (a level-1 member) covers bit 7 (a level-3 member); the
        // level-2 (bit 3) between them is NOT a member, so a naive immediate-parent test would
        // wrongly keep bit 7. The `anc` mask catches it.
        let d = bits(&[1, 7]);
        let mut anc = 0u32;
        anc |= push_l0(d | anc);
        anc |= push_l1(d | anc);
        anc |= push_l2(d | anc);
        anc |= push_l3(d | anc);

        let mut cov = d;
        cov |= fold_l4(cov);
        cov |= fold_l3(cov);
        cov |= fold_l2(cov);
        cov |= fold_l1(cov);
        let cov_parent = push_l0(cov) | push_l1(cov) | push_l2(cov) | push_l3(cov);
        let keep = cov & !cov_parent & !anc;

        assert_eq!(keep, bits(&[1])); // only the /22 survives
    }

    #[test]
    fn keep_merges_siblings() {
        // Two level-3 siblings (bits 7, 8) merge into their parent bit 3; no members above (anc=0).
        let d = bits(&[7, 8]);
        let mut cov = d;
        cov |= fold_l4(cov);
        cov |= fold_l3(cov); // adds bit 3
        cov |= fold_l2(cov);
        cov |= fold_l1(cov);
        let cov_parent = push_l0(cov) | push_l1(cov) | push_l2(cov) | push_l3(cov);
        let keep = cov & !cov_parent;
        assert_eq!(keep, bits(&[3])); // merged level-2, children dropped
    }
}
