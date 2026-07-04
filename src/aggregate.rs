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

use std::cmp::Ordering;

use smallvec::{smallvec, SmallVec};

use crate::{
    allocator::Loc,
    node::{extend_repr, Key, MultiBitNode},
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

// ===========================================================================
// COVERAGE: composed push-down / fold-up sweeps over the whole heap.
// ===========================================================================

/// Find what an ancestor member in this node already covers. Returns `(covered,
/// children_under_member)`: `covered` are the data bits whose strict ancestor in this node is a
/// member, and `children_under_member` are the child slots sitting under such a member (their whole
/// sub-trie is redundant). Independent of values, so it serves both the set and the map aggregations.
#[inline(always)]
pub(crate) const fn member_coverage(data_bitmap: u32) -> (u32, u32) {
    let mut covered = 0u32;
    covered |= push_l0(data_bitmap | covered);
    covered |= push_l1(data_bitmap | covered);
    covered |= push_l2(data_bitmap | covered);
    covered |= push_l3(data_bitmap | covered);
    let children_under_member = push_l4(data_bitmap | covered);
    (covered, children_under_member)
}

/// Find which ranges are fully covered, with adjacent siblings merging into their parent. Bit `b`
/// of the result means the whole range of `b` is covered. `data_bitmap` are the members present in
/// this node and `child_coverage` are the child slots whose entire sub-trie is covered.
#[inline(always)]
pub(crate) const fn fold_coverage(data_bitmap: u32, child_coverage: u32) -> u32 {
    let mut coverage = data_bitmap | fold_children(child_coverage);
    coverage |= fold_l4(coverage);
    coverage |= fold_l3(coverage);
    coverage |= fold_l2(coverage);
    coverage |= fold_l1(coverage);
    coverage
}

/// Find which bits have their immediate heap parent covered: bit `b` of the result is set when
/// `b`'s parent is covered. Used to test whether a covered bit also has a covering ancestor reaching
/// contiguously down to it.
#[inline(always)]
pub(crate) const fn parent_coverage(coverage: u32) -> u32 {
    push_l0(coverage) | push_l1(coverage) | push_l2(coverage) | push_l3(coverage)
}

impl<T> Table<T> {
    /// Drop every data entry whose bit is set in `bits` from node `loc`, returning the (negative)
    /// change in stored-element count. `resolve_mut` recomputes each slot from the live bitmap, so
    /// the removal order is irrelevant.
    ///
    /// # Safety
    /// `loc` must be valid and every bit set in `bits` must be set in `loc`'s data bitmap.
    pub(crate) unsafe fn remove_data_bits(&mut self, loc: Loc, depth: u32, bits: u32) -> i64 {
        let mut count_delta: i64 = 0;
        for bit in 0..NUM_DATA as u32 {
            if bits & (1 << bit) != 0 {
                // SAFETY: `bit` is set in the current bitmap, and data removals touch only `loc`'s
                // data allocation, leaving `loc` (in the parent's children allocation) valid.
                unsafe {
                    DataIdx {
                        node: loc,
                        bit,
                        depth,
                    }
                    .resolve_mut(self)
                }
                .expect("remove_data_bits: data bit not set")
                .take();
                count_delta -= 1;
            }
        }
        count_delta
    }

    /// Free every child sub-trie whose slot is set in `child_bits` of node `loc`: clear the child
    /// and its descendants, then detach it. Returns the (negative) change in stored-element count.
    /// Each child is re-resolved fresh because `remove_child_at` reallocates `loc`'s children
    /// allocation.
    ///
    /// # Safety
    /// `loc` must be a valid, live node location.
    pub(crate) unsafe fn free_children(&mut self, loc: Loc, child_bits: u32) -> i64 {
        let mut count_delta: i64 = 0;
        for child_bit in 0..NUM_CHILDREN as u32 {
            if child_bits & (1 << child_bit) != 0 {
                // SAFETY: `loc` is valid; `child` re-reads the current bitmap, so `child_loc`
                // points into the live children allocation even after prior removals.
                unsafe {
                    if let Some(child_loc) = self.child(loc, child_bit) {
                        count_delta -= self.clear_node_and_children(child_loc) as i64;
                        self.remove_child_at(loc, child_bit);
                    }
                }
            }
        }
        count_delta
    }
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

        // `covered_by_member` are the data bits whose strict ancestor here is a member;
        // `children_under_member` are the child slots under such a member, redundant so never
        // recursed into. Nothing is mutated here; this is pure analysis.
        let (covered_by_member, children_under_member) = member_coverage(data_bitmap);

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

        let coverage = fold_coverage(data_bitmap, child_coverage);

        // Keep a covered bit only if no ancestor covers it. A covering ancestor is either
        // merge-covered, in which case its coverage reaches contiguously down to the immediate
        // parent (`parent_coverage`), or a member (`covered_by_member`).
        let keep = coverage & !parent_coverage(coverage) & !covered_by_member;

        // Drop the members that are no longer kept.
        // SAFETY: every dropped bit is set in `data_bitmap`, and `loc` is valid.
        count_delta += unsafe { self.remove_data_bits(loc, depth, data_bitmap & !keep) };

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
        // (`children_under_member`) or by a merge (`push_l4(coverage)`).
        let absorbed_children = (children_under_member | push_l4(coverage)) & node.child_bitmap();
        // SAFETY: `loc` is valid.
        count_delta += unsafe { self.free_children(loc, absorbed_children) };

        (coverage & 1 != 0, count_delta)
    }

    /// Drop-only aggregation of the sub-trie rooted at `loc`: remove every member that is already
    /// covered by an ancestor member, without merging anything.
    ///
    /// This preserves a stronger invariant than [`Self::aggregate_set`]: for *every* prefix `p`
    /// (not only addresses), `before.get_lpm(p).is_some() == after.get_lpm(p).is_some()` — a dropped
    /// member is always still covered by the ancestor that made it redundant.
    ///
    /// We only ever recurse into children that are *not* covered by a member here; a covered
    /// child's whole sub-trie is redundant and is freed outright. As a consequence a recursed node
    /// is never covered from above (its shallowest member always survives), so no `inherited` flag
    /// is needed and a recursed child can never come back empty.
    ///
    /// Returns the signed change in the number of stored elements.
    ///
    /// # Safety
    /// `loc` must be a valid, live node location.
    pub(crate) unsafe fn aggregate_consistent_set(&mut self, loc: Loc, depth: u32) -> i64 {
        let node = *self.node(loc);
        let data_bitmap = node.data_bitmap();
        let mut count_delta: i64 = 0;

        // `covered` are the data bits whose strict ancestor here is a member; `children_under_member`
        // are the child slots sitting under such a member (their entire sub-trie is redundant).
        let (covered, children_under_member) = member_coverage(data_bitmap);

        // Recurse only into children not covered by a member here.
        for child in node.child_locs() {
            if children_under_member & (1 << child.bit) != 0 {
                continue;
            }
            // SAFETY: `child` comes from the snapshot of `loc`; recursing into a sibling only
            // touches that sibling's own sub-trie, never `loc`'s own allocations, so every `child`
            // location (and `loc` itself) stays valid across iterations.
            count_delta += unsafe { self.aggregate_consistent_set(child, depth + K) };
        }

        // Drop the members covered by an ancestor member in this node.
        // SAFETY: every dropped bit is set in `data_bitmap`, and `loc` is valid.
        count_delta += unsafe { self.remove_data_bits(loc, depth, data_bitmap & covered) };

        // Free the sub-tries that sit under a member here.
        // SAFETY: `loc` is valid.
        count_delta += unsafe { self.free_children(loc, children_under_member) };

        count_delta
    }
}

impl<T: Clone + Eq> Table<T> {
    /// Find the covering value for each slot of the 31-slot heap, and whether the slot is redundant
    /// (the value-aware analog of [`member_coverage`]). Returns `(covering_value, redundant)`:
    ///
    /// * `covering_value[b]` is the value covering position `b` *including* `b`'s own member: the
    ///   member's value if `b` is present, otherwise the value reaching `b` from above. The value
    ///   covering `b` from *strictly* above is therefore `covering_value[parent(b)]` (or `inherited`
    ///   for `b == 0`).
    /// * `redundant` is the set of present members whose value equals the value covering them from
    ///   strictly above, i.e. the members an ancestor already accounts for.
    ///
    /// Parents have a smaller heap index than their children, so a single forward pass fills them
    /// first. No clones: the returned array borrows both `self` and `inherited`.
    ///
    /// # Safety
    /// `loc` must be valid and `data_bitmap` must be its live data bitmap.
    pub(crate) unsafe fn covering_values<'a>(
        &'a self,
        loc: Loc,
        depth: u32,
        data_bitmap: u32,
        inherited: Option<&'a T>,
    ) -> ([Option<&'a T>; NUM_DATA], u32) {
        let mut covering_value: [Option<&T>; NUM_DATA] = [None; NUM_DATA];
        let mut redundant = 0u32;
        for b in 0..NUM_DATA {
            let from_above = if b == 0 {
                inherited
            } else {
                covering_value[(b - 1) / 2]
            };
            covering_value[b] = if data_bitmap & (1 << b) != 0 {
                // SAFETY: bit `b` is set and the node is unmodified during this read scan.
                let present = unsafe {
                    DataIdx {
                        node: loc,
                        bit: b as u32,
                        depth,
                    }
                    .resolve(self)
                }
                .expect("covering_values: data bit not set");
                let val = present.get();
                if Some(val) == from_above {
                    redundant |= 1 << b;
                }
                Some(val)
            } else {
                from_above
            };
        }
        (covering_value, redundant)
    }

    /// The covering value handed to each present child of `node`, as owned clones (the only clones a
    /// value-aware aggregation makes). Child slot `c` sits below level-4 data bit `15 + c / 2`, so it
    /// is covered by `covering_value[15 + c / 2]`; absent children get `None`.
    pub(crate) fn child_cover(
        node: &MultiBitNode,
        covering_value: &[Option<&T>; NUM_DATA],
    ) -> [Option<T>; NUM_CHILDREN] {
        std::array::from_fn(|c| {
            if node.has_child_bit(c as u32) {
                covering_value[15 + c / 2].cloned()
            } else {
                None
            }
        })
    }

    /// Drop-only, value-aware aggregation of the sub-trie rooted at `loc`: remove every entry whose
    /// nearest covering ancestor entry has the **same value**, without merging anything.
    ///
    /// Preserves a stronger invariant than the merging `aggregate`: for every prefix `p`,
    /// `before.get_lpm(p)` and `after.get_lpm(p)` yield the same value (and `Some`/`None`); only the
    /// matched prefix may change. Unlike the set variant we recurse into *every* child, because a
    /// covered child may still hold a differing-value entry that must survive.
    ///
    /// `inherited` is the value of the nearest covering ancestor entry (`None` if uncovered), passed
    /// by owned clone so no borrow of `self` is held across the recursion. Returns
    /// `(node_is_now_empty, count_delta)`: the first tells the caller to free this node, the second
    /// is the signed change in the number of stored elements.
    ///
    /// # Safety
    /// `loc` must be a valid, live node location.
    pub(crate) unsafe fn aggregate_consistent_map(
        &mut self,
        loc: Loc,
        depth: u32,
        inherited: Option<T>,
    ) -> (bool, i64) {
        let node = *self.node(loc);
        let data_bitmap = node.data_bitmap();
        let mut count_delta: i64 = 0;

        // Drop-only: an entry is redundant exactly when it equals its strict-ancestor covering value.
        // SAFETY: `data_bitmap` is `loc`'s live bitmap and the node is unmodified during this read.
        let (covering_value, bits_to_remove) =
            unsafe { self.covering_values(loc, depth, data_bitmap, inherited.as_ref()) };

        // The covering value handed to each present child (the only clones we make).
        let mut child_cover = Self::child_cover(&node, &covering_value);

        // Recurse into every child, then free the ones that came back empty, in a single pass.
        // (`covering_value` is dropped here: its last use was building `child_cover`, releasing the
        // shared borrow of `self`.) We iterate by `child_bit` and re-resolve `self.child(..)` each step
        // because `remove_child_at` reallocates `loc`'s children allocation.
        for child_bit in 0..NUM_CHILDREN as u32 {
            // SAFETY: `loc` is valid; `child` re-reads the current bitmap.
            if let Some(child_loc) = unsafe { self.child(loc, child_bit) } {
                let child_inherited = child_cover[child_bit as usize].take();
                // SAFETY: `child_loc` was just resolved; recursing only touches that child's
                // sub-trie, never `loc`'s allocations beyond what we free below.
                let (child_empty, delta) =
                    unsafe { self.aggregate_consistent_map(child_loc, depth + K, child_inherited) };
                count_delta += delta;
                if child_empty {
                    // SAFETY: an empty node owns no data/children allocations, so detaching it from
                    // `loc` (which compacts it out of `loc`'s children block) fully frees it.
                    unsafe { self.remove_child_at(loc, child_bit) };
                }
            }
        }

        // Drop the redundant entries.
        // SAFETY: every bit in `bits_to_remove` is set in `data_bitmap`, and `loc` is valid.
        count_delta += unsafe { self.remove_data_bits(loc, depth, bits_to_remove) };

        // Report whether this node is now empty, so the caller can free it.
        let node = self.node(loc);
        let empty = node.data_bitmap() == 0 && node.child_bitmap() == 0;
        (empty, count_delta)
    }
}

// ===========================================================================
// ORTC: value-aware `aggregate` and `aggregate_ortc`.
// ===========================================================================

/// A sorted, deduplicated candidate value set. Up to `INLINE` values live inline (no allocation);
/// larger sets spill to the heap.
const INLINE: usize = 4;
type Values<T> = SmallVec<[T; INLINE]>;

/// Intersection of two sorted, deduplicated slices, itself sorted and deduplicated.
fn intersect_sorted<T: Ord + Clone>(l: &[T], r: &[T]) -> Values<T> {
    let mut out = Values::new();
    let (mut i, mut j) = (0, 0);
    while i < l.len() && j < r.len() {
        match l[i].cmp(&r[j]) {
            Ordering::Less => i += 1,
            Ordering::Greater => j += 1,
            Ordering::Equal => {
                out.push(l[i].clone());
                i += 1;
                j += 1;
            }
        }
    }
    out
}

/// Union of two sorted, deduplicated slices, itself sorted and deduplicated.
fn union_sorted<T: Ord + Clone>(l: &[T], r: &[T]) -> Values<T> {
    let mut out = Values::new();
    let (mut i, mut j) = (0, 0);
    while i < l.len() && j < r.len() {
        match l[i].cmp(&r[j]) {
            Ordering::Less => {
                out.push(l[i].clone());
                i += 1;
            }
            Ordering::Greater => {
                out.push(r[j].clone());
                j += 1;
            }
            Ordering::Equal => {
                out.push(l[i].clone());
                i += 1;
                j += 1;
            }
        }
    }
    out.extend(l[i..].iter().cloned());
    out.extend(r[j..].iter().cloned());
    out
}

/// A position's ORTC candidate set.
///
/// `ContainsHole` is absorbing under [`CandidateSet::combine`]: once a region contains uncovered
/// space, no single covering value may represent it. This is exactly what lets `aggregate` never
/// cover a hole (a flat set of `Option<T>` would drop the hole on an intersection).
///
/// `Covered` holds the candidate values sorted, deduplicated, and (for small sets) inline, so a
/// single-value position needs no allocation and `min(S)` is just the first element.
#[derive(Clone, PartialEq, Eq)]
enum CandidateSet<T> {
    /// The region contains uncovered space; no covering entry may be placed at or above it.
    ContainsHole,
    /// The region is fully covered; these are the candidate values (sorted, non-empty).
    Covered(Values<T>),
}

impl<T: Clone + Ord> CandidateSet<T> {
    /// A candidate set covering a single value.
    fn one(value: T) -> Self {
        Self::Covered(smallvec![value])
    }

    /// The candidate set of the parent of two positions: `l ∩ r` if non-empty, else `l ∪ r`; a hole
    /// in either child poisons the result.
    fn combine(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::ContainsHole, _) | (_, Self::ContainsHole) => Self::ContainsHole,
            (Self::Covered(l), Self::Covered(r)) => {
                let intersection = intersect_sorted(l, r);
                Self::Covered(if intersection.is_empty() {
                    union_sorted(l, r)
                } else {
                    intersection
                })
            }
        }
    }
}

/// The single knob distinguishing the two aggregations: what an uncovered leaf forwards to.
///
/// `Fill` carries a copyable factory producing the default value on demand.
#[derive(Clone, Copy)]
pub(crate) enum Aggregation<F> {
    /// `aggregate`: uncovered space stays uncovered.
    Drop,
    /// `aggregate_ortc`: uncovered space forwards to `F()`.
    Fill(F),
}

impl<T: Clone + Ord, F: Fn() -> T + Copy> Aggregation<F> {
    /// The candidate set of a leaf whose covering value from above is `covering`.
    fn leaf_set(self, covering: Option<&T>) -> CandidateSet<T> {
        match (covering, self) {
            (Some(v), _) => CandidateSet::one(v.clone()),
            (None, Aggregation::Drop) => CandidateSet::ContainsHole,
            (None, Aggregation::Fill(f)) => CandidateSet::one(f()),
        }
    }

    /// The single value a uniform leaf region forwards to (the scalar form of [`Self::leaf_set`]).
    fn leaf_value(self, covering: Option<&T>) -> Option<T> {
        match (covering, self) {
            (Some(v), _) => Some(v.clone()),
            (None, Aggregation::Drop) => None,
            (None, Aggregation::Fill(f)) => Some(f()),
        }
    }
}

/// Candidate sets from Walk A, consumed by Walk B in reverse order.
///
/// Two coupled append-only stacks replace what used to be a keyed map. `sets` holds one
/// [`CandidateSet`] for every *stored* heap position; `node_masks` holds one bitmap per node marking
/// which of its 31 heap bits were stored (bit 0 is always stored, so every node contributes exactly
/// one mask). No position keys are needed: Walk A appends nodes in reverse pre-order (it recurses
/// children back-to-front) and Walk B pops in pre-order, so the top of each stack is always the exact
/// position Walk B is visiting.
///
/// Walk A writes a node through [`ChangeSets::node_writer`], pushing its stored bits in *descending*
/// order and committing the mask; Walk B reads a node through [`ChangeSets::node_reader`], popping the
/// mask on entry and then one set per stored bit in *ascending* order. The two walks are coupled by
/// this ordering (see [`Table::collect_sets`] / [`Table::rewrite`]); the aggregation tests cover it.
struct ChangeSets<T> {
    /// One candidate set per stored heap position, in reverse pre-order (popped front-to-back).
    sets: Vec<CandidateSet<T>>,
    /// One stored-bits bitmap per node, in reverse pre-order (popped as each node is entered).
    node_masks: Vec<u32>,
}

impl<T> ChangeSets<T> {
    #[inline]
    fn new() -> Self {
        Self {
            sets: Vec::new(),
            node_masks: Vec::new(),
        }
    }

    /// Whether both stacks have been fully consumed.
    #[inline]
    fn is_empty(&self) -> bool {
        self.sets.is_empty() && self.node_masks.is_empty()
    }

    /// Begin writing one node's stored positions (Walk A).
    #[inline]
    fn node_writer(&mut self) -> NodeWriter<'_, T> {
        NodeWriter {
            store: self,
            mask: 0,
        }
    }

    /// Begin reading one node's stored positions (Walk B), popping its stored-bits mask.
    #[inline]
    fn node_reader(&mut self) -> NodeReader<'_, T> {
        let mask = self.node_masks.pop().expect("one node mask per node");
        NodeReader { store: self, mask }
    }
}

/// Writes the stored candidate sets of a single node (Walk A), accumulating its stored-bits mask.
struct NodeWriter<'a, T> {
    store: &'a mut ChangeSets<T>,
    mask: u32,
}

impl<T> NodeWriter<'_, T> {
    /// Store the candidate set of heap bit `bit`. Bits must be pushed in *descending* order.
    #[inline]
    fn push(&mut self, bit: usize, set: CandidateSet<T>) {
        self.mask |= 1 << bit;
        self.store.sets.push(set);
    }

    /// Commit the node's stored-bits mask.
    #[inline]
    fn finish(self) {
        self.store.node_masks.push(self.mask);
    }
}

/// Reads the stored candidate sets of a single node (Walk B).
struct NodeReader<'a, T> {
    store: &'a mut ChangeSets<T>,
    mask: u32,
}

impl<T> NodeReader<'_, T> {
    /// Whether heap bit `bit` has a stored candidate set.
    #[inline]
    fn stored(&self, bit: usize) -> bool {
        self.mask & (1 << bit) != 0
    }

    /// Take the candidate set of the next stored bit. Call once per stored bit, in *ascending* order.
    #[inline]
    fn pop(&mut self) -> CandidateSet<T> {
        self.store.sets.pop().expect("one set per stored bit")
    }
}

impl<T: Clone + Ord> Table<T> {
    /// Rewrite the trie into an equivalent minimal one (ORTC, Draves and King). `mode` chooses
    /// whether uncovered space stays uncovered (`aggregate`) or is filled with a default
    /// (`aggregate_ortc`).
    ///
    /// Returns the change in the number of stored entries, as a signed `i64` for the caller to add
    /// to its `count`.
    ///
    /// For [`Aggregation::Drop`] this is always `<= 0`: forwarding is preserved exactly, so the
    /// original is already a valid representation and the minimal result is never larger.
    ///
    /// For [`Aggregation::Fill`] it is `<= 1`: filling previously-uncovered space with the default
    /// may add a single default route (the `/0`; an empty map becomes one `/0` entry, `+1`), while
    /// every other emitted entry only replaces or merges existing ones.
    pub(crate) fn aggregate_map<R, F>(&mut self, mode: Aggregation<F>) -> i64
    where
        R: Key,
        F: Fn() -> T + Copy,
    {
        let mut sets: ChangeSets<T> = ChangeSets::new();

        // Walk A (bottom-up): candidate set per position, appended in descending position order.
        // SAFETY: the root node always exists.
        unsafe { self.collect_sets(Loc::root(), 0, None, mode, &mut sets) };

        // Walk B (top-down): assign a value to every position and edit the trie to match. The value
        // above the root is `None`, so the /0 position itself decides whether a default route is
        // emitted. Walk B pops `sets` from the back, which visits the positions in ascending order.
        // SAFETY: the root exists; `sets` describes the same trie we are about to edit.
        let delta = unsafe { self.rewrite(Loc::root(), 0, R::zero(), None, None, mode, &mut sets) };
        debug_assert!(
            sets.is_empty(),
            "every stored change-set must be consumed exactly once"
        );
        delta
    }

    /// Walk A. Fills `sets` and returns the candidate set for the subtree rooted at `loc`.
    ///
    /// # Safety
    /// `loc` must be a valid, live node location.
    unsafe fn collect_sets<F>(
        &self,
        loc: Loc,
        depth: u32,
        covering_inherited: Option<&T>,
        mode: Aggregation<F>,
        sets: &mut ChangeSets<T>,
    ) -> CandidateSet<T>
    where
        F: Fn() -> T + Copy,
    {
        let node = *self.node(loc);
        // SAFETY: `data_bitmap` is `loc`'s live bitmap and the node is unmodified during this read.
        let (covering_value, _) =
            unsafe { self.covering_values(loc, depth, node.data_bitmap(), covering_inherited) };

        // The candidate set at each of the 32 child slots: recurse into a present child, or take the
        // leaf set of the uniform region an absent slot covers. We recurse *back-to-front* so that
        // the child sub-trie sets are appended to `sets` in descending position order.
        let mut child_sets: [Option<CandidateSet<T>>; NUM_CHILDREN] = std::array::from_fn(|_| None);
        for c in (0..NUM_CHILDREN).rev() {
            let covering = covering_value[15 + c / 2];
            // SAFETY: `loc` is valid; the child resolves from the live, unmodified node.
            let set = if let Some(child) = unsafe { self.child(loc, c as u32) } {
                unsafe { self.collect_sets(child, depth + K, covering, mode, sets) }
            } else {
                mode.leaf_set(covering)
            };
            child_sets[c] = Some(set);
        }

        // Fold the 31-bit internal nodes: level-4 bits from child-slot pairs, then the rest bottom-up.
        let mut node_sets: [Option<CandidateSet<T>>; NUM_DATA] = std::array::from_fn(|_| None);
        for j in 0..16 {
            let merged = child_sets[2 * j]
                .as_ref()
                .unwrap()
                .combine(child_sets[2 * j + 1].as_ref().unwrap());
            node_sets[15 + j] = Some(merged);
        }
        for b in (0..15).rev() {
            let merged = node_sets[2 * b + 1]
                .as_ref()
                .unwrap()
                .combine(node_sets[2 * b + 2].as_ref().unwrap());
            node_sets[b] = Some(merged);
        }

        // Append this node's positions after its children (so its bits sort after them), in
        // descending order: the internal bits `30..1` that differ from their in-node parent, then
        // bit 0 unconditionally (bit 0 has no in-node parent, so every node stores its own root set;
        // Walk B always finds it and never needs a set carried across the node boundary).
        let mut writer = sets.node_writer();
        for b in (1..NUM_DATA).rev() {
            if node_sets[b] != node_sets[(b - 1) / 2] {
                writer.push(b, node_sets[b].take().unwrap());
            }
        }
        let root_set = node_sets[0].take().unwrap();
        writer.push(0, root_set.clone());
        writer.finish();
        root_set
    }

    /// Walk B. Edits the subtree rooted at `loc` to match the ORTC assignment; returns the signed
    /// change in the number of stored entries.
    ///
    /// # Safety
    /// `loc` must be a valid, live node location.
    #[allow(clippy::too_many_arguments)]
    unsafe fn rewrite<R, F>(
        &mut self,
        loc: Loc,
        depth: u32,
        key: R,
        assigned_from_above: Option<&T>,
        covering_inherited: Option<&T>,
        mode: Aggregation<F>,
        sets: &mut ChangeSets<T>,
    ) -> i64
    where
        R: Key,
        F: Fn() -> T + Copy,
    {
        let node = *self.node(loc);
        // SAFETY: `data_bitmap` is `loc`'s live bitmap and the node is unmodified at this point.
        let (covering_value, _) =
            unsafe { self.covering_values(loc, depth, node.data_bitmap(), covering_inherited) };
        // Snapshot the covering value of each of the 16 level-4 bits before we start mutating.
        let child_covering: [Option<T>; 16] =
            std::array::from_fn(|j| covering_value[15 + j].cloned());

        // Walk the heap top-down: assign every bit and edit its entry.
        // SAFETY: `loc` is valid and `node` is its snapshot.
        let (assigned, mut delta) =
            unsafe { self.assign_nodes(&node, loc, depth, assigned_from_above, sets) };

        // Recurse into each child slot, inheriting the assignment of the level-4 bit above it.
        for c in 0..NUM_CHILDREN {
            let above = 15 + c / 2;
            // SAFETY: `loc` is valid.
            delta += unsafe {
                self.rewrite_child(
                    loc,
                    depth,
                    key,
                    c,
                    assigned[above].as_ref(),
                    child_covering[c / 2].as_ref(),
                    mode,
                    sets,
                )
            };
        }

        delta
    }

    /// Assign a value to every bit of `node`, top-down, editing entries as it goes.
    ///
    /// Returns the value assigned per bit and the count delta. The node's [`NodeReader`] yields its
    /// stored-bits mask up front; this loop (bits `0..31`, ascending) pops one set from the reader for
    /// each stored bit, in the order Walk A pushed them, and bit 0 is always stored. A bit that is
    /// *not* stored has the same set as its in-node parent, so it always inherits the parent's
    /// assigned value; only its (possibly present) entry has to be dropped.
    ///
    /// The assigned values are owned: they are cloned out of the candidate sets so that Walk B can
    /// keep consuming `sets` as it descends. For a `Copy` `T` this is essentially free; for an
    /// expensive `T` it is the price of not holding references into `sets`.
    ///
    /// # Safety
    /// `loc` must be valid and `node` must be its live snapshot.
    unsafe fn assign_nodes(
        &mut self,
        node: &MultiBitNode,
        loc: Loc,
        depth: u32,
        assigned_from_above: Option<&T>,
        sets: &mut ChangeSets<T>,
    ) -> ([Option<T>; NUM_DATA], i64) {
        let mut assigned: [Option<T>; NUM_DATA] = std::array::from_fn(|_| None);
        let mut delta = 0;
        let mut reader = sets.node_reader();
        for b in 0..NUM_DATA {
            let parent_assigned = if b == 0 {
                assigned_from_above
            } else {
                assigned[(b - 1) / 2].as_ref()
            };
            if reader.stored(b) {
                let set = reader.pop();
                // SAFETY: `loc` is valid and `node` is its snapshot.
                let (value, d) =
                    unsafe { self.rewrite_bit(node, loc, depth, b, parent_assigned, set) };
                assigned[b] = value;
                delta += d;
            } else {
                // Not stored: this bit's set equals its in-node parent's, so it inherits. Drop any
                // entry sitting here. (Bit 0 is always stored, so `b != 0` here.)
                let present = node.has_data_bit(b as u32);
                // SAFETY: `loc` is valid and `node` is its snapshot.
                delta += unsafe { self.rewrite_bit_remove(loc, depth, b, present) };
                assigned[b] = parent_assigned.cloned();
            }
        }
        (assigned, delta)
    }

    /// Assign heap bit `b` and edit its entry. Returns `(assigned_value, count_delta)`, the assigned
    /// value borrowed from the candidate set.
    ///
    /// # Safety
    /// `loc` must be valid and `node` must be its live snapshot.
    unsafe fn rewrite_bit(
        &mut self,
        node: &MultiBitNode,
        loc: Loc,
        depth: u32,
        b: usize,
        parent_assigned: Option<&T>,
        set: CandidateSet<T>,
    ) -> (Option<T>, i64) {
        let present = node.has_data_bit(b as u32);
        match set {
            // A hole is never covered, so no entry can sit here.
            CandidateSet::ContainsHole => {
                debug_assert!(!present, "a hole position never holds an entry");
                (None, 0)
            }

            // Inherit: the covering ancestor already forwards a value in the set; drop any entry.
            CandidateSet::Covered(s) if parent_assigned.is_some_and(|v| s.contains(v)) => {
                (parent_assigned.cloned(), unsafe {
                    self.rewrite_bit_remove(loc, depth, b, present)
                })
            }

            // Otherwise emit `min(s)` (the first element of the sorted set) here, moving it into the
            // assignment (the one clone goes to the trie).
            CandidateSet::Covered(s) => {
                let winner = s.into_iter().next().expect("Covered holds a non-empty set");
                self.rewrite_bit_insert(loc, depth, b, present, winner)
            }
        }
    }

    /// Remove the value at the given position, returning the delta in number of elements.
    ///
    /// # Safety
    /// `loc` must be valid and `node` must be its live snapshot.
    #[inline]
    unsafe fn rewrite_bit_remove(&mut self, loc: Loc, depth: u32, b: usize, present: bool) -> i64 {
        if !present {
            return 0;
        }
        // SAFETY: bit `b` is set; `resolve_mut` re-reads the live bitmap.
        unsafe {
            DataIdx {
                node: loc,
                bit: b as u32,
                depth,
            }
            .resolve_mut(self)
        }
        .expect("rewrite: data bit not set")
        .take();
        -1
    }

    /// replace the value at the given position, returning the new value and the delta in number of
    /// elements.
    ///
    /// # Safety
    /// `loc` must be valid and `node` must be its live snapshot.
    #[inline]
    unsafe fn rewrite_bit_insert(
        &mut self,
        loc: Loc,
        depth: u32,
        b: usize,
        present: bool,
        winner: T,
    ) -> (Option<T>, i64) {
        if present {
            // SAFETY: bit `b` is set; `resolve_mut` re-reads the live bitmap.
            unsafe {
                DataIdx {
                    node: loc,
                    bit: b as u32,
                    depth,
                }
                .resolve_mut(self)
            }
            .expect("rewrite: data bit not set")
            .replace(winner.clone());
            (Some(winner), 0)
        } else {
            EmptyMut {
                table: self,
                node: loc,
                data_bit: b as u32,
                depth,
            }
            .insert(winner.clone());
            (Some(winner), 1)
        }
    }

    /// Rewrite child slot `c`: recurse into a present child, freeing it if the rewrite empties it,
    /// or pin an absent uniform region with one entry when its value differs from the inherited one.
    /// Returns the count delta.
    ///
    /// # Safety
    /// `loc` must be valid.
    #[allow(clippy::too_many_arguments)]
    unsafe fn rewrite_child<R, F>(
        &mut self,
        loc: Loc,
        depth: u32,
        key: R,
        c: usize,
        assigned_above: Option<&T>,
        covering: Option<&T>,
        mode: Aggregation<F>,
        sets: &mut ChangeSets<T>,
    ) -> i64
    where
        R: Key,
        F: Fn() -> T + Copy,
    {
        // SAFETY: `loc` is valid; the child is resolved from the live node.
        if let Some(child_loc) = unsafe { self.child(loc, c as u32) } {
            let child_key = extend_repr(key, depth, c as u32);
            // SAFETY: `child_loc` was just resolved; the recursion only touches its own sub-trie.
            let delta = unsafe {
                self.rewrite(
                    child_loc,
                    depth + K,
                    child_key,
                    assigned_above,
                    covering,
                    mode,
                    sets,
                )
            };
            let child = self.node(child_loc);
            if child.data_bitmap() == 0 && child.child_bitmap() == 0 {
                // SAFETY: an empty node owns no allocations; detaching it fully frees it.
                unsafe { self.remove_child_at(loc, c as u32) };
            }
            delta
        } else if let Some(value) = mode.leaf_value(covering) {
            // Absent slot: a uniform region forwarding `value`. Needs an entry only when it would
            // otherwise inherit something else.
            if Some(&value) == assigned_above {
                return 0;
            }
            let child_key = extend_repr(key, depth, c as u32);
            match self.find_or_insert_mut(child_key, depth + K) {
                Ok(present) => {
                    present.replace(value);
                    0
                }
                Err(empty) => {
                    empty.insert(value);
                    1
                }
            }
        } else {
            0
        }
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
