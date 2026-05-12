use std::{
    cell::UnsafeCell,
    mem::{replace, MaybeUninit},
    ops::{Index, IndexMut},
};

use crate::node::MultiBitNode;

/// Spacing for data allocations (tiers by capacity)
pub(crate) const DATA_SPACING: [usize; 6] = [1, 2, 4, 8, 16, 31];
/// Spacing for children allocations (tiers by capacity)
pub(crate) const CHILD_SPACING: [usize; 6] = [1, 2, 4, 8, 16, 32];

/// Map count -> tier index for data (indices 0..=31)
pub(crate) const DATA_COUNT_TO_TIER: [u8; 32] = build_count_to_tier_data();
/// Map count -> tier index for children (indices 0..=32)
pub(crate) const CHILD_COUNT_TO_TIER: [u8; 33] = build_count_to_tier_child();

const fn build_count_to_tier_data() -> [u8; 32] {
    let mut table = [0u8; 32];
    let mut count = 0;
    while count < 32 {
        let mut tier = 0;
        while tier + 1 < DATA_SPACING.len() && DATA_SPACING[tier] < count {
            tier += 1;
        }
        table[count] = tier as u8;
        count += 1;
    }
    table
}

const fn build_count_to_tier_child() -> [u8; 33] {
    let mut table = [0u8; 33];
    let mut count = 0;
    while count < 33 {
        let mut tier = 0;
        while tier + 1 < CHILD_SPACING.len() && CHILD_SPACING[tier] < count {
            tier += 1;
        }
        table[count] = tier as u8;
        count += 1;
    }
    table
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub(crate) struct AllocIdx(u32);

/// Compute the physical (compact) slot from a bitmap bit position.
/// Used consistently throughout to avoid repeated POPCNT calculations.
#[inline]
pub(crate) fn compute_slot(bitmap: u32, bit: u32) -> u32 {
    (bitmap & ((1u32 << bit) - 1)).count_ones()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Loc {
    pub(crate) idx: AllocIdx,
    pub(crate) bit: u32, // bitmap bit position (0..32); meaningless for plain node-array indices
    pub(crate) slot: u32, // physical (compact) slot, computed from bitmap
}

impl Loc {
    /// Create a new Loc by computing the physical slot from a bitmap bit position and bitmap.
    pub(crate) fn new(idx: AllocIdx, bit: u32, bitmap: u32) -> Self {
        let slot = compute_slot(bitmap, bit);
        Self { idx, bit, slot }
    }

    /// Create a Loc that indexes directly by slot (no associated bitmap bit).
    /// Use this when navigating the node allocator by physical slot alone.
    pub(crate) fn at_slot(idx: AllocIdx, slot: u32) -> Self {
        Self { idx, bit: 0, slot }
    }

    pub(crate) fn root() -> Self {
        Self {
            idx: AllocIdx::from_usize(0),
            bit: 0,
            slot: 0,
        }
    }

    pub(crate) fn is_root(&self) -> bool {
        self.idx == Self::root().idx && self.slot == 0
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.idx.is_empty()
    }
}

impl std::fmt::Debug for AllocIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_empty() {
            f.debug_tuple("Empty").finish()
        } else {
            f.debug_tuple("Idx").field(&self.0).finish()
        }
    }
}

impl Default for AllocIdx {
    fn default() -> Self {
        Self::empty()
    }
}

impl AllocIdx {
    #[inline(always)]
    pub(crate) fn is_empty(self) -> bool {
        self.0 == u32::MAX
    }

    #[inline(always)]
    pub(crate) fn as_usize(self) -> usize {
        debug_assert!(!self.is_empty());
        self.0 as usize
    }

    #[inline(always)]
    pub(crate) fn empty() -> Self {
        Self(u32::MAX)
    }

    #[inline(always)]
    pub(crate) fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }
}

pub(crate) type RawPtr<T> = *mut MaybeUninit<T>;

pub(crate) struct CellAllocator<T> {
    data: UnsafeCell<Vec<MaybeUninit<T>>>,
    free_lists: [Vec<u32>; 6], // one free list per tier
}

impl<T> Default for CellAllocator<T> {
    fn default() -> Self {
        Self {
            data: UnsafeCell::new(Vec::new()),
            free_lists: Default::default(),
        }
    }
}

impl<T> CellAllocator<T> {
    pub(crate) fn mem_size(&self) -> usize {
        // SAFETY: We only read the Vec's metadata (capacity), not any uninitialized elements.
        // No mutable reference to self.data exists, so shared access via get() is sound.
        unsafe {
            self.data.get().as_ref().unwrap().capacity() * std::mem::size_of::<MaybeUninit<T>>()
                + self
                    .free_lists
                    .iter()
                    .map(|fl| fl.capacity() * std::mem::size_of::<u32>())
                    .sum::<usize>()
        }
    }

    pub(crate) fn raw_ptr(&mut self) -> RawPtr<T> {
        self.data.get_mut().as_mut_ptr()
    }

    /// Read a value at the given location.
    /// SAFETY:
    /// - The entry at `idx` + `slot` must have been initialized.
    /// - `slot` must equal `compute_slot(bitmap, bit)` for the bitmap from the corresponding node,
    ///   where the bitmap bit at `bit` is set (indicating the entry is present).
    #[inline(always)]
    pub(crate) unsafe fn get(&self, loc: Loc) -> &T {
        debug_assert!(!loc.idx.is_empty());
        let ptr = (self.data.get() as *const Vec<MaybeUninit<T>>)
            .as_ref()
            .unwrap_unchecked();
        ptr[loc.idx.as_usize() + loc.slot as usize].assume_init_ref()
    }

    /// Read a mutable value at the given location.
    /// SAFETY:
    /// - The entry at `idx` + `slot` must have been initialized.
    /// - `slot` must equal `compute_slot(bitmap, bit)` where the bitmap bit at `bit` is set.
    #[inline(always)]
    pub(crate) unsafe fn get_mut(&mut self, loc: Loc) -> &mut T {
        debug_assert!(!loc.idx.is_empty());
        self.data.get_mut()[loc.idx.as_usize() + loc.slot as usize].assume_init_mut()
    }

    /// SAFETY:
    /// - The entry at `idx` + `slot` must have been initialized.
    /// - `slot` must equal `compute_slot(bitmap, bit)` where the bitmap bit at `bit` is set.
    /// - Standard mutable reference invariants: no other references to this location exist during 'a.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub(crate) unsafe fn unsafe_get_mut(&self, ptr: &mut RawPtr<T>, loc: Loc) -> &mut T {
        let elem = ptr.add(loc.idx.as_usize() + loc.slot as usize);
        &mut *elem
            .cast::<MaybeUninit<T>>()
            .as_mut()
            .unwrap()
            .assume_init_mut()
    }

    /// Write a value at the given location (must be empty).
    /// SAFETY:
    /// - The entry at `idx` + `slot` must be uninitialized.
    /// - `slot` must be the correct physical (compact) position where the entry should be written,
    ///   typically computed as `compute_slot(bitmap, bit)` before calling this.
    pub(crate) unsafe fn write_at(&mut self, idx: AllocIdx, slot: u32, val: T) {
        self.data.get_mut()[idx.as_usize() + slot as usize].write(val);
    }

    /// Replace and return a value at the given location.
    /// SAFETY:
    /// - The entry at `idx` + `slot` must have been initialized.
    /// - `slot` must equal `compute_slot(bitmap, bit)` where the bitmap bit at `bit` is set.
    pub(crate) unsafe fn replace(&mut self, loc: Loc, val: T) -> T {
        replace(
            &mut self.data.get_mut()[loc.idx.as_usize() + loc.slot as usize],
            MaybeUninit::new(val),
        )
        .assume_init()
    }

    /// Remove and return a value at the given location. This function does *not* shift data around.
    /// The resulting state is likely inconsistent.
    ///
    /// SAFETY:
    /// - The entry at `idx` + `slot` must have been initialized.
    /// - `slot` must equal `compute_slot(bitmap, bit)` where the bitmap bit at `bit` is set.
    /// - There is no subsequent read of the same location, but the bitmap to compute the slot is
    ///   not modified, so accesses to other items still get routed to the correct slot.
    pub(crate) unsafe fn remove_raw(&mut self, loc: Loc) -> T {
        replace(
            &mut self.data.get_mut()[loc.idx.as_usize() + loc.slot as usize],
            MaybeUninit::uninit(),
        )
        .assume_init()
    }

    /// Allocate a new group of given capacity tier. Returns AllocIdx to the start of the group.
    pub(crate) fn alloc(&mut self, count: usize) -> AllocIdx {
        debug_assert!(count > 0);
        let tier = DATA_COUNT_TO_TIER[count.min(31)] as usize;
        let cap = DATA_SPACING[tier];

        let data = self.data.get_mut();
        if let Some(free_idx) = self.free_lists[tier].pop() {
            // Reuse a freed slot
            AllocIdx::from_usize(free_idx as usize)
        } else {
            // Allocate new
            let start = data.len();
            data.extend((0..cap).map(|_| MaybeUninit::uninit()));
            AllocIdx::from_usize(start)
        }
    }

    /// Free a group at the given AllocIdx (which was allocated with given count).
    pub(crate) fn free(&mut self, idx: AllocIdx, count: usize) {
        debug_assert!(!idx.is_empty());
        let tier = DATA_COUNT_TO_TIER[count.min(31)] as usize;
        self.free_lists[tier].push(idx.as_usize() as u32);
    }

    /// Insert a new element at the given bit for the given node, and update the data in the node.
    /// This operation will also set the corresponding bit in the node. This function returns the
    /// location where the data was inserted.
    pub(crate) fn insert_new_bit(&mut self, node: &mut MultiBitNode, data_bit: u32, val: T) -> Loc {
        debug_assert!(!node.has_data_bit(data_bit));

        let (new_idx, phys_slot) = if node.data_idx.is_empty() {
            // new allocation
            debug_assert!(node.data_bitmap == 0);
            let new_idx = self.alloc(1);
            // SAFETY:
            // - The slot is uninitialized, because it was just allocated
            // - There is only a single position where the data can be written, i.e., 0.
            unsafe { self.write_at(new_idx, 0, val) };
            (new_idx, 0)
        } else {
            // update / re-allocate
            let count = node.data_bitmap.count_ones() as usize;
            let phys_slot = compute_slot(node.data_bitmap, data_bit);
            let new_idx = self.insert_slot(node.data_idx, count, phys_slot as usize, val);
            (new_idx, phys_slot)
        };
        node.set_data_bit(data_bit);
        node.data_idx = new_idx;

        Loc {
            idx: node.data_idx,
            bit: data_bit,
            slot: phys_slot,
        }
    }

    /// Insert a new element at the given physical slot within a group.
    /// Handles tier upgrade if needed. Shifts elements after `phys_slot` to the right.
    fn insert_slot(&mut self, idx: AllocIdx, count: usize, phys_slot: usize, val: T) -> AllocIdx {
        let old_tier = DATA_COUNT_TO_TIER[count.min(31)] as usize;
        let new_tier = DATA_COUNT_TO_TIER[(count + 1).min(31)] as usize;

        if new_tier > old_tier {
            // Tier upgrade: allocate new group FIRST (before getting mutable data borrow)
            let new_idx = self.alloc(count + 1);
            let old_start = idx.as_usize();
            let new_start = new_idx.as_usize();

            let data = self.data.get_mut();
            // Copy elements before phys_slot
            for i in 0..phys_slot {
                data[new_start + i] = replace(&mut data[old_start + i], MaybeUninit::uninit());
            }
            // Write new element
            data[new_start + phys_slot].write(val);
            // Copy elements after phys_slot (shifted by 1)
            for i in phys_slot..count {
                data[new_start + i + 1] = replace(&mut data[old_start + i], MaybeUninit::uninit());
            }

            self.free(idx, count);
            new_idx
        } else {
            // No upgrade: shift in-place
            let data = self.data.get_mut();
            // Shift elements to the right starting from the end
            for i in (phys_slot..count).rev() {
                data[idx.as_usize() + i + 1] =
                    replace(&mut data[idx.as_usize() + i], MaybeUninit::uninit());
            }
            // Write new element
            data[idx.as_usize() + phys_slot].write(val);
            idx
        }
    }

    /// Remove the content of `node` stored at `loc`, and return it. This function will unset the
    /// corresponding bit, and update the data_idx if the data needed to be re-allocated.
    pub(crate) fn remove_bit(&mut self, node: &mut MultiBitNode, loc: Loc) -> T {
        debug_assert!(node.has_data_bit(loc.bit));
        debug_assert!(!node.data_idx.is_empty());

        // ensure that the provided location is correct.
        debug_assert_eq!(loc.idx, node.data_idx,);
        debug_assert_eq!(loc.slot, compute_slot(node.data_bitmap, loc.bit));

        let count = node.data_bitmap.count_ones() as usize;
        let (val, new_idx) = self.remove_slot(loc.idx, loc.slot as usize, count);

        node.unset_data_bit(loc.bit);
        node.data_idx = new_idx;

        val
    }

    /// Remove element at the given physical slot within a group.
    /// Handles tier downgrade if needed. Shifts elements after `phys_slot` to the left.
    /// Returns the removed value and the new (possibly changed) AllocIdx.
    fn remove_slot(&mut self, idx: AllocIdx, phys_slot: usize, count: usize) -> (T, AllocIdx) {
        // SAFETY: The caller guarantees that the entry at `phys_slot` is initialized.
        // `phys_slot` was computed as `compute_slot(bitmap, bit)` before the call,
        // and the bitmap bit at `bit` was set, so the element is present.
        // Loc::new cannot be used here: `bit` is not meaningful in this context
        // (remove_slot operates on a physical slot directly, not via a live bitmap), so
        // 0 is used as a placeholder and `slot` is set explicitly.
        let val = unsafe { self.remove_raw(Loc::at_slot(idx, phys_slot as u32)) };

        // Shift elements left to fill the gap
        for i in (phys_slot + 1)..count {
            let elem = self.data.get_mut()[idx.as_usize() + i - 1..=idx.as_usize() + i].as_mut();
            elem[0] = replace(&mut elem[1], MaybeUninit::uninit());
        }

        let new_count = count - 1;
        if new_count > 0 {
            let old_tier = DATA_COUNT_TO_TIER[count.min(31)] as usize;
            let new_tier = DATA_COUNT_TO_TIER[new_count.min(31)] as usize;

            if new_tier < old_tier {
                // Tier downgrade: allocate smaller FIRST
                let new_idx = self.alloc(new_count);
                // Copy elements to new group.
                // SAFETY: After the shift above, elements at indices 0..new_count are all
                // initialized (the gap at phys_slot was already closed by shifting left).
                // assume_init_read is safe here because we immediately write each value into
                // the new allocation, taking ownership; the old slots are then returned to the
                // free list without being dropped again.
                for i in 0..new_count {
                    let src = unsafe { self.data.get_mut()[idx.as_usize() + i].assume_init_read() };
                    self.data.get_mut()[new_idx.as_usize() + i].write(src);
                }
                self.free(idx, count);
                return (val, new_idx);
            }
            (val, idx)
        } else {
            // Count is now 0, free the allocation
            self.free(idx, count);
            (val, AllocIdx::empty())
        }
    }

    /// Clear all allocations without calling drop.
    pub(crate) fn clear(&mut self) {
        self.data.get_mut().clear();
        for fl in &mut self.free_lists {
            fl.clear();
        }
    }

    /// Total number of slots in the flat backing array.
    #[cfg(test)]
    pub(crate) fn total_slots(&self) -> usize {
        // SAFETY: We only read the Vec length, no uninitialized data is accessed.
        unsafe { self.data.get().as_ref().unwrap() }.len()
    }

    /// Iterate over `(start, capacity)` for every entry in all free lists.
    #[cfg(test)]
    pub(crate) fn free_list_slots(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.free_lists.iter().enumerate().flat_map(|(tier, list)| {
            let cap = DATA_SPACING[tier];
            list.iter().map(move |&start| (start as usize, cap))
        })
    }
}

#[derive(Clone)]
pub(crate) struct NodeAllocator {
    data: Vec<MultiBitNode>,
    free_lists: [Vec<u32>; 6], // one free list per tier
}

impl Default for NodeAllocator {
    fn default() -> Self {
        let mut alloc = Self {
            data: Vec::new(),
            free_lists: Default::default(),
        };
        // Root node at flat index 0
        alloc.data.push(MultiBitNode::default());
        alloc
    }
}

impl Index<Loc> for NodeAllocator {
    type Output = MultiBitNode;

    fn index(&self, index: Loc) -> &Self::Output {
        self.get(index)
    }
}

impl IndexMut<Loc> for NodeAllocator {
    fn index_mut(&mut self, index: Loc) -> &mut Self::Output {
        self.get_mut(index)
    }
}

impl NodeAllocator {
    pub(crate) fn mem_size(&self) -> usize {
        self.data.capacity() * std::mem::size_of::<MultiBitNode>()
            + self
                .free_lists
                .iter()
                .map(|fl| fl.capacity() * std::mem::size_of::<u32>())
                .sum::<usize>()
    }

    #[inline(always)]
    fn get(&self, pos: Loc) -> &MultiBitNode {
        debug_assert!(!pos.idx.is_empty());
        &self.data[pos.idx.as_usize() + pos.slot as usize]
    }

    fn get_mut(&mut self, pos: Loc) -> &mut MultiBitNode {
        debug_assert!(!pos.idx.is_empty());
        &mut self.data[pos.idx.as_usize() + pos.slot as usize]
    }

    /// Allocate a new group of nodes with given capacity tier.
    ///
    /// Safety: The data is not yet initialized. The caller must ensure that each element will
    /// correctly be created.
    pub(crate) unsafe fn alloc(&mut self, count: usize) -> AllocIdx {
        debug_assert!(count > 0);
        let tier = CHILD_COUNT_TO_TIER[count.min(32)] as usize;
        let cap = CHILD_SPACING[tier];

        if let Some(free_idx) = self.free_lists[tier].pop() {
            AllocIdx::from_usize(free_idx as usize)
        } else {
            let start = self.data.len();
            self.data.extend((0..cap).map(|_| MultiBitNode::default()));
            AllocIdx::from_usize(start)
        }
    }

    /// Free a group at the given AllocIdx.
    pub(crate) fn free(&mut self, idx: AllocIdx, count: usize) {
        debug_assert!(!idx.is_empty());
        let tier = CHILD_COUNT_TO_TIER[count.min(32)] as usize;
        self.free_lists[tier].push(idx.as_usize() as u32);
    }

    /// Insert a new element at the given bit for the given node, and update the data in the node.
    /// The `node_loc` describes the position of the node in the datastructure itself. This function
    /// will read that location, compute the new position to insert that child, insert that child,
    /// and update the node metadata at position `node_loc` to reflect the change. The function will
    /// then return the location at which the child was inserted.
    pub(crate) fn insert_new_bit(&mut self, node_loc: Loc, child_bit: u32) -> Loc {
        let node_snapshot = self[node_loc];
        debug_assert!(!node_snapshot.has_child_bit(child_bit));

        let (new_idx, phys_slot) = if node_snapshot.children_idx.is_empty() {
            // new allocation
            debug_assert!(node_snapshot.child_bitmap == 0);
            // SAFETY: we immediately populate the data with an empty element.
            let idx = unsafe { self.alloc(1) };
            self.data[idx.0 as usize] = MultiBitNode::default();
            (idx, 0)
        } else {
            // update / re-allocate
            let count = node_snapshot.child_bitmap.count_ones() as usize;
            let phys_slot = compute_slot(node_snapshot.child_bitmap, child_bit);
            let new_idx = self.insert_slot(node_snapshot.children_idx, count, phys_slot as usize);
            (new_idx, phys_slot)
        };

        let node = &mut self[node_loc];
        // Populate that new node
        node.set_child_bit(child_bit);
        node.children_idx = new_idx;

        Loc {
            idx: new_idx,
            bit: child_bit,
            slot: phys_slot,
        }
    }

    /// Insert a new node at the given physical slot. Handles tier upgrade and shifting.
    fn insert_slot(&mut self, idx: AllocIdx, count: usize, phys_slot: usize) -> AllocIdx {
        let old_tier = CHILD_COUNT_TO_TIER[count.min(32)] as usize;
        let new_tier = CHILD_COUNT_TO_TIER[(count + 1).min(32)] as usize;

        if new_tier > old_tier {
            // Tier upgrade
            // SAFETY: We immediately populate all used nodes accordingly. Any unused node will
            // eventually be populated in this funtion (if no tier upgrade), where it is gonna be reset.
            let new_idx = unsafe { self.alloc(count + 1) };
            let old_start = idx.as_usize();
            let new_start = new_idx.as_usize();

            // Copy elements before phys_slot
            for i in 0..phys_slot {
                self.data[new_start + i] = self.data[old_start + i];
            }
            // New slot is default-initialized
            self.data[new_start + phys_slot] = MultiBitNode::default();
            // Copy elements after phys_slot (shifted by 1)
            for i in phys_slot..count {
                self.data[new_start + i + 1] = self.data[old_start + i];
            }

            self.free(idx, count);
            new_idx
        } else {
            // No upgrade: shift in-place
            for i in (phys_slot..count).rev() {
                self.data[idx.as_usize() + i + 1] = self.data[idx.as_usize() + i];
            }
            self.data[idx.as_usize() + phys_slot] = MultiBitNode::default();
            idx
        }
    }

    /// Remove child with the given bit from the node at `loc`. This function will read the metadata
    /// of the node at `loc`, compute the position of the slot of `child_bit`, remove that node (and
    /// potentially cause a re-allocation). Then, it will update the metadata of the node at loc
    /// by unsetting the bit and updating the children idx.
    pub(crate) fn remove_bit(&mut self, loc: Loc, child_bit: u32) {
        let node_snapshot = self[loc];

        debug_assert!(node_snapshot.has_child_bit(child_bit));
        debug_assert!(!node_snapshot.children_idx.is_empty());

        let count = node_snapshot.child_bitmap.count_ones() as usize;
        let phys_slot = compute_slot(node_snapshot.child_bitmap, child_bit) as usize;
        let children_idx = node_snapshot.children_idx;

        let new_children_idx = self.remove_slot(children_idx, phys_slot, count);

        let node = &mut self[loc];
        node.unset_child_bit(child_bit);
        node.children_idx = new_children_idx;
    }

    /// Remove node at the given physical slot. Handles tier downgrade and shifting.
    fn remove_slot(&mut self, idx: AllocIdx, phys_slot: usize, count: usize) -> AllocIdx {
        // Shift left
        for i in (phys_slot + 1)..count {
            self.data[idx.as_usize() + i - 1] = self.data[idx.as_usize() + i];
        }

        let new_count = count - 1;
        if new_count > 0 {
            let old_tier = CHILD_COUNT_TO_TIER[count.min(32)] as usize;
            let new_tier = CHILD_COUNT_TO_TIER[new_count.min(32)] as usize;

            if new_tier < old_tier {
                // Tier downgrade
                // SAFETY: Right after allocation, we immediately populate the content with the old
                // content from the previous table.
                let new_idx = unsafe { self.alloc(new_count) };
                let old_start = idx.as_usize();
                let new_start = new_idx.as_usize();
                for i in 0..new_count {
                    self.data[new_start + i] = self.data[old_start + i];
                }
                self.free(idx, count);
                new_idx
            } else {
                idx
            }
        } else {
            self.free(idx, count);
            AllocIdx::empty()
        }
    }

    pub(crate) fn clear(&mut self) {
        self.data.clear();
        self.data.push(MultiBitNode::default());
        for fl in &mut self.free_lists {
            fl.clear();
        }
    }

    /// Total number of slots in the flat backing array (including root at index 0).
    #[cfg(test)]
    pub(crate) fn total_slots(&self) -> usize {
        self.data.len()
    }

    /// Iterate over `(start, capacity)` for every entry in all free lists.
    #[cfg(test)]
    pub(crate) fn free_list_slots(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.free_lists.iter().enumerate().flat_map(|(tier, list)| {
            let cap = CHILD_SPACING[tier];
            list.iter().map(move |&start| (start as usize, cap))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ============ AllocIdx Tests ============

    #[test]
    fn test_alloc_idx_empty() {
        let idx = AllocIdx::empty();
        assert!(idx.is_empty());
        assert_eq!(idx.0, u32::MAX);
    }

    #[test]
    fn test_alloc_idx_default() {
        let idx = AllocIdx::default();
        assert!(idx.is_empty());
    }

    #[test]
    fn test_alloc_idx_from_usize() {
        let idx = AllocIdx::from_usize(42);
        assert!(!idx.is_empty());
        assert_eq!(idx.as_usize(), 42);
    }

    #[test]
    fn test_alloc_idx_from_usize_zero() {
        let idx = AllocIdx::from_usize(0);
        assert!(!idx.is_empty());
        assert_eq!(idx.as_usize(), 0);
    }

    #[test]
    fn test_alloc_idx_roundtrip() {
        for i in [0, 1, 100, 1000, u32::MAX as usize - 1] {
            let idx = AllocIdx::from_usize(i);
            assert_eq!(idx.as_usize(), i);
        }
    }

    // ============ Loc Tests ============

    #[test]
    fn test_loc_root() {
        let root = Loc::root();
        assert!(root.is_root());
        assert!(!root.is_empty());
        assert_eq!(root.idx, AllocIdx::from_usize(0));
        assert_eq!(root.slot, 0);
    }

    #[test]
    fn test_loc_is_empty() {
        let loc = Loc {
            idx: AllocIdx::empty(),
            bit: 0,
            slot: 0,
        };
        assert!(loc.is_empty());
    }

    #[test]
    fn test_loc_is_not_empty() {
        let loc = Loc {
            idx: AllocIdx::from_usize(1),
            bit: 0,
            slot: 0,
        };
        assert!(!loc.is_empty());
    }

    #[test]
    fn test_loc_new_computes_slot() {
        // With bitmap=0b0101 and bit=2, slot should be 1 (one bit set before offset 2)
        let loc = Loc::new(AllocIdx::from_usize(10), 2, 0b0101);
        assert_eq!(loc.idx, AllocIdx::from_usize(10));
        assert_eq!(loc.bit, 2);
        assert_eq!(loc.slot, 1); // bits 0 is set before offset 2
    }

    #[test]
    fn test_loc_new_computes_slot_first_bit() {
        // With bitmap=0b0001 and bit=0, slot should be 0
        let loc = Loc::new(AllocIdx::from_usize(5), 0, 0b0001);
        assert_eq!(loc.slot, 0);
    }

    #[test]
    fn test_loc_new_computes_slot_multiple_bits() {
        // With bitmap=0b1111 and bit=3, slot should be 3
        let loc = Loc::new(AllocIdx::from_usize(7), 3, 0b1111);
        assert_eq!(loc.slot, 3);
    }

    // ============ compute_slot Tests ============

    #[test]
    fn test_compute_slot_empty_bitmap() {
        assert_eq!(compute_slot(0, 0), 0);
        assert_eq!(compute_slot(0, 5), 0);
    }

    #[test]
    fn test_compute_slot_single_bit() {
        assert_eq!(compute_slot(0b1, 1), 1);
        assert_eq!(compute_slot(0b10, 2), 1);
        assert_eq!(compute_slot(0b100, 3), 1);
    }

    #[test]
    fn test_compute_slot_multiple_bits() {
        assert_eq!(compute_slot(0b0111, 3), 3);
        assert_eq!(compute_slot(0b1111, 4), 4);
        assert_eq!(compute_slot(0b11111111, 8), 8);
    }

    #[test]
    fn test_compute_slot_partial_bitmap() {
        // With bitmap=0b10101 (bits 0, 2, 4 set), offset=4 gives slot=2
        assert_eq!(compute_slot(0b10101, 4), 2);
        // With offset=2 gives slot=1
        assert_eq!(compute_slot(0b10101, 2), 1);
    }

    // ============ CellAllocator Tests ============

    #[test]
    fn test_cell_allocator_basic_alloc() {
        let mut alloc = CellAllocator::<u32>::default();
        let idx = alloc.alloc(1);
        assert!(!idx.is_empty());
    }

    #[test]
    fn test_cell_allocator_write_and_read() {
        let mut alloc = CellAllocator::<u32>::default();
        let idx = alloc.alloc(1);

        unsafe {
            alloc.write_at(idx, 0, 42);
        }

        let loc = Loc {
            idx,
            bit: 0,
            slot: 0,
        };
        let val = unsafe { alloc.get(loc) };
        assert_eq!(*val, 42);
    }

    #[test]
    fn test_cell_allocator_replace() {
        let mut alloc = CellAllocator::<u32>::default();
        let idx = alloc.alloc(1);

        unsafe {
            alloc.write_at(idx, 0, 10);
        }

        let loc = Loc {
            idx,
            bit: 0,
            slot: 0,
        };
        let old_val = unsafe { alloc.replace(loc, 20) };
        assert_eq!(old_val, 10);

        let new_val = unsafe { alloc.get(loc) };
        assert_eq!(*new_val, 20);
    }

    #[test]
    fn test_cell_allocator_free_list_reuse() {
        let mut alloc = CellAllocator::<u32>::default();
        let idx1 = alloc.alloc(1);
        alloc.free(idx1, 1);

        let idx2 = alloc.alloc(1);
        // Should reuse the freed allocation
        assert_eq!(idx1, idx2);
    }

    #[test]
    fn test_cell_allocator_multiple_allocations() {
        let mut alloc = CellAllocator::<u32>::default();
        let idx1 = alloc.alloc(2);
        let idx2 = alloc.alloc(2);

        assert_ne!(idx1, idx2);

        unsafe {
            alloc.write_at(idx1, 0, 10);
            alloc.write_at(idx1, 1, 11);
            alloc.write_at(idx2, 0, 20);
            alloc.write_at(idx2, 1, 21);
        }

        let loc1_0 = Loc {
            idx: idx1,
            bit: 0,
            slot: 0,
        };
        let loc1_1 = Loc {
            idx: idx1,
            bit: 0,
            slot: 1,
        };
        let loc2_0 = Loc {
            idx: idx2,
            bit: 0,
            slot: 0,
        };
        let loc2_1 = Loc {
            idx: idx2,
            bit: 0,
            slot: 1,
        };

        assert_eq!(*unsafe { alloc.get(loc1_0) }, 10);
        assert_eq!(*unsafe { alloc.get(loc1_1) }, 11);
        assert_eq!(*unsafe { alloc.get(loc2_0) }, 20);
        assert_eq!(*unsafe { alloc.get(loc2_1) }, 21);
    }

    #[test]
    fn test_cell_allocator_insert_slot_same_tier() {
        let mut alloc = CellAllocator::<u32>::default();
        // Allocate 4 elements (tier 2, capacity 4)
        let idx = alloc.alloc(4);

        unsafe {
            alloc.write_at(idx, 0, 10);
            alloc.write_at(idx, 1, 11);
            alloc.write_at(idx, 2, 12);
        }

        // Insert at count=3 -> count=4, stays in tier 2
        let new_idx = alloc.insert_slot(idx, 3, 1, 99);
        assert_eq!(new_idx, idx);

        let loc0 = Loc {
            idx,
            bit: 0,
            slot: 0,
        };
        let loc1 = Loc {
            idx,
            bit: 0,
            slot: 1,
        };
        let loc2 = Loc {
            idx,
            bit: 0,
            slot: 2,
        };
        let loc3 = Loc {
            idx,
            bit: 0,
            slot: 3,
        };

        assert_eq!(*unsafe { alloc.get(loc0) }, 10);
        assert_eq!(*unsafe { alloc.get(loc1) }, 99);
        assert_eq!(*unsafe { alloc.get(loc2) }, 11);
        assert_eq!(*unsafe { alloc.get(loc3) }, 12);
    }

    #[test]
    fn test_cell_allocator_insert_slot_with_upgrade() {
        let mut alloc = CellAllocator::<u32>::default();
        let idx = alloc.alloc(1);

        unsafe {
            alloc.write_at(idx, 0, 10);
        }

        // Insert triggers upgrade (1 -> 2)
        let new_idx = alloc.insert_slot(idx, 1, 0, 99);
        assert_ne!(new_idx, idx);

        let loc0 = Loc {
            idx: new_idx,
            bit: 0,
            slot: 0,
        };
        let loc1 = Loc {
            idx: new_idx,
            bit: 0,
            slot: 1,
        };

        assert_eq!(*unsafe { alloc.get(loc0) }, 99);
        assert_eq!(*unsafe { alloc.get(loc1) }, 10);
    }

    #[test]
    fn test_cell_allocator_remove_slot_no_downgrade() {
        let mut alloc = CellAllocator::<u32>::default();
        let idx = alloc.alloc(4);

        unsafe {
            alloc.write_at(idx, 0, 10);
            alloc.write_at(idx, 1, 11);
            alloc.write_at(idx, 2, 12);
            alloc.write_at(idx, 3, 13);
        }

        let (removed, new_idx) = alloc.remove_slot(idx, 1, 4);
        assert_eq!(removed, 11);
        assert_eq!(new_idx, idx);

        let loc0 = Loc {
            idx,
            bit: 0,
            slot: 0,
        };
        let loc1 = Loc {
            idx,
            bit: 0,
            slot: 1,
        };
        let loc2 = Loc {
            idx,
            bit: 0,
            slot: 2,
        };

        assert_eq!(*unsafe { alloc.get(loc0) }, 10);
        assert_eq!(*unsafe { alloc.get(loc1) }, 12);
        assert_eq!(*unsafe { alloc.get(loc2) }, 13);
    }

    #[test]
    fn test_cell_allocator_remove_slot_with_downgrade() {
        let mut alloc = CellAllocator::<u32>::default();
        let idx = alloc.alloc(2);

        unsafe {
            alloc.write_at(idx, 0, 10);
            alloc.write_at(idx, 1, 11);
        }

        let (removed, new_idx) = alloc.remove_slot(idx, 1, 2);
        assert_eq!(removed, 11);
        assert_ne!(new_idx, idx);

        let loc0 = Loc {
            idx: new_idx,
            bit: 0,
            slot: 0,
        };
        assert_eq!(*unsafe { alloc.get(loc0) }, 10);
    }

    #[test]
    fn test_cell_allocator_remove_slot_to_empty() {
        let mut alloc = CellAllocator::<u32>::default();
        let idx = alloc.alloc(1);

        unsafe {
            alloc.write_at(idx, 0, 42);
        }

        let (removed, new_idx) = alloc.remove_slot(idx, 0, 1);
        assert_eq!(removed, 42);
        assert!(new_idx.is_empty());
    }

    #[test]
    fn test_cell_allocator_clear() {
        let mut alloc = CellAllocator::<u32>::default();
        let _ = alloc.alloc(5);
        alloc.clear();

        // After clear, data should be empty
        assert_eq!(unsafe { alloc.data.get().as_ref().unwrap() }.len(), 0);
    }

    // ============ NodeAllocator Tests ============

    #[test]
    fn test_node_allocator_free_list_reuse() {
        let mut alloc = NodeAllocator::default();
        let idx1 = unsafe { alloc.alloc(2) };
        alloc.free(idx1, 2);

        let idx2 = unsafe { alloc.alloc(2) };
        // Should reuse
        assert_eq!(idx1, idx2);
    }

    #[test]
    fn test_node_allocator_insert_slot_same_tier() {
        let mut alloc = NodeAllocator::default();
        // Allocate 4 nodes (tier 2, capacity 4)
        let idx = unsafe { alloc.alloc(4) };

        // Insert at count=3 -> count=4, stays in tier 2
        let new_idx = alloc.insert_slot(idx, 3, 0);
        assert_eq!(new_idx, idx);
    }

    #[test]
    fn test_node_allocator_insert_slot_with_upgrade() {
        let mut alloc = NodeAllocator::default();
        let idx = unsafe { alloc.alloc(1) };

        let new_idx = alloc.insert_slot(idx, 1, 0);
        assert_ne!(new_idx, idx);
    }

    #[test]
    fn test_node_allocator_remove_slot_no_downgrade() {
        let mut alloc = NodeAllocator::default();
        let idx = unsafe { alloc.alloc(4) };

        let new_idx = alloc.remove_slot(idx, 1, 4);
        assert_eq!(new_idx, idx);
    }

    #[test]
    fn test_node_allocator_remove_slot_with_downgrade() {
        let mut alloc = NodeAllocator::default();
        let idx = unsafe { alloc.alloc(2) };

        let new_idx = alloc.remove_slot(idx, 1, 2);
        assert_ne!(new_idx, idx);
    }

    #[test]
    fn test_node_allocator_remove_slot_to_empty() {
        let mut alloc = NodeAllocator::default();
        let idx = unsafe { alloc.alloc(1) };

        let new_idx = alloc.remove_slot(idx, 0, 1);
        assert!(new_idx.is_empty());
    }

    #[test]
    fn test_node_allocator_clear() {
        let mut alloc = NodeAllocator::default();
        let _ = unsafe { alloc.alloc(5) };
        alloc.clear();

        // After clear, should reset to initial state with just root
        assert_eq!(alloc.data.len(), 1);
    }

    // ============ Integration Tests ============

    #[test]
    fn test_cell_allocator_sequence_of_operations() {
        let mut alloc = CellAllocator::<i32>::default();

        // Start with 1 element
        let idx1 = alloc.alloc(1);
        unsafe {
            alloc.write_at(idx1, 0, 100);
        }

        // Insert at end (1->2, tier upgrade 0->1)
        // [100] -> insert at 1 -> [100, new]
        let idx2 = alloc.insert_slot(idx1, 1, 1, 200);
        let loc0 = Loc {
            idx: idx2,
            bit: 0,
            slot: 0,
        };
        let loc1 = Loc {
            idx: idx2,
            bit: 0,
            slot: 1,
        };
        assert_eq!(*unsafe { alloc.get(loc0) }, 100);
        assert_eq!(*unsafe { alloc.get(loc1) }, 200);

        // Insert at position 1 (2->3, tier upgrade 1->2)
        // [100, 200] -> insert at 1 -> [100, new, 200]
        let idx3 = alloc.insert_slot(idx2, 2, 1, 300);
        let loc0 = Loc {
            idx: idx3,
            bit: 0,
            slot: 0,
        };
        let loc1 = Loc {
            idx: idx3,
            bit: 0,
            slot: 1,
        };
        let loc2 = Loc {
            idx: idx3,
            bit: 0,
            slot: 2,
        };
        assert_eq!(*unsafe { alloc.get(loc0) }, 100);
        assert_eq!(*unsafe { alloc.get(loc1) }, 300);
        assert_eq!(*unsafe { alloc.get(loc2) }, 200);

        // Insert at end (3->4, tier 2->2, no upgrade)
        // [100, 300, 200] -> insert at 3 -> [100, 300, 200, new]
        let idx4 = alloc.insert_slot(idx3, 3, 3, 400);
        let loc0 = Loc {
            idx: idx4,
            bit: 0,
            slot: 0,
        };
        let loc1 = Loc {
            idx: idx4,
            bit: 0,
            slot: 1,
        };
        let loc2 = Loc {
            idx: idx4,
            bit: 0,
            slot: 2,
        };
        let loc3 = Loc {
            idx: idx4,
            bit: 0,
            slot: 3,
        };
        assert_eq!(*unsafe { alloc.get(loc0) }, 100);
        assert_eq!(*unsafe { alloc.get(loc1) }, 300);
        assert_eq!(*unsafe { alloc.get(loc2) }, 200);
        assert_eq!(*unsafe { alloc.get(loc3) }, 400);

        // Remove at position 1 (4->3, tier 2->2, no downgrade)
        // [100, 300, 200, 400] -> remove 1 -> [100, 200, 400]
        let (removed, idx5) = alloc.remove_slot(idx4, 1, 4);
        assert_eq!(removed, 300);
        let loc0 = Loc {
            idx: idx5,
            bit: 0,
            slot: 0,
        };
        let loc1 = Loc {
            idx: idx5,
            bit: 0,
            slot: 1,
        };
        let loc2 = Loc {
            idx: idx5,
            bit: 0,
            slot: 2,
        };
        assert_eq!(*unsafe { alloc.get(loc0) }, 100);
        assert_eq!(*unsafe { alloc.get(loc1) }, 200);
        assert_eq!(*unsafe { alloc.get(loc2) }, 400);

        // Remove at position 1 again (3->2, tier 2->1, downgrade)
        // [100, 200, 400] -> remove 1 -> [100, 400]
        let (removed, idx6) = alloc.remove_slot(idx5, 1, 3);
        assert_eq!(removed, 200);
        let loc0 = Loc {
            idx: idx6,
            bit: 0,
            slot: 0,
        };
        let loc1 = Loc {
            idx: idx6,
            bit: 0,
            slot: 1,
        };
        assert_eq!(*unsafe { alloc.get(loc0) }, 100);
        assert_eq!(*unsafe { alloc.get(loc1) }, 400);
    }

    #[test]
    fn test_node_allocator_sequence_of_operations() {
        let mut alloc = NodeAllocator::default();

        // Start with 1 node, set value at slot 0
        let idx1 = unsafe { alloc.alloc(1) };
        let loc = Loc {
            idx: idx1,
            bit: 0,
            slot: 0,
        };
        alloc[loc].data_bitmap = 100;

        // Insert at end (1->2, tier upgrade 0->1)
        // [100] -> insert at 1 -> [100, new]
        let idx2 = alloc.insert_slot(idx1, 1, 1);
        let loc_0 = Loc {
            idx: idx2,
            bit: 0,
            slot: 0,
        };
        let loc_1 = Loc {
            idx: idx2,
            bit: 0,
            slot: 1,
        };
        alloc[loc_1].data_bitmap = 200;
        assert_eq!(alloc[loc_0].data_bitmap, 100);
        assert_eq!(alloc[loc_1].data_bitmap, 200);

        // Insert at position 1 (2->3, tier upgrade 1->2)
        // [100, 200] -> insert at 1 -> [100, new, 200]
        let idx3 = alloc.insert_slot(idx2, 2, 1);
        let loc_0 = Loc {
            idx: idx3,
            bit: 0,
            slot: 0,
        };
        let loc_1 = Loc {
            idx: idx3,
            bit: 0,
            slot: 1,
        };
        let loc_2 = Loc {
            idx: idx3,
            bit: 0,
            slot: 2,
        };
        alloc[loc_1].data_bitmap = 300;
        assert_eq!(alloc[loc_0].data_bitmap, 100);
        assert_eq!(alloc[loc_1].data_bitmap, 300);
        assert_eq!(alloc[loc_2].data_bitmap, 200);

        // Insert at end (3->4, tier 2->2, no upgrade)
        // [100, 300, 200] -> insert at 3 -> [100, 300, 200, new]
        let idx4 = alloc.insert_slot(idx3, 3, 3);
        let loc_0 = Loc {
            idx: idx4,
            bit: 0,
            slot: 0,
        };
        let loc_1 = Loc {
            idx: idx4,
            bit: 0,
            slot: 1,
        };
        let loc_2 = Loc {
            idx: idx4,
            bit: 0,
            slot: 2,
        };
        let loc_3 = Loc {
            idx: idx4,
            bit: 0,
            slot: 3,
        };
        alloc[loc_3].data_bitmap = 400;
        assert_eq!(alloc[loc_0].data_bitmap, 100);
        assert_eq!(alloc[loc_1].data_bitmap, 300);
        assert_eq!(alloc[loc_2].data_bitmap, 200);
        assert_eq!(alloc[loc_3].data_bitmap, 400);

        // Remove at position 1 (4->3, tier 2->2, no downgrade)
        // [100, 300, 200, 400] -> remove 1 -> [100, 200, 400]
        let idx5 = alloc.remove_slot(idx4, 1, 4);
        let loc_0 = Loc {
            idx: idx5,
            bit: 0,
            slot: 0,
        };
        let loc_1 = Loc {
            idx: idx5,
            bit: 0,
            slot: 1,
        };
        let loc_2 = Loc {
            idx: idx5,
            bit: 0,
            slot: 2,
        };
        assert_eq!(alloc[loc_0].data_bitmap, 100);
        assert_eq!(alloc[loc_1].data_bitmap, 200);
        assert_eq!(alloc[loc_2].data_bitmap, 400);

        // Remove at position 1 again (3->2, tier 2->1, downgrade)
        // [100, 200, 400] -> remove 1 -> [100, 400]
        let idx6 = alloc.remove_slot(idx5, 1, 3);
        let loc_0 = Loc {
            idx: idx6,
            bit: 0,
            slot: 0,
        };
        let loc_1 = Loc {
            idx: idx6,
            bit: 0,
            slot: 1,
        };
        assert_eq!(alloc[loc_0].data_bitmap, 100);
        assert_eq!(alloc[loc_1].data_bitmap, 400);
    }
}
