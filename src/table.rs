//! The inner node implementation.

use num_traits::Zero;

use crate::{
    prefix::mask_from_prefix_len,
    Prefix,
    {
        allocator::{compute_slot, AllocIdx, CellAllocator, Loc, NodeAllocator, RawPtr},
        node::{
            child_bit, child_cover_mask, data_bit, data_cover_mask, extend_repr, Key,
            MaskedLexIter, MultiBitNode, DATA_BIT_TO_PREFIX,
        },
    },
};

/// Number of levels inside each node
pub(crate) const K: u32 = 5;
pub(crate) const NUM_DATA: usize = (1 << (K as usize)) - 1;
pub(crate) const NUM_CHILDREN: usize = 1 << (K as usize);

/// A table to the dense prefix-trie that offers interior mutability.
///
/// # Architecture
///
/// The table consists of the allocator for (multi-bit) nodes and data. Each multi-bit node
/// represents `K` levels of the binary tree, and thus contains `NUM_DATA` branches (possible data
/// slots) and `NUM_CHILDREN` pointers to children.
///
/// ## Memory Layout
///
/// To avoid storing pointers to each data and child slot, each node stores a single base index
/// into a compact allocation, and the physical slot is computed from a bitmap using a popcount.
/// The bitmap also enables efficient tree traversals.
///
/// Sparse nodes would waste memory if we always allocated the maximum capacity. To avoid this, the
/// allocator uses a tier system: allocations come in capacities of 1, 2, 4, 8, 16, and 31 (or 32
/// for children). The allocator upgrades or downgrades the tier as the node grows or shrinks.
///
/// ### AllocIdx
///
/// `AllocIdx` is a single `u32` that identifies an allocation. `u32::MAX` represents the empty
/// state (no allocation). All other values are indices into the flat backing array.
///
/// # Safety
/// Owning a mutable reference to the Table implies that you can safely get a mutable reference to
/// the inner data. If, however, you own an immutable reference, then you must guarantee that there
/// is no other reference to the Table that potentially accesses the same node mutably. This interior
/// mutability is only ever provided in `get_mut`.
pub(crate) struct Table<T> {
    nodes: NodeAllocator,
    cells: CellAllocator<T>,
}

impl<T> Default for Table<T> {
    fn default() -> Self {
        Self {
            nodes: Default::default(),
            cells: Default::default(),
        }
    }
}

// Safety:
// - Sending a Table over thread boundary is fine. No-one besides us can have the raw pointer,
//   otherwise, the map would be borrowed.
// - Sending a reference of Table over thread boundaries (i.e., TrieView is Send) is safe,
//   because we ensure that the existence of a TrieView on a sub-tree implies the absence of a
//   TrieViewMut that overlaps with that sub-tree.
// - Sending a mutable reference of Table over thread boundaries (i.e., TrieView is Send) is
//   safe, because we ensure that the existence of a TrieViewMut on a sub-tree implies the absence
//   of any other TrieView or TrieViewMut that overlaps with that sub-tree.
// The same argument holds for Sync.
unsafe impl<T: Send> Send for Table<T> {}
unsafe impl<T: Sync> Sync for Table<T> {}

impl<T> Table<T> {
    pub(crate) fn raw_cells(&mut self) -> RawPtr<T> {
        self.cells.raw_ptr()
    }

    /// get the root node
    #[inline(always)]
    pub(crate) fn root(&self) -> &MultiBitNode {
        // Safety: no-one else owns a mutable reference to the table.
        &self.nodes[Loc::root()]
    }

    #[inline(always)]
    pub(crate) fn node(&self, pos: Loc) -> &MultiBitNode {
        // Safety: no-one else owns a mutable reference to the table.
        &self.nodes[pos]
    }

    #[inline(always)]
    pub(crate) fn child(&self, pos: Loc, child_bit: u32) -> Option<Loc> {
        let node = self.node(pos);
        if node.has_child_bit(child_bit) {
            Some(Loc::new(node.children_idx, child_bit, node.child_bitmap))
        } else {
            None
        }
    }

    /// Remove a child from a parent node and compact the children allocation.
    ///
    /// After insertion, each child occupies physical slot `compute_slot(child_bitmap, bit)`.
    /// Simply calling `unset_child_offset` clears the bit but leaves the physical array unchanged,
    /// making remaining children inaccessible at the wrong slots. This function correctly shifts
    /// the array and handles tier downgrades.
    #[inline(always)]
    pub(crate) fn remove_child_at(&mut self, parent_loc: Loc, child_bit: u32) {
        self.nodes.remove_bit(parent_loc, child_bit);
    }

    #[inline(always)]
    pub(crate) fn get_data(&self, loc: Present) -> &T {
        // SAFETY: `Present` may only be constructed when the bitmap bit at `loc.data.bit`
        // is set and `loc.data.slot == compute_slot(bitmap, bit)`, guaranteeing the cell
        // at `data.idx + data.slot` is initialized.
        unsafe { self.cells.get(loc.data) }
    }

    #[inline(always)]
    pub(crate) fn get_data_mut(&mut self, loc: Present) -> &mut T {
        // SAFETY: Same as `get_data`; `Present` invariant guarantees initialization and correct
        // slot. Exclusive `&mut self` ensures no aliasing.
        unsafe { self.cells.get_mut(loc.data) }
    }

    /// SAFETY: you must ensure that:
    /// 1. The raw pointer must be the same as self.internal_nodes.
    /// 2. There exists no reference to that location right now.
    /// 3. During 'a, you will never ever again construct a reference to the internal_nodes table.
    /// 4. During 'a, you will never again access this location again.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub(crate) unsafe fn unsafe_get_mut(&self, ptr: &mut RawPtr<T>, loc: Present) -> &mut T {
        // SAFETY: Caller upholds the invariants declared on this function (exclusive access,
        // no other live references). `Present` invariant ensures `loc.data.slot` points to an
        // initialized cell with the correct POPCNT-derived offset.
        unsafe { self.cells.unsafe_get_mut(ptr, loc.data) }
    }

    #[inline(always)]
    pub(crate) fn set_data(&mut self, loc: Empty, val: T) -> Present {
        let data_loc = self
            .cells
            .insert_new_bit(&mut self.nodes[loc.node], loc.data_bit, val);
        // SAFETY:
        // - `set_data_bit(raw)` just set the bitmap bit, and the value was written above,
        //   so the cell at `data_idx + phys_slot` is now initialized.
        // - `phys_slot` = compute_slot(bitmap_before_insert, data_bit), which is the
        //   correct physical slot for this raw offset after the insertion shift.
        unsafe { Present::new(loc.node, data_loc, loc.depth) }
    }

    #[inline(always)]
    pub(crate) fn replace_data(&mut self, loc: Present, val: T) -> T {
        // SAFETY: `Present` invariant: bitmap bit at `loc.data.bit` is set and
        // `loc.data.slot == compute_slot(bitmap, bit)`, so the cell is initialized.
        unsafe { self.cells.replace(loc.data, val) }
    }

    /// Take data for consuming iteration without shifting remaining elements.
    ///
    /// Unlike `take_data`, this does NOT call `shift_left` after removal, intentionally
    /// leaving the cell array non-compact.  This is only correct when the following
    /// invariants are upheld by the caller (see `# Safety` below).
    ///
    /// # Safety
    ///
    /// The caller must guarantee all of the following:
    ///
    /// 1. **Snapshot consistency**: `loc` was produced by a `MaskedLexIter` whose internal
    ///    node snapshot was taken *before* any elements in this node were removed.  The slot
    ///    `loc.data.slot == compute_slot(snapshot_bitmap, bit)` is only valid relative
    ///    to that snapshot; after a `shift_left` it would point to the wrong cell.  Because
    ///    we skip `shift_left`, every slot derived from the same snapshot remains valid until
    ///    its own turn is reached.
    ///
    /// 2. **Single consumption**: each `bit` is passed at most once; `MaskedLexIter`
    ///    yields every set bit in the snapshot exactly once, so no double-free can occur.
    ///
    /// 3. **No subsequent structured access**: after this call the node's bitmap still has
    ///    the bit at `loc.data.bit` set, and the cell array has a hole where the
    ///    element was.  Any code that recomputes `compute_slot` from the live bitmap would
    ///    derive wrong slot values.  The caller must ensure that no such access happens,
    ///    i.e., the consuming iterator owns the table exclusively and will drop it once all
    ///    elements are consumed.
    #[inline(always)]
    pub(crate) unsafe fn take_data_for_iter(&mut self, loc: Present) -> T {
        // SAFETY: `Present` invariant guarantees the bitmap bit at `loc.data.bit`
        // is set and `loc.data.slot == compute_slot(snapshot_bitmap, bit)`, so the
        // cell is initialized and the slot is correct relative to the snapshot.
        unsafe { self.cells.remove_raw(loc.data) }
        // No shift_left: remaining elements stay at their snapshot-derived physical slots
        // so that subsequent MaskedLexIter items can still find them (safety invariant 1).
    }

    #[inline(always)]
    pub(crate) fn take_data(&mut self, loc: Present) -> T {
        self.cells.remove_bit(&mut self.nodes[loc.node], loc.data)
    }

    pub(crate) fn mem_size(&self) -> usize {
        self.nodes.mem_size() + self.cells.mem_size()
    }
}

impl<T: Clone> Clone for Table<T> {
    fn clone(&self) -> Self {
        let mut x = Self {
            nodes: self.nodes.clone(),
            cells: Default::default(),
        };

        // Clone only live nodes reachable from root via DFS. Freed nodes in the flat
        // array may have stale data_bitmap/data_idx from tier upgrades; visiting them
        // would allocate cells that are never freed, causing a memory leak.
        let mut stack = vec![Loc::root()];
        while let Some(loc) = stack.pop() {
            let node = self.nodes[loc];
            if node.data_bitmap != 0 && !node.data_idx.is_empty() {
                let count = node.data_bitmap.count_ones() as usize;
                let data_idx = x.cells.alloc(count);
                for (slot, data_loc) in node.data_locs().enumerate() {
                    let val = unsafe { self.cells.get(data_loc) }.clone();
                    unsafe { x.cells.write_at(data_idx, slot as u32, val) };
                }
                x.nodes[loc].data_idx = data_idx;
            } else {
                x.nodes[loc].data_idx = AllocIdx::empty();
            }
            if node.child_bitmap != 0 {
                stack.extend(node.child_locs());
            }
        }

        x
    }
}

/// Safety: This represents a present (initialized) data element in the trie.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Present {
    node: Loc,
    data: Loc, // includes bit (bitmap position) and slot (physical location)
    depth: u32,
}

impl Present {
    /// SAFETY:
    /// - The data cell at `data.slot` (computed from `data.bit` and the node's data_bitmap) must be initialized.
    /// - The node's data_bitmap bit at `data.bit` must be set, indicating the entry is present.
    /// - `data.slot` must equal `compute_slot(node.data_bitmap, data.bit)`.
    pub(crate) unsafe fn new(node: Loc, data: Loc, depth: u32) -> Self {
        debug_assert!((data.bit as usize) < NUM_DATA);
        Self { node, data, depth }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Empty {
    node: Loc,
    pub(crate) data_bit: u32, // bitmap bit where data will be inserted
    depth: u32,
}

impl Empty {
    /// SAFETY: The referenced cell at data_bit must be empty (uninitialized).
    pub(crate) unsafe fn new(node: Loc, data_bit: u32, depth: u32) -> Self {
        debug_assert!((data_bit as usize) < NUM_DATA);
        Self {
            node,
            data_bit,
            depth,
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct NoNode {
    last_node: Loc,
    last_depth: u32,
}

impl NoNode {
    /// SAFETY: The referenced cell at internal_idx must be empty (uninitialized).
    pub(crate) fn new(last_node: Loc, last_depth: u32) -> Self {
        Self {
            last_node,
            last_depth,
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) enum Location {
    Present(Present),
    Empty(Empty),
    NoNode(NoNode),
}

impl Location {
    pub fn present(self) -> Option<Present> {
        match self {
            Location::Present(l) => Some(l),
            _ => None,
        }
    }

    pub fn into_node(self) -> Option<Result<Present, Empty>> {
        match self {
            Location::Present(l) => Some(Ok(l)),
            Location::Empty(l) => Some(Err(l)),
            _ => None,
        }
    }
}

#[rustfmt::skip]
pub(crate) trait ElementLoc {
    fn node(&self) -> Loc;
    fn depth(&self) -> u32;
}

impl Present {
    /// Compute the prefix of that element
    pub(crate) fn prefix<P: Prefix>(&self, key: P::R) -> P {
        prefix(key, self.depth, self.data.bit as usize)
    }

    /// Get the bitmap bit position of this data element
    pub(crate) fn bit(&self) -> u32 {
        self.data.bit
    }

    /// Refresh this location against the current node state.
    ///
    /// When multiple `take_data` calls are made on the same node in sequence (e.g. in
    /// `remove_children`), tier downgrades inside `take_data` may update `node.data_idx` and
    /// shift elements to a new allocation. The `Present` values produced by `data_descendants`
    /// were computed from a snapshot and may hold a stale `data.idx`. This method re-reads
    /// `data_idx` from the live node and recomputes `data.slot` from the live bitmap, returning
    /// a fresh `Present` that is safe to pass to `take_data`.
    pub(crate) fn refresh<T>(self, table: &Table<T>) -> Self {
        let node = table.node(self.node);
        let current_idx = node.data_idx;
        let current_slot = compute_slot(node.data_bitmap, self.data.bit);
        // The bit must still be set; if it isn't, the caller has a logic error.
        debug_assert!(
            (node.data_bitmap >> self.data.bit) & 1 == 1,
            "refresh: bit {} is no longer set in data_bitmap",
            self.data.bit
        );
        Self {
            node: self.node,
            data: Loc {
                idx: current_idx,
                bit: self.data.bit,
                slot: current_slot,
            },
            depth: self.depth,
        }
    }
}

fn prefix<P: Prefix>(key: P::R, depth: u32, data_offset: usize) -> P {
    let mask = mask_from_prefix_len(depth as u8);
    let root = key & mask;

    let (offset, offset_len) = DATA_BIT_TO_PREFIX[data_offset];
    let offset = <P::R as num_traits::cast::NumCast>::from(offset).unwrap();
    let offset_bits = K - 1;
    let total_width = P::num_bits();
    let shifted_offset = if total_width > depth + offset_bits {
        offset << (total_width - (depth + offset_bits)) as usize
    } else {
        offset >> (depth + offset_bits - total_width) as usize
    };

    let repr = root | shifted_offset;
    let prefix_len = depth + offset_len as u32;

    P::from_repr_len(repr, prefix_len as u8)
}

#[rustfmt::skip]
impl ElementLoc for Present {
    fn node(&self) -> Loc { self.node }
    fn depth(&self) -> u32 { self.depth }
}
#[rustfmt::skip]
impl ElementLoc for Empty {
    fn node(&self) -> Loc { self.node }
    fn depth(&self) -> u32 { self.depth }
}
#[rustfmt::skip]
impl ElementLoc for NoNode {
    fn node(&self) -> Loc { self.last_node }
    fn depth(&self) -> u32 { self.last_depth }
}
#[rustfmt::skip]
impl<A: ElementLoc, B: ElementLoc> ElementLoc for Result<A, B> {
    fn node(&self) -> Loc { match self {Ok(a) => a.node(), Err(b) => b.node(), } }
    fn depth(&self) -> u32 { match self {Ok(a) => a.depth(), Err(b) => b.depth(), } }
}
impl ElementLoc for Location {
    fn node(&self) -> Loc {
        match self {
            Location::Present(x) => x.node,
            Location::Empty(x) => x.node,
            Location::NoNode(x) => x.last_node,
        }
    }
    fn depth(&self) -> u32 {
        match self {
            Location::Present(x) => x.depth,
            Location::Empty(x) => x.depth,
            Location::NoNode(x) => x.last_depth,
        }
    }
}

impl<T> Table<T> {
    /// Find the node in which the given prefix is/should be stored. If the node does not exist,
    /// the function returns Err(idx) with the index of the closest parent of that node.
    #[inline(always)]
    pub(crate) fn find_element<R: Key>(&self, key: R, prefix_len: u32) -> Location {
        let mut loc = Loc::root();
        let mut node = self.root();
        let mut depth = 0;
        while prefix_len >= depth + K {
            let child_bit = child_bit(depth, key);
            let Some(next) = self.child(loc, child_bit) else {
                return Location::NoNode(NoNode::new(loc, depth));
            };
            loc = next;
            depth += K;
            node = self.node(loc);
        }
        let data_bit = data_bit(key, prefix_len);
        if node.has_data_bit(data_bit) {
            let data_loc = Loc::new(node.data_idx, data_bit, node.data_bitmap);
            Location::Present(
                // SAFETY: `has_data_bit` confirmed the bitmap bit at `data_bit` is set,
                // so the element is initialized. `slot` = compute_slot(node.data_bitmap, data_bit).
                unsafe { Present::new(loc, data_loc, depth) },
            )
        } else {
            Location::Empty(
                // SAFETY: `has_data_bit` returned false, so the bitmap bit at `data_bit`
                // is clear, meaning no element is stored at this position.
                unsafe { Empty::new(loc, data_bit, depth) },
            )
        }
    }

    /// Find the location of the longest prefix match.
    #[inline(always)]
    pub(crate) fn find_lpm<R: Key>(&self, key: R, prefix_len: u32) -> Option<Present> {
        let mut loc = Loc::root();
        let mut depth = 0;
        let mut lpm = None;

        loop {
            let node = self.node(loc);
            // update the LPM
            if let Some(data_loc) = node.data_lpm_loc(depth, key, prefix_len) {
                // SAFETY: `data_lpm_loc` only returns `Some(loc)` when the bitmap bit at
                // `loc.bit` is set, and `loc.slot == compute_slot(data_bitmap, bit)`.
                lpm = Some(unsafe { Present::new(loc, data_loc, depth) });
            }
            // if the prefix is in this node
            if prefix_len < depth + K {
                return lpm;
            }
            let child_bit = child_bit(depth, key);
            let Some(next) = self.child(loc, child_bit) else {
                return lpm;
            };
            loc = next;
            depth += K;
        }
    }

    /// Find the location of the shortest prefix match.
    #[inline(always)]
    pub(crate) fn find_spm<R: Key>(&self, key: R, prefix_len: u32) -> Option<Present> {
        let mut loc = Loc::root();
        let mut depth = 0;

        loop {
            let node = self.node(loc);
            // update the SPM
            if let Some(spm_loc) = node.data_spm_loc(depth, key, prefix_len) {
                // SAFETY: `data_spm_loc` only returns `Some(loc)` when the bitmap bit at
                // `loc.bit` is set, and `loc.slot == compute_slot(data_bitmap, bit)`.
                return Some(unsafe { Present::new(loc, spm_loc, depth) });
            }
            // if the prefix is in this node
            if prefix_len < depth + K {
                return None;
            }
            let child_bit = child_bit(depth, key);
            loc = self.child(loc, child_bit)?;
            depth += K;
        }
    }

    /// Find the node in which the given prefix is/should be stored. If the node does not exist,
    /// the function returns Err(idx) with the index of the closest parent of that node. If it does
    /// exist, the function returns also a path, that is, the index of each node along with the
    /// external index taken to reach the node. The returned node is not part of that path. The root
    /// is the first element in the path.
    #[inline(always)]
    #[allow(clippy::type_complexity)]
    pub(crate) fn find_element_with_path<R: Key>(
        &self,
        key: R,
        prefix_len: u32,
    ) -> Option<(Result<Present, Empty>, Vec<(Loc, u32)>)> {
        let mut path: Vec<(Loc, u32)> = Vec::new();
        let mut loc = Loc::root();
        let mut depth = 0;
        while prefix_len >= depth + K {
            let child_bit = child_bit(depth, key);
            let next_loc = self.child(loc, child_bit)?;
            path.push((loc, child_bit));
            loc = next_loc;
            depth += K;
        }

        let node = self.node(loc);
        let data_bit = data_bit(key, prefix_len);
        let result = if node.has_data_bit(data_bit) {
            let data_loc = Loc::new(node.data_idx, data_bit, node.data_bitmap);
            // SAFETY: `has_data_bit` confirmed the bitmap bit at `data_bit` is set, so the
            // element is initialized. `slot` = compute_slot(node.data_bitmap, data_bit).
            Ok(unsafe { Present::new(loc, data_loc, depth) })
        } else {
            // SAFETY: `has_data_bit` returned false, so the bitmap bit at `data_bit` is clear
            // and no element is stored at this position.
            Err(unsafe { Empty::new(loc, data_bit, depth) })
        };
        Some((result, path))
    }

    #[inline(always)]
    pub(crate) fn find_node_or_insert<R: Key>(
        &mut self,
        key: R,
        prefix_len: u32,
    ) -> Result<Present, Empty> {
        self.find_node_or_insert_from(Loc::root(), 0, key, prefix_len)
    }

    #[inline(always)]
    pub(crate) fn find_node_or_insert_from<R: Key>(
        &mut self,
        mut loc: Loc,
        mut depth: u32,
        key: R,
        prefix_len: u32,
    ) -> Result<Present, Empty> {
        while prefix_len >= depth + K {
            loc = self.get_next_node_idx_or_insert(loc, depth, key);
            depth += K;
        }
        let node = self.node(loc);
        let data_bit = data_bit(key, prefix_len);
        if node.has_data_bit(data_bit) {
            let data_loc = Loc::new(node.data_idx, data_bit, node.data_bitmap);
            // SAFETY: `has_data_bit` confirmed the bitmap bit at `data_bit` is set, so the
            // element is initialized. `slot` = compute_slot(node.data_bitmap, data_bit).
            Ok(unsafe { Present::new(loc, data_loc, depth) })
        } else {
            // SAFETY: `has_data_bit` returned false, so the bitmap bit at `data_bit` is clear
            // and no element is stored at this position.
            Err(unsafe { Empty::new(loc, data_bit, depth) })
        }
    }

    fn get_next_node_idx_or_insert<R: Key>(&mut self, loc: Loc, depth: u32, key: R) -> Loc {
        let child_bit = child_bit(depth, key);
        if let Some(next) = self.child(loc, child_bit) {
            return next;
        }

        self.nodes.insert_new_bit(loc, child_bit)
    }

    // get an iterator over all data locations in the current node that are descendants of the given prefix.
    pub(crate) fn data_descendants<R: Key>(
        &self,
        loc: Loc,
        depth: u32,
        key: R,
        prefix_len: u32,
    ) -> impl DoubleEndedIterator<Item = Present> + 'static {
        self.node(loc)
            .data_cover_locs(depth, key, prefix_len)
            // SAFETY: `data_cover_locs` only yields Loc values whose bitmap bit is set, and
            // each Loc has `slot == compute_slot(data_bitmap, bit)`, so the referenced
            // cell is initialized.
            .map(move |data_loc| unsafe { Present::new(loc, data_loc, depth) })
    }

    // get an iterator over all data locations in the current node that are ancestors of (cover) the given prefix.
    pub(crate) fn data_ancestors<R: Key>(
        &self,
        loc: Loc,
        depth: u32,
        key: R,
        prefix_len: u32,
    ) -> impl Iterator<Item = Present> + 'static {
        self.node(loc)
            .data_lpm_locs(depth, key, prefix_len)
            // SAFETY: `data_lpm_locs` only yields Loc values whose bitmap bit is set, and
            // each Loc has `slot == compute_slot(data_bitmap, bit)`, so the referenced
            // cell is initialized.
            .map(move |data_loc| unsafe { Present::new(loc, data_loc, depth) })
    }

    // Create a lex iterator at a specific location
    pub(crate) fn lex_iter_at<R: Key>(&self, key: R, prefix_len: u32) -> MaskedLexIter<R> {
        let Some(element) = self.find_element(key, prefix_len).into_node() else {
            return MaskedLexIter::default();
        };
        let loc = element.node();
        let depth = element.depth();
        let mut lex = self.lex_iter(loc, depth, key);

        // Only take those that are children of the prefix
        lex.apply_data_mask(data_cover_mask(depth, key, prefix_len));
        lex.apply_child_mask(child_cover_mask(depth, key, prefix_len));

        lex
    }

    /// Get all elements in the given node.
    pub(crate) fn data_iter(
        &self,
        loc: Loc,
        depth: u32,
    ) -> impl DoubleEndedIterator<Item = Present> + 'static {
        self.node(loc)
            .data_locs()
            // SAFETY: `data_locs` only yields Loc values whose bitmap bit is set, and each Loc
            // has `slot == compute_slot(data_bitmap, bit)`, so the referenced cell is
            // initialized.
            .map(move |data_loc| unsafe { Present::new(loc, data_loc, depth) })
    }

    pub(crate) fn lex_iter<R: Key>(&self, loc: Loc, depth: u32, key: R) -> MaskedLexIter<R> {
        MaskedLexIter::new(loc, depth, key, *self.node(loc))
    }

    /// Retain only the data elements for which `f` returns `true`, removing the rest and
    /// cleaning up any empty nodes.  Returns the number of elements removed.
    ///
    /// Each node is identified by a path of child raw-offsets from root so that the Loc is
    /// always re-resolved fresh.  This avoids the stale-Loc hazard: when `cleanup_tree`
    /// removes a node it may trigger a tier-downgrade in the parent's children allocation
    /// (copy to a smaller block, free the old block).  Any pre-computed Loc whose `idx` field
    /// points into the freed block would then produce UB.
    pub(crate) fn retain_all<P: Prefix, F>(&mut self, f: &mut F) -> usize
    where
        F: FnMut(&P, &T) -> bool,
    {
        let mut removed_total = 0usize;

        // Stack of sibling groups.  Each entry: (child-offsets-from-root, depth, key).
        #[allow(clippy::type_complexity)]
        let mut stack: Vec<Vec<(Vec<u32>, u32, P::R)>> =
            vec![vec![(vec![], 0, <P::R as Zero>::zero())]];

        'main: while let Some(mut siblings) = stack.pop() {
            let Some((offsets, depth, key)) = siblings.pop() else {
                continue;
            };
            stack.push(siblings);

            // Re-resolve this node's current Loc from root and rebuild the path vector.
            let mut loc = Loc::root();
            let mut path: Vec<(Loc, u32)> = Vec::with_capacity(offsets.len());
            for &offset in &offsets {
                let Some(child_loc) = self.child(loc, offset) else {
                    continue 'main; // node was removed by a prior cleanup_tree
                };
                path.push((loc, offset));
                loc = child_loc;
            }

            // Collect bitmap bits of elements that fail the predicate.
            let mut to_remove: Vec<u32> = self
                .data_iter(loc, depth)
                .filter(|&dl| {
                    let t = self.get_data(dl);
                    let p = dl.prefix::<P>(key);
                    !f(&p, t)
                })
                .map(|dl| dl.bit())
                .collect();

            // Remove in reverse bit order so that take_data's left-shift does not
            // corrupt the physical slots of elements with lower bits still to be removed.
            // We re-read the node state before each removal to get the current data_idx (which
            // may change due to tier downgrades inside take_data).
            to_remove.sort_by_key(|&r| std::cmp::Reverse(r));
            removed_total += to_remove.len();
            for bit in to_remove {
                let node = self.node(loc);
                let data_loc = Loc::new(node.data_idx, bit, node.data_bitmap);
                // SAFETY: bit came from data_iter (bitmap bit is set) and slot is the
                // correct compute_slot result for the current bitmap.
                let present = unsafe { Present::new(loc, data_loc, depth) };
                self.take_data(present);
            }

            // Clean up this (now potentially empty) node and any empty ancestors.
            self.cleanup_tree(loc, &mut path);

            // Re-resolve to check whether cleanup_tree left this node in the tree.
            let mut cur = Loc::root();
            for &offset in &offsets {
                let Some(child_loc) = self.child(cur, offset) else {
                    continue 'main;
                };
                cur = child_loc;
            }

            // Push children as offset-path entries (not pre-computed Locs).
            let node_snap = *self.node(cur);
            if node_snap.child_bitmap != 0 {
                let children: Vec<_> = node_snap
                    .child_locs()
                    .map(|child| {
                        let mut child_offsets = offsets.clone();
                        child_offsets.push(child.bit);
                        (child_offsets, depth + K, extend_repr(key, depth, child.bit))
                    })
                    .collect();
                stack.push(children);
            }
        }

        removed_total
    }

    /// Cleanup the tree by removing empty multi-bit nodes.
    ///
    /// The `start_node` is the first one that needs to be removed. It cannot be the root (therefore
    /// is of type `NonZeroU32`, and it is only removed if it is actually empty.)
    ///
    /// The `path` is a vector from the root to the node. Each element contains the index of the
    /// previous node's parent, and the external idx of where the previous node can be found in the
    /// parent's external index vector.
    ///
    /// The function returns the first non-empty node on the path, as well as the number of nodes
    /// that were removed due to being empty.
    pub(crate) fn cleanup_tree(
        &mut self,
        start_loc: Loc,
        path: &mut Vec<(Loc, u32)>,
    ) -> (Loc, usize) {
        let mut loc = start_loc;
        let mut num_removed = 0;
        loop {
            let MultiBitNode {
                data_bitmap,
                child_bitmap,
                ..
            } = *self.node(loc);

            // Data allocations are already freed by remove_slot when the last element is removed.
            // Child group allocations are freed when clear_node_and_children processes this node.

            // break if the node is not empty, or if it is the root
            if data_bitmap != 0 || child_bitmap != 0 {
                break;
            }
            if loc.is_root() {
                break;
            }

            // mark this node as unused (without actually deleting it)
            num_removed += 1;

            // go to the parent by popping the path
            let Some((parent_loc, child_offset)) = path.pop() else {
                unreachable!("Path must go back all the way to the root");
            };
            // on that parent, remove the child pointer and compact the children allocation
            self.remove_child_at(parent_loc, child_offset);

            // continue with the parent as the idx, but only if it is not the root.
            if parent_loc.is_root() {
                // parent is the root. Immediately exit
                return (Loc::root(), num_removed);
            }
            loc = parent_loc;
        }

        (loc, num_removed)
    }

    /// Clear the entire branch, starting from the given node. This function returns the number of
    /// elements that were dropped.
    pub(crate) fn clear_node_and_children(&mut self, loc: Loc) -> usize {
        let is_all = loc.is_root();
        let mut stack = vec![loc];
        let mut count = 0;
        let mut children_to_free: Vec<(AllocIdx, usize)> = Vec::new();
        while let Some(loc) = stack.pop() {
            let node = self.node(loc);
            // push all children to the stack to be deleted as well
            stack.extend(node.child_locs());
            // remember that we need to free up all that memory (with count for tier computation).
            let child_count = node.child_bitmap.count_ones() as usize;
            children_to_free.push((node.children_idx, child_count));

            // Drop all data values and free the allocation in one shot, avoiding the slot
            // corruption that arises when take_data shifts elements during iteration.
            let node_snap = *self.node(loc);
            let data_count = node_snap.data_bitmap.count_ones() as usize;
            count += data_count;
            if data_count > 0 {
                for data_loc in node_snap.data_locs() {
                    // SAFETY: data_locs yields only initialized slots (bitmap bit is set).
                    let _ = unsafe { self.cells.remove_raw(data_loc) };
                }
                self.cells.free(node_snap.data_idx, data_count);
                self.nodes[loc].data_bitmap = 0;
                self.nodes[loc].data_idx = AllocIdx::empty();
            }
        }

        // we cleared everything
        if is_all {
            // reset the datastructures
            self.nodes.clear();
            self.cells.clear();
        } else {
            // free up all these nodes
            for (to_free, child_count) in children_to_free {
                if !to_free.is_empty() && child_count > 0 {
                    self.nodes.free(to_free, child_count);
                }
            }
        }

        count
    }

    /// Walk the entire trie and verify that every slot in both flat backing arrays is either:
    /// - referenced by a live node (via `data_idx` or `children_idx`), or
    /// - recorded in a free list.
    ///
    /// This function returns true if the memory allocation is correct.
    #[cfg(test)]
    pub(crate) fn check_memory_alloc(&self) -> bool {
        use crate::allocator::{
            CHILD_COUNT_TO_TIER, CHILD_SPACING, DATA_COUNT_TO_TIER, DATA_SPACING,
        };

        macro_rules! assert_soft {
            ($var:ident, $check:expr, $($fmt:expr),*) => {
                if !($check) {
                    $var = false;
                    eprintln!($($fmt),*);
                }
            }
        }

        let mut correct = true;

        let cell_len = self.cells.total_slots();
        let node_len = self.nodes.total_slots();

        // false = unaccounted, true = accounted (referenced or free)
        let mut cell_acc = vec![false; cell_len];
        let mut node_acc = vec![false; node_len];

        // Root node lives at flat index 0 and is never returned by alloc().
        node_acc[0] = true;

        // DFS over the live tree.
        let mut stack = vec![Loc::root()];
        while let Some(loc) = stack.pop() {
            let node = *self.node(loc);

            // -- data allocation --
            if node.data_bitmap != 0 {
                assert_soft!(
                    correct,
                    !node.data_idx.is_empty(),
                    "node at slot {} has non-zero data_bitmap but empty data_idx",
                    loc.idx.as_usize() + loc.slot as usize
                );
                let count = node.data_bitmap.count_ones() as usize;
                let cap = DATA_SPACING[DATA_COUNT_TO_TIER[count.min(31)] as usize];
                let start = node.data_idx.as_usize();
                for i in start..start + cap {
                    assert_soft!(
                        correct,
                        !cell_acc[i],
                        "cell slot {i} is referenced by more than one live node"
                    );
                    cell_acc[i] = true;
                }
            } else {
                assert_soft!(
                    correct,
                    node.data_idx.is_empty(),
                    "node at slot {} has zero data_bitmap but non-empty data_idx",
                    loc.idx.as_usize() + loc.slot as usize
                );
            }

            // -- children allocation + push children --
            if node.child_bitmap != 0 {
                assert_soft!(
                    correct,
                    !node.children_idx.is_empty(),
                    "node at slot {} has non-zero child_bitmap but empty children_idx",
                    loc.idx.as_usize() + loc.slot as usize
                );
                let count = node.child_bitmap.count_ones() as usize;
                let cap = CHILD_SPACING[CHILD_COUNT_TO_TIER[count.min(32)] as usize];
                let start = node.children_idx.as_usize();
                for i in start..start + cap {
                    assert_soft!(
                        correct,
                        !node_acc[i],
                        "node slot {i} is referenced by more than one live node"
                    );
                    node_acc[i] = true;
                }
                stack.extend(node.child_locs());
            } else {
                assert_soft!(
                    correct,
                    node.children_idx.is_empty(),
                    "node at slot {} has zero child_bitmap but non-empty children_idx",
                    loc.idx.as_usize() + loc.slot as usize
                );
            }
        }

        // -- free list entries (cells) --
        for (start, cap) in self.cells.free_list_slots() {
            for i in start..start + cap {
                assert_soft!(
                    correct,
                    !cell_acc[i],
                    "cell slot {i} appears in both the live tree and a free list"
                );
                cell_acc[i] = true;
            }
        }

        // -- free list entries (nodes) --
        for (start, cap) in self.nodes.free_list_slots() {
            for i in start..start + cap {
                assert_soft!(
                    correct,
                    !node_acc[i],
                    "node slot {i} appears in both the live tree and a free list"
                );
                node_acc[i] = true;
            }
        }

        // -- verify no leaks --
        for (i, &acc) in cell_acc.iter().enumerate() {
            assert_soft!(
                correct,
                acc,
                "cell slot {i} is leaked (neither referenced by any live node nor in any free list)"
            );
        }
        for (i, &acc) in node_acc.iter().enumerate() {
            assert_soft!(
                correct,
                acc,
                "node slot {i} is leaked (neither referenced by any live node nor in any free list)"
            );
        }

        correct
    }
}
