//! The inner node implementation.

use num_traits::Zero;

use crate::{
    allocator::{AllocIdx, CellAllocator, Loc, NodeAllocator, RawPtr},
    node::{
        child_bit, child_cover_mask, data_bit, data_cover_mask, extend_repr, Key, MaskedLexIter,
        MultiBitNode, DATA_BIT_TO_PREFIX,
    },
    prefix::mask_from_prefix_len,
    Prefix,
};

// ============================================================================
// Resolved reference types
// ============================================================================
//
// Safety model
// ────────────
// The types below borrow the `Table<T>` directly:
//   • `Present<'a, T>`    : holds `&'a Table<T>`     -> immutable, gives `&'a T`
//   • `PresentMut<'a, T>` : holds `&'a mut Table<T>` -> mutable, gives `&'a mut T`
//   • `EmptyMut<'a, T>`   : holds `&'a mut Table<T>` -> insert into an empty slot
//   • `NoNodeMut<'a, T>`  : holds `&'a mut Table<T>` -> create path + insert
//   • `Location<'a, T>`   : enum over the three mutable variants
//
// Because the borrow is held, Rust's borrow checker prevents any concurrent
// structural mutation (tier upgrade/downgrade, node insert/remove) while a
// resolved reference is alive.
//
// For iterator/retain patterns where a resolved reference cannot outlive a
// mutation, use `DataIdx` (no borrow, `Copy`) and re-resolve after each
// mutation.

/// Number of levels inside each node
pub(crate) const K: u32 = 5;
pub(crate) const NUM_DATA: usize = (1 << (K as usize)) - 1;
pub(crate) const NUM_CHILDREN: usize = 1 << (K as usize);

/// An unresolved index into the trie.
///
/// A `Copy` token that identifies a data slot without borrowing the table.
/// Obtained from iterators or the `DataIdx { node, bit, depth }` constructor.
/// Re-resolve with [`DataIdx::resolve`] / [`DataIdx::resolve_mut`].
///
/// # Safety invariant
/// `node` stores a `Loc` that was valid at construction time.  If the *node*
/// allocator has been structurally modified since (tier upgrade/downgrade on a
/// parent's children allocation), `node` may point into freed memory and
/// resolution is unsound.
#[derive(Debug, Clone, Copy)]
pub(crate) struct DataIdx {
    /// Location of the `MultiBitNode` containing this data element.
    pub(crate) node: Loc,
    /// Bitmap bit position within the node.
    pub(crate) bit: u32,
    /// Binary-tree depth of the node (multiple of `K`).
    pub(crate) depth: u32,
}

impl DataIdx {
    /// Resolve to an immutable reference.
    ///
    /// # Safety
    /// `table.nodes` must not have been structurally modified since this
    /// `DataIdx` was created; otherwise `self.node` may be dangling.
    ///
    /// Returns `None` if the bitmap bit is no longer set (element removed).
    #[inline]
    pub(crate) unsafe fn resolve<'a, T>(self, table: &'a Table<T>) -> Option<Present<'a, T>> {
        let node = table.node(self.node);
        if !node.has_data_bit(self.bit) {
            return None;
        }
        let data = Loc::new(node.data_idx, self.bit, node.data_bitmap);
        Some(Present {
            table,
            data,
            depth: self.depth,
        })
    }

    /// Resolve to a mutable reference.
    ///
    /// # Safety
    /// Same as [`DataIdx::resolve`].
    ///
    /// Returns `None` if the bitmap bit is no longer set.
    #[inline]
    pub(crate) unsafe fn resolve_mut<'a, T>(
        self,
        table: &'a mut Table<T>,
    ) -> Option<PresentMut<'a, T>> {
        let node = table.node(self.node);
        if !node.has_data_bit(self.bit) {
            return None;
        }
        let data = Loc::new(node.data_idx, self.bit, node.data_bitmap);
        Some(PresentMut {
            table,
            node: self.node,
            data,
            depth: self.depth,
        })
    }
}

/// An immutable resolved reference to a data element.
///
/// Holds `&'a Table<T>`, preventing structural mutations while alive.
pub(crate) struct Present<'a, T> {
    table: &'a Table<T>,
    data: Loc,
    depth: u32,
}

impl<'a, T> Present<'a, T> {
    /// Get a shared reference to the value, with the table's lifetime.
    #[inline]
    pub(crate) fn get(self) -> &'a T {
        // SAFETY: `Ref` is only constructed when the bitmap bit is set and
        // `data.slot == compute_slot(data_bitmap, data.bit)`.
        unsafe { self.table.cells.get(self.data) }
    }

    /// Get a mutable reference via a pre-acquired raw cell pointer.
    ///
    /// Used by [`IterMut`] to return `&'a mut T` while the iterator holds only `&'a Table<T>`.
    ///
    /// # Safety
    /// No other live `&T` or `&mut T` references to this slot must exist, and `ptr` must have
    /// been obtained from the same table.
    #[inline]
    #[allow(clippy::mut_from_ref)]
    pub(crate) unsafe fn unsafe_get_mut(self, ptr: &mut RawPtr<T>) -> &'a mut T {
        // SAFETY: `self.table` has lifetime 'a; `cells.unsafe_get_mut` is parameterized by
        // that lifetime, so the returned reference inherits lifetime 'a from the table borrow.
        unsafe { self.table.cells.unsafe_get_mut(ptr, self.data) }
    }

    /// Compute the prefix of this element.
    pub(crate) fn prefix<P: Prefix>(&self, key: P::R) -> P {
        prefix(key, self.depth, self.data.bit as usize)
    }
}

/// A mutable resolved reference to a data element.
///
/// Holds `&'a mut Table<T>`, preventing any concurrent access.
pub(crate) struct PresentMut<'a, T> {
    table: &'a mut Table<T>,
    node: Loc,
    data: Loc,
    depth: u32,
}

impl<'a, T> PresentMut<'a, T> {
    /// Get a mutable reference to the value, with the table's lifetime.
    /// Consumes `self` so that the exclusive borrow is released into `&'a mut T`.
    #[inline]
    pub(crate) fn get_mut(self) -> &'a mut T {
        // SAFETY: bitmap bit is set, slot is correct, exclusive `&mut Table`.
        unsafe { self.table.cells.get_mut(self.data) }
    }

    /// Get a shared reference to the value.
    #[inline]
    pub(crate) fn get(&self) -> &T {
        // SAFETY: bitmap bit is set, slot is correct.
        unsafe { self.table.cells.get(self.data) }
    }

    /// Get a mutable reference to the value, borrowing `self` mutably.
    /// Unlike [`get_mut`], this does not consume `self`, so the `PresentMut` remains usable.
    #[inline]
    pub(crate) fn as_mut(&mut self) -> &mut T {
        // SAFETY: bitmap bit is set, slot is correct, exclusive `&mut Table` via `&mut self`.
        unsafe { self.table.cells.get_mut(self.data) }
    }

    /// Replace the value, returning the old one. Consumes `self`.
    #[inline]
    pub(crate) fn replace(self, val: T) -> T {
        // SAFETY: bitmap bit is set, slot is correct.
        unsafe { self.table.cells.replace(self.data, val) }
    }

    /// Remove and return the value. Consumes `self`.
    #[inline]
    pub(crate) fn take(self) -> T {
        self.table
            .cells
            .remove_bit(&mut self.table.nodes[self.node], self.data)
    }

    /// Compute the prefix of this element.
    pub(crate) fn prefix<P: Prefix>(&self, key: P::R) -> P {
        prefix(key, self.depth, self.data.bit as usize)
    }
}

/// A resolved reference to an *empty* data slot (bitmap bit is **not** set).
///
/// Holds `&'a mut Table<T>`.
pub(crate) struct EmptyMut<'a, T> {
    pub(crate) table: &'a mut Table<T>,
    pub(crate) node: Loc,
    pub(crate) data_bit: u32,
    pub(crate) depth: u32,
}

impl<'a, T> EmptyMut<'a, T> {
    /// Insert a value, consuming `self` and returning a mutable reference to
    /// the newly inserted element.
    #[inline]
    pub(crate) fn insert(self, val: T) -> PresentMut<'a, T> {
        let data =
            self.table
                .cells
                .insert_new_bit(&mut self.table.nodes[self.node], self.data_bit, val);
        PresentMut {
            table: self.table,
            node: self.node,
            data,
            depth: self.depth,
        }
    }
}

/// The last reachable node when no intermediate trie node exists on the path
/// to the target prefix.
pub(crate) struct NoNodeMut<'a, T> {
    pub(crate) table: &'a mut Table<T>,
    pub(crate) last_node: Loc,
    pub(crate) last_depth: u32,
}

impl<'a, T> NoNodeMut<'a, T> {
    /// Take one step toward `(key, prefix_len)`.
    ///
    /// If the target prefix fits within the current node (i.e. `prefix_len < last_depth + K`),
    /// returns `Ok(EmptyMut)` ready for insertion.  Otherwise creates the next child node
    /// (the `NoNodeMut` invariant guarantees it is absent) and returns `Err(NoNodeMut)` pointing
    /// one level deeper.
    #[inline(always)]
    pub(crate) fn advance<R: Key>(self, key: R, prefix_len: u32) -> Result<EmptyMut<'a, T>, Self> {
        let NoNodeMut {
            table,
            last_node,
            last_depth,
        } = self;
        if prefix_len < last_depth + K {
            let data_bit = data_bit(key, prefix_len);
            Ok(EmptyMut {
                table,
                node: last_node,
                data_bit,
                depth: last_depth,
            })
        } else {
            let child_bit = child_bit(last_depth, key);
            // SAFETY: `NoNodeMut` is only constructed when `find_mut` (or a prior `advance`)
            // could not follow the child pointer at `(last_node, child_bit)` — meaning that
            // child bit is guaranteed to be unset in `last_node`'s child_bitmap.
            // `insert_new_bit` requires the bit to be clear (asserted in debug mode); this
            // invariant is upheld here.
            let next_node = table.nodes.insert_new_bit(last_node, child_bit);
            Err(NoNodeMut {
                table,
                last_node: next_node,
                last_depth: last_depth + K,
            })
        }
    }

    /// Create all intermediate trie nodes needed to reach `(key, prefix_len)` and insert `val`.
    /// The `NoNodeMut` invariant guarantees the data slot is unoccupied.
    pub(crate) fn insert_path_and_data<R: Key>(
        mut self,
        key: R,
        prefix_len: u32,
        val: T,
    ) -> PresentMut<'a, T> {
        loop {
            match self.advance(key, prefix_len) {
                Ok(empty) => return empty.insert(val),
                Err(next) => self = next,
            }
        }
    }
}

/// Result of a mutable lookup.
pub(crate) enum Location<'a, T> {
    Present(PresentMut<'a, T>),
    Empty(EmptyMut<'a, T>),
    NoNode(NoNodeMut<'a, T>),
}

impl<'a, T> Location<'a, T> {
    /// Return the inner `PresentMut` if the slot is occupied, `None` otherwise.
    #[inline]
    pub(crate) fn present(self) -> Option<PresentMut<'a, T>> {
        match self {
            Location::Present(p) => Some(p),
            _ => None,
        }
    }

    /// Return the node `Loc` regardless of variant.
    #[inline]
    pub(crate) fn node_loc(&self) -> Loc {
        match self {
            Location::Present(p) => p.node,
            Location::Empty(e) => e.node,
            Location::NoNode(n) => n.last_node,
        }
    }

    /// Return the depth regardless of variant.
    #[inline]
    pub(crate) fn depth(&self) -> u32 {
        match self {
            Location::Present(p) => p.depth,
            Location::Empty(e) => e.depth,
            Location::NoNode(n) => n.last_depth,
        }
    }
}

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

impl<T> Drop for Table<T> {
    fn drop(&mut self) {
        self.drop_values();
    }
}

// Safety:
// `CellAllocator` uses `UnsafeCell`, making `Table` `!Sync` by default. Manual impls are sound:
// - Send: owning a Table (or &mut Table) and moving it across threads is safe — no external
//   references can exist while the move happens.
// - Sync: sharing `&Table` across threads is safe because `unsafe_get_mut` (the only path that
//   produces `&mut T` from `&Table`) requires a `RawPtr` obtained from `&mut Table` and is only
//   used in `IterMut`/`TrieRefMut`, which enforce disjoint access via the acyclic tree structure.
unsafe impl<T: Send> Send for Table<T> {}
unsafe impl<T: Sync> Sync for Table<T> {}

impl<T> Table<T> {
    pub(crate) fn raw_cells(&mut self) -> RawPtr<T> {
        self.cells.raw_ptr()
    }

    #[inline(always)]
    pub(crate) fn node(&self, pos: Loc) -> &MultiBitNode {
        &self.nodes[pos]
    }

    /// Return the child node at `child_bit`, or `None` if absent.
    // SAFETY: `pos` must be a valid, live node location: the `AllocIdx` inside `pos` must
    // still point into the active node allocation (i.e. no tier upgrade/downgrade of `pos`'s
    // parent has occurred since `pos` was obtained).
    #[inline(always)]
    pub(crate) unsafe fn child(&self, pos: Loc, child_bit: u32) -> Option<Loc> {
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
    /// Simply clearing the bit would leave the physical array unchanged, making remaining
    /// children inaccessible at the wrong slots. This function shifts the array and handles
    /// tier downgrades.
    ///
    /// # Safety
    /// `parent_loc` must be a valid, live node location (same invariant as [`Self::child`]).
    #[inline(always)]
    pub(crate) unsafe fn remove_child_at(&mut self, parent_loc: Loc, child_bit: u32) {
        self.nodes.remove_bit(parent_loc, child_bit);
    }

    pub(crate) fn mem_size(&self) -> usize {
        self.nodes.mem_size() + self.cells.mem_size()
    }

    fn drop_values(&mut self) {
        let mut stack = vec![Loc::root()];
        while let Some(loc) = stack.pop() {
            let node = *self.node(loc);
            stack.extend(node.child_locs());

            for data_loc in node.data_locs() {
                // SAFETY: data_locs yields only initialized slots from the live node snapshot.
                let _ = unsafe { self.cells.remove_raw(data_loc) };
            }
        }
    }

    /// Traverse child pointers to the `MultiBitNode` containing `prefix_len`.
    /// Returns `(node_loc, depth)` on success, or `None` if any required child is absent.
    /// This is the shared traversal primitive used by all `find_*` methods.
    #[inline(always)]
    fn find_loc<R: Key>(&self, key: R, prefix_len: u32) -> Option<(Loc, u32)> {
        let mut loc = Loc::root();
        let mut depth = 0u32;
        while prefix_len >= depth + K {
            let cb = child_bit(depth, key);
            // SAFETY: `loc` starts as `Loc::root()` (always valid) and is only updated
            // to the result of a prior `child()` call, which always returns a valid `Loc`.
            let Some(next) = (unsafe { self.child(loc, cb) }) else {
                return None;
            };
            loc = next;
            depth += K;
        }
        Some((loc, depth))
    }

    /// Find the exact prefix and return an immutable reference.
    /// Returns `None` if the prefix is absent.
    #[inline(always)]
    pub(crate) fn find<R: Key>(&self, key: R, prefix_len: u32) -> Option<Present<'_, T>> {
        let (loc, depth) = self.find_loc(key, prefix_len)?;
        let node = self.node(loc);
        let db = data_bit(key, prefix_len);
        if node.has_data_bit(db) {
            let data = Loc::new(node.data_idx, db, node.data_bitmap);
            Some(Present {
                table: self,
                data,
                depth,
            })
        } else {
            None
        }
    }

    /// Find the longest-prefix match and return an immutable reference.
    #[inline(always)]
    pub(crate) fn find_lpm<R: Key>(&self, key: R, prefix_len: u32) -> Option<Present<'_, T>> {
        let mut loc = Loc::root();
        let mut depth = 0;
        let mut lpm: Option<Present<'_, T>> = None;

        loop {
            let node = self.node(loc);
            if let Some(data_loc) = node.data_lpm_loc(depth, key, prefix_len) {
                lpm = Some(Present {
                    table: self,
                    data: data_loc,
                    depth,
                });
            }
            if prefix_len < depth + K {
                return lpm;
            }
            let child_bit = child_bit(depth, key);
            // SAFETY: `loc` starts as `Loc::root()` and is only updated to the result
            // of a prior `child()` call, which always returns a valid `Loc`.
            let Some(next) = (unsafe { self.child(loc, child_bit) }) else {
                return lpm;
            };
            loc = next;
            depth += K;
        }
    }

    /// Find the longest-prefix match and return a mutable reference.
    #[inline(always)]
    pub(crate) fn find_lpm_mut<R: Key>(
        &mut self,
        key: R,
        prefix_len: u32,
    ) -> Option<PresentMut<'_, T>> {
        let mut loc = Loc::root();
        let mut depth = 0;
        let mut lpm: Option<(Loc, Loc, u32)> = None; // (node, data, depth)

        loop {
            let node = self.node(loc);
            if let Some(data_loc) = node.data_lpm_loc(depth, key, prefix_len) {
                lpm = Some((loc, data_loc, depth));
            }
            if prefix_len < depth + K {
                break;
            }
            let child_bit = child_bit(depth, key);
            // SAFETY: `loc` starts as `Loc::root()` and is only updated to the result
            // of a prior `child()` call, which always returns a valid `Loc`.
            let Some(next) = (unsafe { self.child(loc, child_bit) }) else {
                break;
            };
            loc = next;
            depth += K;
        }

        let (node, data, depth) = lpm?;
        // Re-read node to get fresh data_idx after any mutations; here there are none,
        // but we re-read for consistency and to satisfy the borrow checker.
        let node_snap = self.node(node);
        let data = Loc::new(node_snap.data_idx, data.bit, node_snap.data_bitmap);
        Some(PresentMut {
            table: self,
            node,
            data,
            depth,
        })
    }

    /// Find the shortest-prefix match and return an immutable reference.
    #[inline(always)]
    pub(crate) fn find_spm<R: Key>(&self, key: R, prefix_len: u32) -> Option<Present<'_, T>> {
        let mut loc = Loc::root();
        let mut depth = 0;

        loop {
            let node = self.node(loc);
            if let Some(data_loc) = node.data_spm_loc(depth, key, prefix_len) {
                return Some(Present {
                    table: self,
                    data: data_loc,
                    depth,
                });
            }
            if prefix_len < depth + K {
                return None;
            }
            let child_bit = child_bit(depth, key);
            // SAFETY: `loc` starts as `Loc::root()` and is only updated to the result
            // of a prior `child()` call, which always returns a valid `Loc`.
            loc = unsafe { self.child(loc, child_bit) }?;
            depth += K;
        }
    }

    /// Find the exact prefix and return a mutable location (present / empty /
    /// no-node).
    #[inline(always)]
    pub(crate) fn find_mut<R: Key>(&mut self, key: R, prefix_len: u32) -> Location<'_, T> {
        let mut loc = Loc::root();
        let mut depth = 0;
        while prefix_len >= depth + K {
            let child_bit = child_bit(depth, key);
            // SAFETY: `loc` starts as `Loc::root()` and is only updated to the result
            // of a prior `child()` call, which always returns a valid `Loc`.
            let Some(next) = (unsafe { self.child(loc, child_bit) }) else {
                return Location::NoNode(NoNodeMut {
                    table: self,
                    last_node: loc,
                    last_depth: depth,
                });
            };
            loc = next;
            depth += K;
        }
        let db = data_bit(key, prefix_len);
        let node = self.node(loc);
        if node.has_data_bit(db) {
            let data = Loc::new(node.data_idx, db, node.data_bitmap);
            Location::Present(PresentMut {
                table: self,
                node: loc,
                data,
                depth,
            })
        } else {
            Location::Empty(EmptyMut {
                table: self,
                node: loc,
                data_bit: db,
                depth,
            })
        }
    }

    /// Find the exact prefix, creating intermediate nodes if necessary.
    /// Returns `Ok(PresentMut)` if the element already exists, or `Err(EmptyMut)`
    /// if the slot is available for insertion.
    #[inline(always)]
    pub(crate) fn find_or_insert_mut<R: Key>(
        &mut self,
        key: R,
        prefix_len: u32,
    ) -> Result<PresentMut<'_, T>, EmptyMut<'_, T>> {
        let mut loc = Loc::root();
        let mut depth = 0;
        while prefix_len >= depth + K {
            let cb = child_bit(depth, key);
            // SAFETY: `loc` starts as `Loc::root()` (always valid) and is only updated to
            // the result of a previous `child()` call or `insert_new_bit()`, both of which
            // return a valid `Loc`.
            loc = match unsafe { self.child(loc, cb) } {
                Some(next) => next,
                None => self.nodes.insert_new_bit(loc, cb),
            };
            depth += K;
        }
        let db = data_bit(key, prefix_len);
        let node = self.node(loc);
        if node.has_data_bit(db) {
            let data = Loc::new(node.data_idx, db, node.data_bitmap);
            Ok(PresentMut {
                table: self,
                node: loc,
                data,
                depth,
            })
        } else {
            Err(EmptyMut {
                table: self,
                node: loc,
                data_bit: db,
                depth,
            })
        }
    }

    /// Find the exact prefix with path, returning a mutable location.
    /// The path is a vector of `(parent_loc, child_bit)` from root to the node.
    #[inline(always)]
    #[allow(clippy::type_complexity)]
    pub(crate) fn find_mut_with_path<R: Key>(
        &mut self,
        key: R,
        prefix_len: u32,
    ) -> Option<(Location<'_, T>, Vec<(Loc, u32)>)> {
        let mut path: Vec<(Loc, u32)> = Vec::new();
        let mut loc = Loc::root();
        let mut depth = 0;
        while prefix_len >= depth + K {
            let child_bit = child_bit(depth, key);
            // SAFETY: `loc` starts as `Loc::root()` and is only updated to the result
            // of a prior `child()` call, which always returns a valid `Loc`.
            let next_loc = unsafe { self.child(loc, child_bit) }?;
            path.push((loc, child_bit));
            loc = next_loc;
            depth += K;
        }
        let db = data_bit(key, prefix_len);
        let node = self.node(loc);
        let loc_mut = if node.has_data_bit(db) {
            let data = Loc::new(node.data_idx, db, node.data_bitmap);
            Location::Present(PresentMut {
                table: self,
                node: loc,
                data,
                depth,
            })
        } else {
            Location::Empty(EmptyMut {
                table: self,
                node: loc,
                data_bit: db,
                depth,
            })
        };
        Some((loc_mut, path))
    }

    /// Iterate over all data slots in `loc` that are descendants of `(key, prefix_len)`.
    ///
    /// # Safety
    /// `loc` must be a valid, live node location: the `AllocIdx` inside `loc` must still point
    /// into the active node allocation (i.e. no tier upgrade/downgrade of `loc`'s parent has
    /// occurred since `loc` was obtained).
    pub(crate) unsafe fn data_descendants<R: Key>(
        &self,
        loc: Loc,
        depth: u32,
        key: R,
        prefix_len: u32,
    ) -> impl DoubleEndedIterator<Item = DataIdx> + 'static {
        self.node(loc)
            .data_cover_locs(depth, key, prefix_len)
            .map(move |data_loc| DataIdx {
                node: loc,
                bit: data_loc.bit,
                depth,
            })
    }

    /// Iterate over all data slots in `loc` that are ancestors of (cover) `(key, prefix_len)`.
    ///
    /// # Safety
    /// `loc` must be a valid, live node location: the `AllocIdx` inside `loc` must still point
    /// into the active node allocation (i.e. no tier upgrade/downgrade of `loc`'s parent has
    /// occurred since `loc` was obtained).
    pub(crate) unsafe fn data_ancestors<R: Key>(
        &self,
        loc: Loc,
        depth: u32,
        key: R,
        prefix_len: u32,
    ) -> impl Iterator<Item = DataIdx> + 'static {
        self.node(loc)
            .data_lpm_locs(depth, key, prefix_len)
            .map(move |data_loc| DataIdx {
                node: loc,
                bit: data_loc.bit,
                depth,
            })
    }

    // Create a lex iterator at a specific location
    pub(crate) fn lex_iter_at<R: Key>(&self, key: R, prefix_len: u32) -> MaskedLexIter<R> {
        let Some((loc, depth)) = self.find_loc(key, prefix_len) else {
            return MaskedLexIter::default();
        };
        // SAFETY: `find_loc` traversed from `Loc::root()` to `loc`; since the traversal
        // completed without structural mutations, `loc` is a valid, live node location.
        let mut lex = unsafe { self.lex_iter(loc, depth, key) };
        // Only take those that are children of the prefix
        lex.apply_data_mask(data_cover_mask(depth, key, prefix_len));
        lex.apply_child_mask(child_cover_mask(depth, key, prefix_len));
        lex
    }

    /// Iterate over all data slots in `loc`.
    ///
    /// # Safety
    /// `loc` must be a valid, live node location: the `AllocIdx` inside `loc` must still point
    /// into the active node allocation (i.e. no tier upgrade/downgrade of `loc`'s parent has
    /// occurred since `loc` was obtained).
    pub(crate) unsafe fn data_iter(
        &self,
        loc: Loc,
        depth: u32,
    ) -> impl DoubleEndedIterator<Item = DataIdx> + 'static {
        self.node(loc).data_locs().map(move |data_loc| DataIdx {
            node: loc,
            bit: data_loc.bit,
            depth,
        })
    }

    /// Build a lexicographic iterator rooted at `loc`.
    ///
    /// # Safety
    /// `loc` must be a valid, live node location: the `AllocIdx` inside `loc` must still point
    /// into the active node allocation (i.e. no tier upgrade/downgrade of `loc`'s parent has
    /// occurred since `loc` was obtained).
    pub(crate) unsafe fn lex_iter<R: Key>(&self, loc: Loc, depth: u32, key: R) -> MaskedLexIter<R> {
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
                // SAFETY: `loc` starts as `Loc::root()` and is only updated to the result
                // of a prior `child()` call, which always returns a valid `Loc`.
                let Some(child_loc) = (unsafe { self.child(loc, offset) }) else {
                    continue 'main; // node was removed by a prior cleanup_tree
                };
                path.push((loc, offset));
                loc = child_loc;
            }

            // Collect bitmap bits of elements that fail the predicate.
            // SAFETY: `loc` was obtained by re-traversing from root above; no structural
            // mutations have occurred since, so `loc` is a valid, live node location.
            let to_remove: Vec<u32> = unsafe { self.data_iter(loc, depth) }
                .filter(|&dl| {
                    // SAFETY: data_iter yields bits set in the current bitmap; retain_all does
                    // not mutate node structure during this read-only scan.
                    let r = unsafe { dl.resolve(self) }.expect("data_iter: bit not in bitmap");
                    !f(&r.prefix::<P>(key), r.get())
                })
                .map(|dl| dl.bit)
                .collect();

            removed_total += to_remove.len();
            for bit in to_remove {
                let idx = DataIdx {
                    node: loc,
                    bit,
                    depth,
                };
                // SAFETY: bit came from data_iter (set in bitmap). `resolve_mut` re-reads the
                // current node state, so stale data-AllocIdx from tier downgrades are handled.
                // `loc` itself remains valid: data removals only touch the node's data allocation,
                // not the parent's children allocation where `loc` resides.
                let r = unsafe { idx.resolve_mut(self) }.expect("retain_all: bit not in bitmap");
                r.take();
            }

            // Clean up this (now potentially empty) node and any empty ancestors.
            // SAFETY: `loc` was re-traversed fresh above; data removals do not alter node
            // structure, so all `Loc`s in `path` (and `loc` itself) are still valid.
            unsafe { self.cleanup_tree(loc, &mut path) };

            // Re-resolve to check whether cleanup_tree left this node in the tree.
            let mut cur = Loc::root();
            for &offset in &offsets {
                // SAFETY: same re-traversal-from-root invariant as the first loop above.
                let Some(child_loc) = (unsafe { self.child(cur, offset) }) else {
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

    /// Walk up from `start_loc` toward the root, removing empty nodes.
    ///
    /// `path` is a vector of `(parent_loc, child_bit)` pairs from the root down to `start_loc`.
    /// Returns `(first_non_empty_loc, num_removed)`.
    ///
    /// # Safety
    /// `start_loc` and every `Loc` in `path` must be valid, live node locations: their
    /// `AllocIdx` values must still point into the active node allocation (i.e. no tier
    /// upgrade/downgrade has occurred on any node in the path since those `Loc`s were obtained).
    pub(crate) unsafe fn cleanup_tree(
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
            // on that parent, remove the child pointer and compact the children allocation.
            // SAFETY: caller guarantees all `Loc`s in `path` are valid (see # Safety above).
            // `remove_child_at` may reallocate the parent's *children* block, but `parent_loc`
            // itself lives in the *grandparent's* children block, which is unaffected.
            unsafe { self.remove_child_at(parent_loc, child_offset) };

            // continue with the parent as the idx, but only if it is not the root.
            if parent_loc.is_root() {
                // parent is the root. Immediately exit
                return (Loc::root(), num_removed);
            }
            loc = parent_loc;
        }

        (loc, num_removed)
    }

    /// Clear the entire branch rooted at `loc`, dropping all values. Returns the count dropped.
    ///
    /// # Safety
    /// `loc` must be a valid, live node location: the `AllocIdx` inside `loc` must still point
    /// into the active node allocation (i.e. no tier upgrade/downgrade of `loc`'s parent has
    /// occurred since `loc` was obtained).
    pub(crate) unsafe fn clear_node_and_children(&mut self, loc: Loc) -> usize {
        let is_all = loc.is_root();
        let mut stack = vec![loc];
        let mut count = 0;
        let mut children_to_free: Vec<(AllocIdx, usize)> = Vec::new();
        while let Some(loc) = stack.pop() {
            let node_snap = *self.node(loc);
            // push all children to the stack to be deleted as well
            stack.extend(node_snap.child_locs());
            // remember that we need to free up all that memory (with count for tier computation).
            let child_count = node_snap.child_bitmap.count_ones() as usize;
            children_to_free.push((node_snap.children_idx, child_count));

            // Drop all data values and free the allocation in one shot, avoiding the slot
            // corruption that arises when take_data shifts elements during iteration.
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
                for (i, item) in cell_acc.iter_mut().enumerate().skip(start).take(cap) {
                    assert_soft!(
                        correct,
                        !*item,
                        "cell slot {i} is referenced by more than one live node"
                    );
                    *item = true;
                }
            } else {
                assert_soft!(
                    correct,
                    node.data_idx.is_empty(),
                    "cell at slot {} has zero data_bitmap but non-empty data_idx",
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
                for (i, item) in node_acc.iter_mut().enumerate().skip(start).take(cap) {
                    assert_soft!(
                        correct,
                        !*item,
                        "node slot {i} is referenced by more than one live node"
                    );
                    *item = true;
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
            for (i, item) in cell_acc.iter_mut().enumerate().skip(start).take(cap) {
                assert_soft!(
                    correct,
                    !*item,
                    "cell slot {i} appears in both the live tree and a free list"
                );
                *item = true;
            }
        }

        // -- free list entries (nodes) --
        for (start, cap) in self.nodes.free_list_slots() {
            for (i, item) in node_acc.iter_mut().enumerate().skip(start).take(cap) {
                assert_soft!(
                    correct,
                    !*item,
                    "node slot {i} appears in both the live tree and a free list"
                );
                *item = true;
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

impl<T: Clone> Clone for Table<T> {
    fn clone(&self) -> Self {
        let mut x = Self {
            nodes: self.nodes.clone(),
            cells: Default::default(),
        };

        // The cloned node allocator initially contains data_idx values that point into `self`.
        // Clear live data metadata first so `x` can be dropped safely if T::clone panics below.
        let mut stack = vec![Loc::root()];
        while let Some(loc) = stack.pop() {
            let node = self.nodes[loc];
            x.nodes[loc].data_bitmap = 0;
            x.nodes[loc].data_idx = AllocIdx::empty();
            if node.child_bitmap != 0 {
                stack.extend(node.child_locs());
            }
        }

        // Clone only live nodes reachable from root via DFS. Freed nodes in the flat
        // array may have stale data_bitmap/data_idx from tier upgrades; visiting them
        // would allocate cells that are never freed, causing a memory leak.
        let mut stack = vec![Loc::root()];
        while let Some(loc) = stack.pop() {
            let node = self.nodes[loc];
            if node.data_bitmap != 0 && !node.data_idx.is_empty() {
                let count = node.data_bitmap.count_ones() as usize;
                let data_idx = x.cells.alloc(count);
                x.nodes[loc].data_idx = data_idx;
                for data_loc in node.data_locs() {
                    // SAFETY: `data_loc` from source's live bitmap; entry is initialized.
                    let val = unsafe { self.cells.get(data_loc) }.clone();
                    unsafe { x.cells.write_at(data_idx, data_loc.slot, val) };
                    x.nodes[loc].set_data_bit(data_loc.bit);
                }
            }
            if node.child_bitmap != 0 {
                stack.extend(node.child_locs());
            }
        }

        x
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
