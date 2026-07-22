//! Module containing the archived prefix map and access methods.

use std::marker::PhantomData;

#[repr(transparent)]
#[derive(Portable, CheckBytes)]
#[bytecheck(crate = rkyv::bytecheck)]
pub(super) struct MyPhantomData<T>(pub(super) PhantomData<T>);

// Safety: PhantomData is zero-sized, so it cannot have an undefined value by definition.
unsafe impl<T> NoUndef for MyPhantomData<T> {}

use num_traits::{CheckedAdd, One, Zero};
use rkyv::{
    bytecheck::CheckBytes,
    traits::NoUndef,
    vec::{ArchivedVec, VecResolver},
    Archive, Portable, Serialize,
};

use crate::{
    aggregate::member_coverage,
    allocator::compute_slot,
    node::{child_bit, data_bit, data_lpm_mask, Key, DATA_BIT_TO_PREFIX},
    table::{reconstruct_prefix, K, NUM_CHILDREN, NUM_DATA},
    Prefix,
};

/// Archived (immutable) version of a [`PrefixMap`].
///
/// Any (verified) archived prefix map is canonical and has the following properties:
/// - The tree is stored as BFS (ordered per level).
/// - Data is stored contiguously without empty (uninitialized) memory in between.
/// - The root node is always present.
/// - No node (except the root) may be emtpy.
///
/// Due to these properties, assuming that T is also canonical (i.e., has only one possible
/// representation), you can compare two `ArchivedPrefixMap`s for equality by comparing their byte
/// string.
#[repr(C)]
#[derive(Portable, CheckBytes)]
#[bytecheck(verify, crate = rkyv::bytecheck)]
pub struct ArchivedPrefixMap<P, T: Archive> {
    pub(super) nodes: ArchivedVec<ArchivedNodeRepr>,
    pub(super) data: ArchivedVec<T::Archived>,
    pub(super) marker: MyPhantomData<P>,
}

impl<P, T: Archive> ArchivedPrefixMap<P, T> {
    /// Returns the number of elements stored in `self`.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

impl<P: Prefix, T: Archive> ArchivedPrefixMap<P, T> {
    /// Count the number of unique addresses covered by all prefixes in the map. If the entire trie
    /// is fully covered, the function returns `None` (as it contains `P::R::MAX + 1` addresses).
    /// Overlapping prefixes are not double-counted.
    ///
    /// To avoid double-counting, the function traverses the (partial) trie once, skipping nodes
    /// that are already covered.
    ///
    /// See [`PrefixMap::address_count`] for an example.
    pub fn address_count(&self) -> Option<P::R> {
        // check if the trie is fully covered by a single root node
        if self.nodes[0].has_data_bit(0) {
            return None;
        }
        // otherwise, traverse the tree
        self.address_count_at(0, 0)
    }

    /// Get the value of an element by matching exactly on the prefix.
    ///
    /// See [`PrefixMap::get`] for an example.
    pub fn get<'a>(&'a self, prefix: &P) -> Option<&'a T::Archived> {
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        let (loc, _) = self.find_loc(key, prefix_len)?;
        let bit = data_bit(key, prefix_len);
        let data_loc = self.nodes[loc.idx()].data_loc(bit)?;
        Some(&self.data[data_loc.idx()])
    }

    /// Get the value of an element by matching exactly on the prefix, plus the (canonical version)
    /// of the matched prefix.
    ///
    /// **Warning**: The table does not store the prefix, but it is reconstructed. This means that
    /// any bits in the host part will be truncated.
    ///
    /// See [`PrefixMap::get_key_value`] for an example.
    pub fn get_key_value<'a>(&'a self, prefix: &P) -> Option<(P, &'a T::Archived)> {
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        let (loc, depth) = self.find_loc(key, prefix_len)?;
        let bit = data_bit(key, prefix_len);
        let data_loc = self.nodes[loc.idx()].data_loc(bit)?;
        let prefix = reconstruct_prefix(key, depth, data_loc.bit as usize);
        Some((prefix, &self.data[data_loc.idx()]))
    }

    /// Get the value of an address or prefix using longest prefix matching.
    ///
    /// See [`PrefixMap::get_lpm`] for an example.
    pub fn get_lpm<'a>(&'a self, prefix: &P) -> Option<(P, &'a T::Archived)> {
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        let (data_loc, depth) = self.find_lpm(key, prefix_len)?;
        let prefix = reconstruct_prefix(key, depth, data_loc.bit as usize);
        Some((prefix, &self.data[data_loc.idx()]))
    }

    /// recursive function to compute the address count.
    fn address_count_at(&self, loc: u32, depth: u32) -> Option<P::R> {
        let node = &self.nodes[loc as usize];
        let data_bitmap = node.data_bitmap();
        let (covered_data, covered_children) = member_coverage(data_bitmap);
        let mut count = P::R::zero();

        for bit in 0..NUM_DATA as u32 {
            if data_bitmap & !covered_data & (1 << bit) == 0 {
                continue;
            }
            let prefix_len = depth + DATA_BIT_TO_PREFIX[bit as usize].1 as u32;
            let host_bits = P::num_bits() - prefix_len;
            let addresses = P::R::one() << host_bits as usize;
            count = count.checked_add(&addresses)?;
        }

        for child in node.child_locs() {
            if covered_children & (1 << child.bit) == 0 {
                let child_count = self.address_count_at(child.idx, depth + K)?;
                count = count.checked_add(&child_count)?;
            }
        }

        Some(count)
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
            loc = self.nodes[loc.idx()].child_loc(cb)?;
            depth += K;
        }
        Some((loc, depth))
    }

    /// Find the longest-prefix match and return the position of the data of the LPM match, plus the
    /// depth of the node containing this data.
    #[inline(always)]
    fn find_lpm<R: Key>(&self, key: R, prefix_len: u32) -> Option<(Loc, u32)> {
        let mut loc = Loc::root();
        let mut depth = 0;
        let mut lpm: Option<(Loc, u32)> = None;

        loop {
            let node = &self.nodes[loc.idx()];
            if let Some(data_loc) = node.data_lpm_loc(depth, key, prefix_len) {
                lpm = Some((data_loc, depth));
            }
            if prefix_len < depth + K {
                return lpm;
            }
            let child_bit = child_bit(depth, key);
            // SAFETY: `loc` starts as `Loc::root()` and is only updated to the result
            // of a prior `child()` call, which always returns a valid `Loc`.
            let Some(next) = self.nodes[loc.idx()].child_loc(child_bit) else {
                return lpm;
            };
            loc = next;
            depth += K;
        }
    }
}

/// Rkyv representation of a node with compacted indices
#[derive(Archive, Serialize, Default)]
#[rkyv(derive(Debug))]
pub(super) struct NodeRepr {
    pub(super) data_bitmap: u32,
    pub(super) child_bitmap: u32,
    pub(super) data_idx: u32,
    pub(super) children_idx: u32,
}

impl ArchivedNodeRepr {
    #[inline(always)]
    pub(super) fn data_idx(&self) -> u32 {
        self.data_idx.to_native()
    }

    #[inline(always)]
    pub(super) fn data_bitmap(&self) -> u32 {
        self.data_bitmap.to_native()
    }

    #[inline(always)]
    pub(super) fn has_data_bit(&self, bit: u32) -> bool {
        self.data_bitmap() & (1 << bit) != 0
    }

    /// Get the location of the given data bit (only if it is set)
    pub(super) fn data_loc(&self, bit: u32) -> Option<Loc> {
        if self.has_data_bit(bit) {
            Some(Loc {
                idx: self.data_idx() + compute_slot(self.data_bitmap(), bit),
                bit,
            })
        } else {
            None
        }
    }

    /// Get an iterator over all indices of data.
    #[inline(always)]
    pub(super) fn data_locs(&self) -> impl DoubleEndedIterator<Item = Loc> + 'static {
        let bitmap = self.data_bitmap();
        let offset = self.data_idx();
        (0..(NUM_CHILDREN as u32))
            .filter(move |&bit| bitmap & (1 << bit) != 0)
            .map(move |bit| Loc {
                idx: offset + compute_slot(bitmap, bit),
                bit,
            })
    }

    #[inline(always)]
    pub(super) fn children_idx(&self) -> u32 {
        self.children_idx.to_native()
    }

    #[inline(always)]
    pub(super) fn child_bitmap(&self) -> u32 {
        self.child_bitmap.to_native()
    }

    #[inline(always)]
    pub(super) fn has_child_bit(&self, bit: u32) -> bool {
        self.child_bitmap() & (1 << bit) != 0
    }

    /// Get the location of the given data bit (only if it is set)
    pub(super) fn child_loc(&self, bit: u32) -> Option<Loc> {
        if self.has_child_bit(bit) {
            Some(Loc {
                idx: self.children_idx() + compute_slot(self.child_bitmap(), bit),
                bit,
            })
        } else {
            None
        }
    }

    /// Get an iterator over all children.
    #[inline(always)]
    pub(super) fn child_locs(&self) -> impl DoubleEndedIterator<Item = Loc> + 'static {
        let bitmap = self.child_bitmap();
        let offset = self.children_idx();
        (0..(NUM_CHILDREN as u32))
            .filter(move |&bit| bitmap & (1 << bit) != 0)
            .map(move |bit| Loc {
                idx: offset + compute_slot(bitmap, bit),
                bit,
            })
    }

    /// Get the data loc of the longest prefix match in this node (if it exists).
    /// Returns Loc with bit (bitmap position) and computed slot.
    #[inline(always)]
    fn data_lpm_loc<R: Key>(&self, depth: u32, key: R, prefix_len: u32) -> Option<Loc> {
        let nodes_present = self.data_bitmap & data_lpm_mask(depth, key, prefix_len);
        if nodes_present == 0 {
            return None;
        }
        let msb_bit = u32::BITS - 1 - nodes_present.leading_zeros();
        Some(Loc {
            idx: self.data_idx() + compute_slot(self.data_bitmap(), msb_bit),
            bit: msb_bit,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct Loc {
    idx: u32,
    bit: u32,
}

impl Loc {
    pub(super) fn root() -> Self {
        Self { idx: 0, bit: 0 }
    }

    pub(super) fn idx(&self) -> usize {
        self.idx as usize
    }
}

/// The `rkyv` resolver for [`ArchivedPrefixMap`] and [`ArchivedPrefixSet`].
pub struct PrefixMapResolver {
    pub(super) nodes: VecResolver,
    pub(super) nodes_len: usize,
    pub(super) data: VecResolver,
    pub(super) data_len: usize,
}
