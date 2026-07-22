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
    node::DATA_BIT_TO_PREFIX,
    table::{K, NUM_CHILDREN, NUM_DATA},
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
}

/// Rkyv representation of a node with compacted indices
#[derive(Archive, Serialize, Default)]
#[rkyv(derive(Debug))]
pub(crate) struct NodeRepr {
    pub(super) data_bitmap: u32,
    pub(super) child_bitmap: u32,
    pub(super) data_idx: u32,
    pub(super) children_idx: u32,
}

impl ArchivedNodeRepr {
    #[inline(always)]
    pub(crate) fn data_bitmap(&self) -> u32 {
        self.data_bitmap.to_native()
    }

    #[inline(always)]
    pub(crate) fn has_data_bit(&self, bit: u32) -> bool {
        self.data_bitmap() & (1 << bit) != 0
    }

    /// Get an iterator over all indices of data.
    #[inline(always)]
    pub(crate) fn data_locs(&self) -> impl DoubleEndedIterator<Item = Loc> + 'static {
        let bitmap = self.data_bitmap();
        let offset = self.data_idx.to_native();
        (0..(NUM_CHILDREN as u32))
            .filter(move |&bit| bitmap & (1 << bit) != 0)
            .map(move |bit| Loc {
                idx: offset + compute_slot(bitmap, bit),
                bit,
            })
    }

    #[inline(always)]
    pub(crate) fn child_bitmap(&self) -> u32 {
        self.child_bitmap.to_native()
    }

    #[inline(always)]
    pub(crate) fn has_child_bit(&self, bit: u32) -> bool {
        self.child_bitmap() & (1 << bit) != 0
    }

    /// Get an iterator over all children.
    #[inline(always)]
    pub(crate) fn child_locs(&self) -> impl DoubleEndedIterator<Item = Loc> + 'static {
        let bitmap = self.child_bitmap();
        let offset = self.children_idx.to_native();
        (0..(NUM_CHILDREN as u32))
            .filter(move |&bit| bitmap & (1 << bit) != 0)
            .map(move |bit| Loc {
                idx: offset + compute_slot(bitmap, bit),
                bit,
            })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Loc {
    pub(crate) idx: u32,
    pub(crate) bit: u32,
}

/// The `rkyv` resolver for [`ArchivedPrefixMap`] and [`ArchivedPrefixSet`].
pub struct PrefixMapResolver {
    pub(crate) nodes: VecResolver,
    pub(crate) nodes_len: usize,
    pub(crate) data: VecResolver,
    pub(crate) data_len: usize,
}
