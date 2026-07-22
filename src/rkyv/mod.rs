//! # rkyv zero-copy deserialization.
//!
//! The archived version of a `PrefixMap` is extremely similar to the regular table representation
//! (5-level nodes, heaps of size 31), but read-only. Thus, they do not have an allocator. Instead
//! the data is saved in a contiguous array without empty spaces: Each node is allocated exactly by
//! its popcount (no exponential slots), and without a free list. The data layout is stored in a BFS
//! order to simplify validation and to improve cache locality for the hottest nodes (close to the
//! root).

mod deserialize;
mod serialize;
#[cfg(test)]
mod test;
mod validate;
mod view;

use core::error::Error;
use std::marker::PhantomData;

use crate::joint::JointPrefix;
use rkyv::{
    bytecheck::CheckBytes,
    traits::NoUndef,
    vec::{ArchivedVec, VecResolver},
    Archive, Portable, Serialize,
};

#[repr(transparent)]
#[derive(Portable, CheckBytes)]
#[bytecheck(crate = rkyv::bytecheck)]
struct MyPhantomData<T>(PhantomData<T>);

// Safety: PhantomData is zero-sized, so it cannot have an undefined value by definition.
unsafe impl<T> NoUndef for MyPhantomData<T> {}

/// Rkyv representation of a node with compacted indices
#[derive(Archive, Serialize, Default)]
#[rkyv(derive(Debug))]
pub(crate) struct NodeRepr {
    pub(super) data_bitmap: u32,
    pub(super) child_bitmap: u32,
    pub(super) data_idx: u32,
    pub(super) children_idx: u32,
}

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
    nodes: ArchivedVec<ArchivedNodeRepr>,
    data: ArchivedVec<T::Archived>,
    _marker: MyPhantomData<P>,
}

/// Archived (immutable) version of a [`PrefixSet`].
///
/// Any (verified) archived prefix map is canonical and has the following properties:
/// - The tree is stored as BFS (ordered per level).
/// - The root node is always present.
/// - No node (except the root) may be emtpy.
///
/// Due to these properties, you can compare two `ArchivedPrefixSet`s for equality by comparing
/// their byte string.
#[repr(transparent)]
#[derive(Portable, CheckBytes)]
#[bytecheck(crate = rkyv::bytecheck)]
pub struct ArchivedPrefixSet<P>(ArchivedPrefixMap<P, ()>);

/// Archived (immutable) version of a [`JointPrefixMap`].
///
/// Any (verified) archived prefix map is canonical and has the following properties:
/// - The two tree are stored as BFS (ordered per level).
/// - The root nodes are always present.
/// - Data is stored contiguously without empty (uninitialized) memory in between.
/// - No node (except the two roots) may be emtpy.
///
/// Due to these properties, you can compare two `ArchivedJointPrefixSet`s for equality by
/// comparing their byte string.
#[repr(C)]
#[derive(Portable, CheckBytes)]
#[bytecheck(crate = rkyv::bytecheck)]
pub struct ArchivedJointPrefixMap<P: JointPrefix, T: Archive> {
    /// PrefixMap that corresponds to the first prefix type
    pub t1: ArchivedPrefixMap<P::P1, T>,
    /// PrefixMap that corresponds to the second prefix type
    pub t2: ArchivedPrefixMap<P::P2, T>,
}

/// Archived (immutable) version of a [`JointPrefixSet`].
///
/// Any (verified) archived prefix set is canonical and has the following properties:
/// - The two tree are stored as BFS (ordered per level).
/// - The root nodes are always present.
/// - No node (except the two roots) may be emtpy.
///
/// Due to these properties, you can compare two `ArchivedJointPrefixSet`s for equality by
/// comparing their byte string.
#[repr(C)]
#[derive(Portable, CheckBytes)]
#[bytecheck(crate = rkyv::bytecheck)]
pub struct ArchivedJointPrefixSet<P: JointPrefix> {
    /// PrefixSet that corresponds to the first prefix type
    pub t1: ArchivedPrefixSet<P::P1>,
    /// PrefixSet that corresponds to the second prefix type
    pub t2: ArchivedPrefixSet<P::P2>,
}

/// The `rkyv` resolver for [`ArchivedPrefixMap`] and [`ArchivedPrefixSet`].
pub struct PrefixMapResolver {
    nodes: VecResolver,
    nodes_len: usize,
    data: VecResolver,
    data_len: usize,
}

/// The `rkyv` resolver for [`ArchivedJointPrefixMap`] and [`ArchivedJointPrefixSet`].
pub struct JointPrefixMapResolver {
    t1: PrefixMapResolver,
    t2: PrefixMapResolver,
}

#[derive(Debug)]
pub enum ArchiveError {
    NodeListTooShort,
    NodeListTooLong,
    NodeListInconsistent,
    NodeIndexOverflow,
    DataListTooShort,
    DataListTooLong,
    DataListInconsistent,
    DataIndexOverflow,
    ContainsEmptyNode,
    MissingRootNode,
    DepthExceedsPrefixRepr,
}

impl Error for ArchiveError {}
impl std::fmt::Display for ArchiveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::NodeListTooShort => "Node list is too short",
            Self::NodeListTooLong => "Node list is too long",
            Self::NodeListInconsistent => "Inconsistent node list",
            Self::NodeIndexOverflow => "Node list too long for 32-bit index.",
            Self::DataListTooShort => "Data list is too short",
            Self::DataListTooLong => "Data list is too long",
            Self::DataListInconsistent => "Inconsistent data list",
            Self::DataIndexOverflow => "Data list too long for 32-bit index.",
            Self::ContainsEmptyNode => "Trie contains empty nodes.",
            Self::MissingRootNode => "Missing the root node.",
            Self::DepthExceedsPrefixRepr => {
                "Depth of tree exceeds the number of bits in the prefix."
            }
        };
        f.write_str(s)
    }
}
