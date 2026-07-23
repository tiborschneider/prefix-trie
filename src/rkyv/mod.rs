//! # rkyv zero-copy deserialization.
//!
//! The archived version of a `PrefixMap` is extremely similar to the regular table representation
//! (5-level nodes, heaps of size 31), but read-only. Thus, they do not have an allocator. Instead
//! the data is saved in a contiguous array without empty spaces: Each node is allocated exactly by
//! its popcount (no exponential slots), and without a free list. The data layout is stored in a BFS
//! order to simplify validation and to improve cache locality for the hottest nodes (close to the
//! root).

mod deserialize;
pub mod joint;
pub mod map;
mod serialize;
pub mod set;
#[cfg(test)]
mod test;
mod validate;
mod view;

use core::error::Error;

pub use joint::{ArchivedJointPrefixMap, ArchivedJointPrefixSet, JointPrefixMapResolver};
pub use map::{ArchivedPrefixMap, PrefixMapResolver};
pub use set::ArchivedPrefixSet;

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
