//! # Zero-copy archives with [`rkyv`]
//!
//! With the `rkyv` feature enabled, every map and set in this crate implements [`rkyv::Archive`],
//! [`rkyv::Serialize`], and [`rkyv::Deserialize`]. You can therefore serialize a trie into a byte
//! buffer and later read it back without a separate deserialization step: the archived trie is
//! validated once and then queried directly, in place, out of the bytes.
//!
//! Each owned collection has an archived counterpart:
//!
//! | Owned                                            | Archived                   |
//! |--------------------------------------------------|----------------------------|
//! | [`PrefixMap`](crate::PrefixMap)                  | [`ArchivedPrefixMap`]      |
//! | [`PrefixSet`](crate::PrefixSet)                  | [`ArchivedPrefixSet`]      |
//! | [`JointPrefixMap`](crate::joint::JointPrefixMap) | [`ArchivedJointPrefixMap`] |
//! | [`JointPrefixSet`](crate::joint::JointPrefixSet) | [`ArchivedJointPrefixSet`] |
//!
//! ## Serializing, accessing, and deserializing
//!
//! Use `rkyv`'s own entry points:
//!
//! - [`rkyv::to_bytes`] turns an owned map or set into a byte buffer.
//! - [`rkyv::access`] borrows the archived trie from those bytes after validating them, without
//!   allocating or copying. [`rkyv::access_unchecked`] skips validation for trusted input.
//! - [`rkyv::from_bytes`] (or [`rkyv::deserialize`] on an accessed archive) rebuilds a full owned
//!   [`PrefixMap`](crate::PrefixMap), allocator and free list included, when you need a mutable
//!   trie back.
//!
//! Prefixes are never stored in the archive. Just like in the owned collections, an entry is
//! identified by its path through the trie, and the prefix is reconstructed from that position when
//! it is returned. The prefix type `P` therefore does not need to implement any `rkyv` trait (it
//! appears only as a `PhantomData` marker on the archived types). Only the value type `T` is
//! archived, through its own [`rkyv::Archive`] implementation, so a query on an archived map yields
//! `&T::Archived` rather than `&T`.
//!
//! ## Reading an archive
//!
//! The archived types mirror the immutable API of the owned collections: exact, longest-prefix,
//! and shortest-prefix lookups ([`get`](ArchivedPrefixMap::get),
//! [`get_lpm`](ArchivedPrefixMap::get_lpm), [`get_spm`](ArchivedPrefixMap::get_spm), and their
//! `_prefix`/`_key_value` variants), containment checks, [`address_count`](ArchivedPrefixMap::address_count), the
//! [`iter`](ArchivedPrefixMap::iter), [`keys`](ArchivedPrefixMap::keys), and
//! [`values`](ArchivedPrefixMap::values) family, [`iter_from`](ArchivedPrefixMap::iter_from),
//! [`children`](ArchivedPrefixMap::children), and the [`cover`](ArchivedPrefixMap::cover)
//! iterators. They deliberately do not expose any mutating methods, memory-accounting helpers,
//! or the consuming (`into_*`) iterators, none of which make sense for data borrowed out of a
//! read-only buffer.
//!
//! ## Integrating with existing code through `TrieView`
//!
//! The recommended way to plug an archive into code that already works with this crate is the
//! [`TrieView`](crate::TrieView) trait. `&ArchivedPrefixMap` and `&ArchivedPrefixSet` implement
//! [`AsView`](crate::AsView), so any function written against a [`TrieView`](crate::TrieView)
//! accepts an archive just as it accepts a borrowed [`PrefixMap`](crate::PrefixMap) or
//! [`PrefixSet`](crate::PrefixSet). This also means archives participate in the set operations
//! (`union`, `intersection`, `difference`, and the covering variants), which are themselves
//! expressed as trie views: you can combine an archived trie with an owned one and evaluate the
//! result in a single traversal, without deserializing either side.
//!
//! The joint archives do not implement [`AsView`](crate::AsView) directly. Reach for their public
//! `t1` and `t2` fields, which are ordinary [`ArchivedPrefixMap`]/[`ArchivedPrefixSet`] values, to
//! obtain per-family views.
//!
//! ## Layout and canonical form
//!
//! The archived version of a [`PrefixMap`](crate::PrefixMap) is extremely similar to the regular
//! table representation (5-level nodes, heaps of size 31), but read-only. Thus, it does not have an
//! allocator. Instead the data is saved in a contiguous array without empty spaces: each node is
//! allocated exactly by its popcount (no exponential slots), and without a free list. The data
//! layout is stored in BFS order to simplify validation and to improve cache locality for the
//! hottest nodes (close to the root).
//!
//! Because of these rules the archived representation is canonical: a given set of entries has
//! exactly one valid encoding. Two tries that store the same entries (with the same, canonically
//! encoded values) serialize to identical byte buffers, so the simplest and cheapest equality check
//! is to compare the two [`rkyv::to_bytes`] outputs directly.
//!
//! Note that this byte comparison is a property of the whole serialized buffer, not of an accessed
//! [`ArchivedPrefixMap`] on its own: the archived struct holds relative pointers into the rest of
//! the buffer, so its own bytes are not meaningful in isolation. The [`PartialEq`]/[`Eq`]
//! implementations therefore compare the node and data arrays element by element (following those
//! pointers into the archived values), which for a canonical archive gives the same answer as
//! comparing the serialized buffers.

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
/// Error while serializing an Archive or validating it.
pub enum ArchiveError {
    /// The node list does not contain all referenced nodes.
    NodeListTooShort,
    /// The node list contains unreferenced nodes.
    NodeListTooLong,
    /// The node list is not stored in BFS order.
    NodeListInconsistent,
    /// The node list is too long to be serialized or deserialized.
    NodeIndexOverflow,
    /// The data list does not contain all referenced data.
    DataListTooShort,
    /// The data list contains unreferenced data
    DataListTooLong,
    /// The data list is not stored in BFS order.
    DataListInconsistent,
    /// The data list is too long to be serialized or deserialized.
    DataIndexOverflow,
    /// The trie contains empty nodes.
    ContainsEmptyNode,
    /// The root node is missing
    MissingRootNode,
    /// The tree is deeper than the Prefix type allows.
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
