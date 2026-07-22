//! Module containing the archived joint prefix set and map.

use crate::{
    joint::JointPrefix,
    rkyv::{ArchivedPrefixMap, ArchivedPrefixSet, PrefixMapResolver},
    Prefix,
};
use either::Either::{Left, Right};
use rkyv::{bytecheck::CheckBytes, Archive, Portable};

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

impl<P: JointPrefix, T: Archive> ArchivedJointPrefixMap<P, T> {
    /// Returns the number of elements stored in `self`.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.t1.len() + self.t2.len()
    }

    /// Returns `true` if the map contains no elements.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.t1.is_empty() && self.t2.is_empty()
    }

    /// Count the number of unique addresses covered by all prefixes in the map. If the entire trie
    /// is fully covered, the function returns `None` (as it contains `P::R::MAX + 1` addresses).
    /// Overlapping prefixes are not double-counted.
    ///
    /// To avoid double-counting, the function traverses the (partial) trie once, skipping nodes
    /// that are already covered.
    ///
    /// See [`JointPrefixMap::address_count`] for an example.
    #[inline(always)]
    #[allow(clippy::type_complexity)]
    pub fn address_count(&self) -> (Option<<P::P1 as Prefix>::R>, Option<<P::P2 as Prefix>::R>) {
        (self.t1.address_count(), self.t2.address_count())
    }

    /// Get the value of an element by matching exactly on the prefix.
    ///
    /// See [`JointPrefixMap::get`] for an example.
    pub fn get<'a>(&'a self, prefix: &P) -> Option<&'a T::Archived> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get(p),
            Right(p) => self.t2.get(p),
        }
    }

    /// Get the value of an element by matching exactly on the prefix, plus the (canonical version)
    /// of the matched prefix.
    ///
    /// **Warning**: The table does not store the prefix, but it is reconstructed. This means that
    /// any bits in the host part will be truncated.
    ///
    /// See [`JointPrefixMap::get_key_value`] for an example.
    pub fn get_key_value<'a>(&'a self, prefix: &P) -> Option<(P, &'a T::Archived)> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get_key_value(p).map(|(p, t)| (P::from_p1(&p), t)),
            Right(p) => self.t2.get_key_value(p).map(|(p, t)| (P::from_p2(&p), t)),
        }
    }

    /// Get the value of an address or prefix using longest prefix matching.
    ///
    /// See [`JointPrefixMap::get_lpm`] for an example.
    pub fn get_lpm<'a>(&'a self, prefix: &P) -> Option<(P, &'a T::Archived)> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get_lpm(p).map(|(p, t)| (P::from_p1(&p), t)),
            Right(p) => self.t2.get_lpm(p).map(|(p, t)| (P::from_p2(&p), t)),
        }
    }
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

impl<P: JointPrefix> ArchivedJointPrefixSet<P> {
    /// Returns the number of elements stored in `self`.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.t1.len() + self.t2.len()
    }

    /// Returns `true` if the map contains no elements.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.t1.is_empty() && self.t2.is_empty()
    }

    /// Count the number of unique addresses covered by all prefixes in the set. If the entire trie
    /// is fully covered, the function returns `None` (as it contains `P::R::MAX + 1` addresses).
    /// Overlapping prefixes are not double-counted.
    ///
    /// To avoid double-counting, the function traverses the (partial) trie once, skipping nodes
    /// that are already covered.
    ///
    /// See [`JointPrefixSet::address_count`] for an example.
    #[inline(always)]
    #[allow(clippy::type_complexity)]
    pub fn address_count(&self) -> (Option<<P::P1 as Prefix>::R>, Option<<P::P2 as Prefix>::R>) {
        (self.t1.address_count(), self.t2.address_count())
    }

    /// Check whether some (exact) prefix is present in the set, without using longest prefix match.
    ///
    /// See [`JointPrefixSet::contains`] for an example.
    pub fn contains(&self, prefix: &P) -> bool {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.contains(p),
            Right(p) => self.t2.contains(p),
        }
    }

    /// Get the canonical (reconstructed) prefix by exact prefix matching.
    ///
    /// Prefixes are not stored verbatim. They are reconstructed from the trie position, so host
    /// bits are not preserved.
    pub fn get(&self, prefix: &P) -> Option<P> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get(p).as_ref().map(P::from_p1),
            Right(p) => self.t2.get(p).as_ref().map(P::from_p2),
        }
    }

    /// Get the longest prefix in the set that contains `prefix`.
    ///
    /// See [`JointPrefixSet::get_lpm`] for an example.
    pub fn get_lpm(&self, prefix: &P) -> Option<P> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get_lpm(p).as_ref().map(P::from_p1),
            Right(p) => self.t2.get_lpm(p).as_ref().map(P::from_p2),
        }
    }
}

/// The `rkyv` resolver for [`ArchivedJointPrefixMap`] and [`ArchivedJointPrefixSet`].
pub struct JointPrefixMapResolver {
    pub(super) t1: PrefixMapResolver,
    pub(super) t2: PrefixMapResolver,
}
