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

    /// Check if a key is present in the datastructure
    ///
    /// See [`JointPrefixMap::contains_key`] for an example.
    pub fn contains_key(&self, prefix: &P) -> bool {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.contains_key(p),
            Right(p) => self.t2.contains_key(p),
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

    /// Get the longest prefix in the map that contains `prefix`.
    ///
    /// See [`JointPrefixMap::get_lpm_prefix`] for an example.
    pub fn get_lpm_prefix(&self, prefix: &P) -> Option<P> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get_lpm_prefix(p).map(|p| P::from_p1(&p)),
            Right(p) => self.t2.get_lpm_prefix(p).map(|p| P::from_p2(&p)),
        }
    }

    /// Get the value of an address or prefix using shortest prefix matching.
    ///
    /// See [`JointPrefixMap::get_spm`] for an example.
    pub fn get_spm<'a>(&'a self, prefix: &P) -> Option<(P, &'a T::Archived)> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get_spm(p).map(|(p, t)| (P::from_p1(&p), t)),
            Right(p) => self.t2.get_spm(p).map(|(p, t)| (P::from_p2(&p), t)),
        }
    }

    /// Get the shortest prefix in the map that contains `prefix`.
    ///
    /// See [`JointPrefixMap::get_spm_prefix`] for an example.
    pub fn get_spm_prefix(&self, prefix: &P) -> Option<P> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get_spm_prefix(p).map(|p| P::from_p1(&p)),
            Right(p) => self.t2.get_spm_prefix(p).map(|p| P::from_p2(&p)),
        }
    }

    /// An iterator visiting all key-value pairs in lexicographic order. The iterator element type
    /// is `(P, &T::Archived)`, with reconstructed prefixes `P`.
    ///
    /// See [`JointPrefixMap::iter`] for an example.
    pub fn iter(&self) -> Iter<'_, P, T> {
        Iter {
            i1: self.t1.iter(),
            i2: self.t2.iter(),
        }
    }

    /// An iterator visiting all keys in lexicographic order. The iterator element type is
    /// reconstructed prefixes `P`.
    ///
    /// See [`JointPrefixMap::keys`] for an example.
    pub fn keys(&self) -> Keys<'_, P, T> {
        Keys {
            i1: self.t1.keys(),
            i2: self.t2.keys(),
        }
    }

    /// An iterator visiting all values in lexicographic order. The iterator element type is
    /// `&T::Archived`.
    ///
    /// See [`JointPrefixMap::values`] for an example.
    pub fn values(&self) -> Values<'_, P, T> {
        Values {
            i1: self.t1.values(),
            i2: self.t2.values(),
        }
    }

    /// Return an iterator starting at the given prefix in lexicographic order. This function can be
    /// used to implement paginated access without remembering state (of the iterator position).
    ///
    /// If `inclusive` is `true`, the iterator includes `prefix` (if present).
    /// If `inclusive` is `false`, the iterator starts after `prefix`.
    ///
    /// If `prefix` is not present in the map, the iterator starts at the first prefix that
    /// would come after it in lexicographic order, regardless of `inclusive`.
    ///
    /// See [`JointPrefixMap::iter_from`] for an example.
    pub fn iter_from<'a>(&'a self, prefix: &P, inclusive: bool) -> Iter<'a, P, T> {
        match prefix.p1_or_p2_ref() {
            Left(p) => Iter {
                i1: self.t1.iter_from(p, inclusive),
                i2: self.t2.iter(),
            },
            Right(p) => Iter {
                i1: Default::default(),
                i2: self.t2.iter_from(p, inclusive),
            },
        }
    }

    /// Iterate over all entries in the map that cover the given `prefix` (including `prefix` itself
    /// if that is present in the map). The returned iterator yields `(P, &'a T::Archived)`, with
    /// reconstructed prefixes `P`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// See [`JointPrefixMap::cover`] for an example.
    pub fn cover<'a>(&'a self, prefix: &P) -> Cover<'a, P, T> {
        match prefix.p1_or_p2_ref() {
            Left(p) => Cover::P1(self.t1.cover(p)),
            Right(p) => Cover::P2(self.t2.cover(p)),
        }
    }

    /// Iterate over all prefixes in the map that cover the given `prefix` (including `prefix` itself
    /// if that is present in the map). The returned iterator yields reconstructed prefixes `P`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// See [`JointPrefixMap::cover_keys`] for an example.
    pub fn cover_keys<'a>(&'a self, prefix: &P) -> CoverKeys<'a, P, T> {
        match prefix.p1_or_p2_ref() {
            Left(p) => CoverKeys::P1(self.t1.cover_keys(p)),
            Right(p) => CoverKeys::P2(self.t2.cover_keys(p)),
        }
    }

    /// Iterate over all values of prefixes in the map that cover the given `prefix` (including
    /// `prefix` itself if that is present in the map). The returned iterator yields
    /// `&'a T::Archived`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// See [`JointPrefixMap::cover_values`] for an example.
    pub fn cover_values<'a>(&'a self, prefix: &P) -> CoverValues<'a, P, T> {
        match prefix.p1_or_p2_ref() {
            Left(p) => CoverValues::P1(self.t1.cover_values(p)),
            Right(p) => CoverValues::P2(self.t2.cover_values(p)),
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

    /// Get the shortest prefix in the set that contains `prefix`.
    ///
    /// See [`JointPrefixSet::get_spm`] for an example.
    pub fn get_spm(&self, prefix: &P) -> Option<P> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get_spm(p).as_ref().map(P::from_p1),
            Right(p) => self.t2.get_spm(p).as_ref().map(P::from_p2),
        }
    }

    /// An iterator visiting all keys in lexicographic order. The iterator element type is
    /// reconstructed prefixes `P`.
    ///
    /// See [`JointPrefixSet::iter`] for an example.
    pub fn iter(&self) -> Keys<'_, P, ()> {
        Keys {
            i1: self.t1.iter(),
            i2: self.t2.iter(),
        }
    }

    /// Return an iterator starting at the given prefix in lexicographic order. This function can be
    /// used to implement paginated access without remembering state (of the iterator position).
    ///
    /// If `inclusive` is `true`, the iterator includes `prefix` (if present).
    /// If `inclusive` is `false`, the iterator starts after `prefix`.
    ///
    /// If `prefix` is not present in the set, the iterator starts at the first prefix that
    /// would come after it in lexicographic order, regardless of `inclusive`.
    ///
    /// See [`JointPrefixSet::iter_from`] for an example.
    pub fn iter_from(&self, prefix: &P, inclusive: bool) -> Keys<'_, P, ()> {
        match prefix.p1_or_p2_ref() {
            Left(p) => Keys {
                i1: self.t1.iter_from(p, inclusive),
                i2: self.t2.iter(),
            },
            Right(p) => Keys {
                i1: Default::default(),
                i2: self.t2.iter_from(p, inclusive),
            },
        }
    }

    /// Iterate over all prefixes in the set that cover the given `prefix` (including `prefix` itself
    /// if that is present in the map). The returned iterator yields reconstructed prefixes `P`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// See [`JointPrefixSet::cover`] for an example.
    pub fn cover<'a>(&'a self, prefix: &P) -> CoverKeys<'a, P, ()> {
        match prefix.p1_or_p2_ref() {
            Left(p) => CoverKeys::P1(self.t1.cover(p)),
            Right(p) => CoverKeys::P2(self.t2.cover(p)),
        }
    }
}

/// An iterator over all entries of a [`JointPrefixMap`] in lexicographic order.
pub struct Iter<'a, P: JointPrefix, T: Archive> {
    i1: super::map::Iter<'a, P::P1, T>,
    i2: super::map::Iter<'a, P::P2, T>,
}

impl<'a, P: JointPrefix, T: Archive> Default for Iter<'a, P, T> {
    fn default() -> Self {
        Self {
            i1: Default::default(),
            i2: Default::default(),
        }
    }
}

impl<'a, P: JointPrefix, T: Archive> Iterator for Iter<'a, P, T> {
    type Item = (P, &'a T::Archived);

    fn next(&mut self) -> Option<Self::Item> {
        self.i1
            .next()
            .map(|(p, t)| (P::from_p1(&p), t))
            .or_else(|| self.i2.next().map(|(p, t)| (P::from_p2(&p), t)))
    }
}

/// An iterator over all prefixes of a [`JointPrefixMap`] in lexicographic order.
pub struct Keys<'a, P: JointPrefix, T: Archive> {
    i1: super::map::Keys<'a, P::P1, T>,
    i2: super::map::Keys<'a, P::P2, T>,
}

impl<'a, P: JointPrefix, T: Archive> Default for Keys<'a, P, T> {
    fn default() -> Self {
        Self {
            i1: Default::default(),
            i2: Default::default(),
        }
    }
}

impl<'a, P: JointPrefix, T: Archive> Iterator for Keys<'a, P, T> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.i1
            .next()
            .map(|p| P::from_p1(&p))
            .or_else(|| self.i2.next().map(|p| P::from_p2(&p)))
    }
}

/// An iterator over all values of a [`JointPrefixMap`] in lexicographic order.
pub struct Values<'a, P: JointPrefix, T: Archive> {
    i1: super::map::Values<'a, P::P1, T>,
    i2: super::map::Values<'a, P::P2, T>,
}

impl<'a, P: JointPrefix, T: Archive> Default for Values<'a, P, T> {
    fn default() -> Self {
        Self {
            i1: Default::default(),
            i2: Default::default(),
        }
    }
}

impl<'a, P: JointPrefix, T: Archive> Iterator for Values<'a, P, T> {
    type Item = &'a T::Archived;

    fn next(&mut self) -> Option<Self::Item> {
        self.i1.next().or_else(|| self.i2.next())
    }
}

/// An iterator that yields all items of a `JointPrefixMap` thhat cover a given prefix (including
/// the prefix itself if present). See `JointPrefixMap::cover` for an example.
pub enum Cover<'a, P: JointPrefix, T: Archive> {
    P1(super::map::Cover<'a, P::P1, T>),
    P2(super::map::Cover<'a, P::P2, T>),
}

impl<'a, P: JointPrefix, T: Archive> Iterator for Cover<'a, P, T> {
    type Item = (P, &'a T::Archived);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::P1(c) => c.next().map(|(p, t)| (P::from_p1(&p), t)),
            Self::P2(c) => c.next().map(|(p, t)| (P::from_p2(&p), t)),
        }
    }
}

/// An iterator that yields all prefixes of a `JointPrefixMap` thhat cover a given prefix (including
/// the prefix itself if present). See `JointPrefixMap::cover_keys` for an example.
pub enum CoverKeys<'a, P: JointPrefix, T: Archive> {
    P1(super::map::CoverKeys<'a, P::P1, T>),
    P2(super::map::CoverKeys<'a, P::P2, T>),
}

impl<'a, P: JointPrefix, T: Archive> Iterator for CoverKeys<'a, P, T> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::P1(c) => c.next().map(|p| P::from_p1(&p)),
            Self::P2(c) => c.next().map(|p| P::from_p2(&p)),
        }
    }
}

/// An iterator that yields all values of prefixes in a `JointPrefixMap` thhat cover a given prefix
/// (including the prefix itself if present). See `JointPrefixMap::cover_values` for an example.
pub enum CoverValues<'a, P: JointPrefix, T: Archive> {
    P1(super::map::CoverValues<'a, P::P1, T>),
    P2(super::map::CoverValues<'a, P::P2, T>),
}

impl<'a, P: JointPrefix, T: Archive> Iterator for CoverValues<'a, P, T> {
    type Item = &'a T::Archived;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::P1(c) => c.next(),
            Self::P2(c) => c.next(),
        }
    }
}

/// The `rkyv` resolver for [`ArchivedJointPrefixMap`] and [`ArchivedJointPrefixSet`].
pub struct JointPrefixMapResolver {
    pub(super) t1: PrefixMapResolver,
    pub(super) t2: PrefixMapResolver,
}
