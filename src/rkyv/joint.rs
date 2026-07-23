//! Module containing the archived joint prefix set and map.

use std::fmt::Debug;

use crate::{
    joint::JointPrefix,
    rkyv::{ArchivedPrefixMap, ArchivedPrefixSet, PrefixMapResolver},
    Prefix,
};
// needed for doc references.
#[allow(unused_imports)]
use crate::joint::{JointPrefixMap, JointPrefixSet};
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

impl<P, T> Debug for ArchivedJointPrefixMap<P, T>
where
    P::P1: Debug,
    P::P2: Debug,
    P: JointPrefix + Debug,
    T: Archive,
    T::Archived: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("JointPrefixMap")
            .field("t1", &self.t1)
            .field("t2", &self.t2)
            .finish()
    }
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
    /// This mirrors [`JointPrefixMap::address_count`], but operates on the archived map.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("192.0.2.0/24"), 1);
    /// pm.insert(p!("198.51.100.0/24"), 2);
    /// pm.insert(p!("2001:db8::/96"), 3);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(map.address_count(), (Some(512), Some(0x1_0000_0000)));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    #[allow(clippy::type_complexity)]
    pub fn address_count(&self) -> (Option<<P::P1 as Prefix>::R>, Option<<P::P2 as Prefix>::R>) {
        (self.t1.address_count(), self.t2.address_count())
    }

    /// Get the value of an element by matching exactly on the prefix.
    ///
    /// This mirrors [`JointPrefixMap::get`], but operates on the archived map and yields a reference
    /// to the archived value.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.1.0/24"), 1);
    /// pm.insert(p!("2001:db8::/96"), 2);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(map.get(&p!("10.0.1.0/24")).map(|v| v.to_native()), Some(1));
    /// assert_eq!(map.get(&p!("10.0.2.0/24")), None);
    /// assert_eq!(map.get(&p!("2001:db8::/96")).map(|v| v.to_native()), Some(2));
    /// assert_eq!(map.get(&p!("2001:db8:1::/48")), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn get<'a>(&'a self, prefix: &P) -> Option<&'a T::Archived> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get(p),
            Right(p) => self.t2.get(p),
        }
    }

    /// Check if a key is present in the datastructure
    ///
    /// This mirrors [`JointPrefixMap::contains_key`], but operates on the archived map.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.1.0/24"), 1);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert!(map.contains_key(&p!("10.0.1.0/24")));
    /// assert!(!map.contains_key(&p!("10.0.2.0/24")));
    /// assert!(!map.contains_key(&p!("10.0.0.0/23")));
    /// assert!(!map.contains_key(&p!("10.0.1.128/25")));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
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
    /// This mirrors [`JointPrefixMap::get_key_value`], but operates on the archived map and yields a
    /// reference to the archived value.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let prefix = p!("10.0.1.0/24");
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(prefix, 1);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// let (key, value) = map.get_key_value(&prefix).unwrap();
    /// assert_eq!((key, value.to_native()), (prefix, 1));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn get_key_value<'a>(&'a self, prefix: &P) -> Option<(P, &'a T::Archived)> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get_key_value(p).map(|(p, t)| (P::from_p1(&p), t)),
            Right(p) => self.t2.get_key_value(p).map(|(p, t)| (P::from_p2(&p), t)),
        }
    }

    /// Get the value of an address or prefix using longest prefix matching.
    ///
    /// This mirrors [`JointPrefixMap::get_lpm`], but operates on the archived map and yields a
    /// reference to the archived value.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.1.0/24"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// let lpm = |s| map.get_lpm(&s).map(|(p, v)| (p, v.to_native()));
    /// assert_eq!(lpm(p!("10.0.1.1/32")), Some((p!("10.0.1.0/24"), 1)));
    /// assert_eq!(lpm(p!("10.0.1.0/24")), Some((p!("10.0.1.0/24"), 1)));
    /// assert_eq!(lpm(p!("10.0.0.0/24")), Some((p!("10.0.0.0/23"), 2)));
    /// assert_eq!(lpm(p!("10.0.2.0/24")), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn get_lpm<'a>(&'a self, prefix: &P) -> Option<(P, &'a T::Archived)> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get_lpm(p).map(|(p, t)| (P::from_p1(&p), t)),
            Right(p) => self.t2.get_lpm(p).map(|(p, t)| (P::from_p2(&p), t)),
        }
    }

    /// Get the longest prefix in the map that contains `prefix`.
    ///
    /// This mirrors [`JointPrefixMap::get_lpm_prefix`], but operates on the archived map.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.1.0/24"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(map.get_lpm_prefix(&p!("10.0.1.1/32")), Some(p!("10.0.1.0/24")));
    /// assert_eq!(map.get_lpm_prefix(&p!("10.0.0.0/24")), Some(p!("10.0.0.0/23")));
    /// assert_eq!(map.get_lpm_prefix(&p!("10.0.2.0/24")), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn get_lpm_prefix(&self, prefix: &P) -> Option<P> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get_lpm_prefix(p).map(|p| P::from_p1(&p)),
            Right(p) => self.t2.get_lpm_prefix(p).map(|p| P::from_p2(&p)),
        }
    }

    /// Get the value of an address or prefix using shortest prefix matching.
    ///
    /// This mirrors [`JointPrefixMap::get_spm`], but operates on the archived map and yields a
    /// reference to the archived value.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.1.0/24"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// let spm = |s| map.get_spm(&s).map(|(p, v)| (p, v.to_native()));
    /// assert_eq!(spm(p!("10.0.1.1/32")), Some((p!("10.0.0.0/23"), 2)));
    /// assert_eq!(spm(p!("10.0.1.0/24")), Some((p!("10.0.0.0/23"), 2)));
    /// assert_eq!(spm(p!("10.0.0.0/23")), Some((p!("10.0.0.0/23"), 2)));
    /// assert_eq!(spm(p!("10.0.2.0/24")), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn get_spm<'a>(&'a self, prefix: &P) -> Option<(P, &'a T::Archived)> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get_spm(p).map(|(p, t)| (P::from_p1(&p), t)),
            Right(p) => self.t2.get_spm(p).map(|(p, t)| (P::from_p2(&p), t)),
        }
    }

    /// Get the shortest prefix in the map that contains `prefix`.
    ///
    /// This mirrors [`JointPrefixMap::get_spm_prefix`], but operates on the archived map.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.1.0/24"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(map.get_spm_prefix(&p!("10.0.1.1/32")), Some(p!("10.0.0.0/23")));
    /// assert_eq!(map.get_spm_prefix(&p!("10.0.0.0/23")), Some(p!("10.0.0.0/23")));
    /// assert_eq!(map.get_spm_prefix(&p!("10.0.2.0/24")), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn get_spm_prefix(&self, prefix: &P) -> Option<P> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get_spm_prefix(p).map(|p| P::from_p1(&p)),
            Right(p) => self.t2.get_spm_prefix(p).map(|p| P::from_p2(&p)),
        }
    }

    /// An iterator visiting all key-value pairs in lexicographic order. The iterator element type
    /// is `(P, &T::Archived)`, with reconstructed prefixes `P`.
    ///
    /// This mirrors [`JointPrefixMap::iter`], but operates on the archived map and yields references
    /// to archived values. Entries of the first prefix family are yielded before the second.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/22"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    /// pm.insert(p!("10.0.2.0/23"), 3);
    /// pm.insert(p!("10.0.0.0/24"), 4);
    /// pm.insert(p!("10.0.2.0/24"), 5);
    /// pm.insert(p!("2001:db8::/96"), 6);
    /// pm.insert(p!("2001:db8::/97"), 7);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     map.iter().map(|(p, v)| (p, v.to_native())).collect::<Vec<_>>(),
    ///     vec![
    ///         (p!("10.0.0.0/22"), 1),
    ///         (p!("10.0.0.0/23"), 2),
    ///         (p!("10.0.0.0/24"), 4),
    ///         (p!("10.0.2.0/23"), 3),
    ///         (p!("10.0.2.0/24"), 5),
    ///         (p!("2001:db8::/96"), 6),
    ///         (p!("2001:db8::/97"), 7),
    ///     ],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn iter(&self) -> Iter<'_, P, T> {
        Iter {
            i1: self.t1.iter(),
            i2: self.t2.iter(),
        }
    }

    /// An iterator visiting all keys in lexicographic order. The iterator element type is
    /// reconstructed prefixes `P`.
    ///
    /// This mirrors [`JointPrefixMap::keys`], but operates on the archived map.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/22"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    /// pm.insert(p!("10.0.2.0/23"), 3);
    /// pm.insert(p!("10.0.0.0/24"), 4);
    /// pm.insert(p!("10.0.2.0/24"), 5);
    /// pm.insert(p!("2001:db8::/96"), 6);
    /// pm.insert(p!("2001:db8::/97"), 7);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     map.keys().collect::<Vec<_>>(),
    ///     vec![
    ///         p!("10.0.0.0/22"),
    ///         p!("10.0.0.0/23"),
    ///         p!("10.0.0.0/24"),
    ///         p!("10.0.2.0/23"),
    ///         p!("10.0.2.0/24"),
    ///         p!("2001:db8::/96"),
    ///         p!("2001:db8::/97"),
    ///     ],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn keys(&self) -> Keys<'_, P, T> {
        Keys {
            i1: self.t1.keys(),
            i2: self.t2.keys(),
        }
    }

    /// An iterator visiting all values in lexicographic order. The iterator element type is
    /// `&T::Archived`.
    ///
    /// This mirrors [`JointPrefixMap::values`], but operates on the archived map and yields
    /// references to archived values.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/22"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    /// pm.insert(p!("10.0.2.0/23"), 3);
    /// pm.insert(p!("10.0.0.0/24"), 4);
    /// pm.insert(p!("10.0.2.0/24"), 5);
    /// pm.insert(p!("2001:db8::/96"), 6);
    /// pm.insert(p!("2001:db8::/97"), 7);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     map.values().map(|v| v.to_native()).collect::<Vec<_>>(),
    ///     vec![1, 2, 4, 3, 5, 6, 7],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn values(&self) -> Values<'_, P, T> {
        Values {
            i1: self.t1.values(),
            i2: self.t2.values(),
        }
    }

    /// Get an iterator over the node itself and all children. All elements returned have a prefix
    /// that is contained within `prefix` itself (or are the same). The iterator yields
    /// `(P, &'a T)`, with reconstructed prefixes `P`. The iterator yields elements in
    /// lexicographic order.
    ///
    /// **Note**: Consider using [`crate::AsView::view_at`] as an alternative.
    ///
    /// This mirrors [`JointPrefixMap::children`], but operates on the archived map and yields
    /// references to archived values.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/22"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    /// pm.insert(p!("10.0.2.0/23"), 3);
    /// pm.insert(p!("10.0.0.0/24"), 4);
    /// pm.insert(p!("10.0.2.0/24"), 5);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     map.children(&p!("10.0.0.0/23"))
    ///         .map(|(p, v)| (p, v.to_native()))
    ///         .collect::<Vec<_>>(),
    ///     vec![(p!("10.0.0.0/23"), 2), (p!("10.0.0.0/24"), 4)],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn children<'a>(&'a self, prefix: &P) -> Iter<'a, P, T> {
        match prefix.p1_or_p2_ref() {
            Left(p) => Iter {
                i1: self.t1.children(p),
                i2: Default::default(),
            },
            Right(p) => Iter {
                i1: Default::default(),
                i2: self.t2.children(p),
            },
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
    /// This mirrors [`JointPrefixMap::iter_from`], but operates on the archived map and yields
    /// references to archived values.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/22"), 1);
    /// pm.insert(p!("10.0.0.0/24"), 2);
    /// pm.insert(p!("2001:db8::/96"), 3);
    /// pm.insert(p!("2001:db8::/97"), 4);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     map.iter_from(&p!("10.0.0.0/24"), false)
    ///         .map(|(p, v)| (p, v.to_native()))
    ///         .collect::<Vec<_>>(),
    ///     vec![(p!("2001:db8::/96"), 3), (p!("2001:db8::/97"), 4)],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
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
    /// This mirrors [`JointPrefixMap::cover`], but operates on the archived map and yields
    /// references to archived values.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/8"), 0);
    /// pm.insert(p!("10.1.0.0/16"), 1);
    /// pm.insert(p!("10.1.1.0/24"), 2);
    /// pm.insert(p!("10.1.2.0/24"), 3); // disjoint prefixes are not covered
    /// pm.insert(p!("10.1.1.0/25"), 4); // more specific prefixes are not covered
    /// pm.insert(p!("11.0.0.0/8"), 5);  // branch points without a value are skipped
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     map.cover(&p!("10.1.1.0/24"))
    ///         .map(|(p, v)| (p, v.to_native()))
    ///         .collect::<Vec<_>>(),
    ///     vec![(p!("10.0.0.0/8"), 0), (p!("10.1.0.0/16"), 1), (p!("10.1.1.0/24"), 2)],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
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
    /// This mirrors [`JointPrefixMap::cover_keys`], but operates on the archived map.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/8"), 0);
    /// pm.insert(p!("10.1.0.0/16"), 1);
    /// pm.insert(p!("10.1.1.0/24"), 2);
    /// pm.insert(p!("10.1.2.0/24"), 3); // disjoint prefixes are not covered
    /// pm.insert(p!("10.1.1.0/25"), 4); // more specific prefixes are not covered
    /// pm.insert(p!("11.0.0.0/8"), 5);  // branch points without a value are skipped
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     map.cover_keys(&p!("10.1.1.0/24")).collect::<Vec<_>>(),
    ///     vec![p!("10.0.0.0/8"), p!("10.1.0.0/16"), p!("10.1.1.0/24")],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
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
    /// This mirrors [`JointPrefixMap::cover_values`], but operates on the archived map and yields
    /// references to archived values.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixMap;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = JointPrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/8"), 0);
    /// pm.insert(p!("10.1.0.0/16"), 1);
    /// pm.insert(p!("10.1.1.0/24"), 2);
    /// pm.insert(p!("10.1.2.0/24"), 3); // disjoint prefixes are not covered
    /// pm.insert(p!("10.1.1.0/25"), 4); // more specific prefixes are not covered
    /// pm.insert(p!("11.0.0.0/8"), 5);  // branch points without a value are skipped
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedJointPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     map.cover_values(&p!("10.1.1.0/24"))
    ///         .map(|v| v.to_native())
    ///         .collect::<Vec<_>>(),
    ///     vec![0, 1, 2],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn cover_values<'a>(&'a self, prefix: &P) -> CoverValues<'a, P, T> {
        match prefix.p1_or_p2_ref() {
            Left(p) => CoverValues::P1(self.t1.cover_values(p)),
            Right(p) => CoverValues::P2(self.t2.cover_values(p)),
        }
    }
}

impl<'a, P: JointPrefix, T: Archive> IntoIterator for &'a ArchivedJointPrefixMap<P, T> {
    type Item = (P, &'a T::Archived);
    type IntoIter = Iter<'a, P, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<P, T> Eq for ArchivedJointPrefixMap<P, T>
where
    P: JointPrefix,
    T: Archive,
    T::Archived: PartialEq,
{
}

impl<P, T> PartialEq for ArchivedJointPrefixMap<P, T>
where
    P: JointPrefix,
    T: Archive,
    T::Archived: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.t1 == other.t1 && self.t2 == other.t2
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
    /// This mirrors [`JointPrefixSet::address_count`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixSet;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = JointPrefixSet::<P>::new();
    /// ps.insert(p!("192.0.2.0/24"));
    /// ps.insert(p!("198.51.100.0/24"));
    /// ps.insert(p!("2001:db8::/96"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedJointPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(set.address_count(), (Some(512), Some(0x1_0000_0000)));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    #[allow(clippy::type_complexity)]
    pub fn address_count(&self) -> (Option<<P::P1 as Prefix>::R>, Option<<P::P2 as Prefix>::R>) {
        (self.t1.address_count(), self.t2.address_count())
    }

    /// Check whether some (exact) prefix is present in the set, without using longest prefix match.
    ///
    /// This mirrors [`JointPrefixSet::contains`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixSet;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = JointPrefixSet::<P>::new();
    /// ps.insert(p!("10.0.1.0/24"));
    /// ps.insert(p!("2001:db8::/96"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedJointPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert!(set.contains(&p!("10.0.1.0/24")));
    /// assert!(!set.contains(&p!("10.0.2.0/24")));
    /// assert!(set.contains(&p!("2001:db8::/96")));
    /// assert!(!set.contains(&p!("2001:db8:1::/48")));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
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
    ///
    /// This mirrors [`JointPrefixSet::get`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixSet;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = JointPrefixSet::<P>::new();
    /// ps.insert(p!("10.0.1.0/24"));
    /// ps.insert(p!("2001:db8::/96"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedJointPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(set.get(&p!("10.0.1.0/24")), Some(p!("10.0.1.0/24")));
    /// assert_eq!(set.get(&p!("10.0.2.0/24")), None);
    /// assert_eq!(set.get(&p!("2001:db8::/96")), Some(p!("2001:db8::/96")));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn get(&self, prefix: &P) -> Option<P> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get(p).as_ref().map(P::from_p1),
            Right(p) => self.t2.get(p).as_ref().map(P::from_p2),
        }
    }

    /// Get the longest prefix in the set that contains `prefix`.
    ///
    /// This mirrors [`JointPrefixSet::get_lpm`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixSet;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = JointPrefixSet::<P>::new();
    /// ps.insert(p!("10.0.1.0/24"));
    /// ps.insert(p!("10.0.0.0/23"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedJointPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(set.get_lpm(&p!("10.0.1.1/32")), Some(p!("10.0.1.0/24")));
    /// assert_eq!(set.get_lpm(&p!("10.0.0.0/24")), Some(p!("10.0.0.0/23")));
    /// assert_eq!(set.get_lpm(&p!("10.0.2.0/24")), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn get_lpm(&self, prefix: &P) -> Option<P> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get_lpm(p).as_ref().map(P::from_p1),
            Right(p) => self.t2.get_lpm(p).as_ref().map(P::from_p2),
        }
    }

    /// Get the shortest prefix in the set that contains `prefix`.
    ///
    /// This mirrors [`JointPrefixSet::get_spm`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixSet;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = JointPrefixSet::<P>::new();
    /// ps.insert(p!("10.0.1.0/24"));
    /// ps.insert(p!("10.0.0.0/23"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedJointPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(set.get_spm(&p!("10.0.1.1/32")), Some(p!("10.0.0.0/23")));
    /// assert_eq!(set.get_spm(&p!("10.0.0.0/23")), Some(p!("10.0.0.0/23")));
    /// assert_eq!(set.get_spm(&p!("10.0.2.0/24")), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn get_spm(&self, prefix: &P) -> Option<P> {
        match prefix.p1_or_p2_ref() {
            Left(p) => self.t1.get_spm(p).as_ref().map(P::from_p1),
            Right(p) => self.t2.get_spm(p).as_ref().map(P::from_p2),
        }
    }

    /// An iterator visiting all keys in lexicographic order. The iterator element type is
    /// reconstructed prefixes `P`.
    ///
    /// This mirrors [`JointPrefixSet::iter`], but operates on the archived set. Prefixes of the
    /// first family are yielded before the second.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixSet;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = JointPrefixSet::<P>::new();
    /// ps.insert(p!("10.0.0.0/23"));
    /// ps.insert(p!("10.0.0.0/24"));
    /// ps.insert(p!("10.0.2.0/23"));
    /// ps.insert(p!("2001:db8::/96"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedJointPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     set.iter().collect::<Vec<_>>(),
    ///     vec![
    ///         p!("10.0.0.0/23"),
    ///         p!("10.0.0.0/24"),
    ///         p!("10.0.2.0/23"),
    ///         p!("2001:db8::/96"),
    ///     ],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn iter(&self) -> Keys<'_, P, ()> {
        Keys {
            i1: self.t1.iter(),
            i2: self.t2.iter(),
        }
    }

    /// Get an iterator over the node itself and all children. All elements returned have a prefix
    /// that is contained within `prefix` itself (or are the same). The iterator yields
    /// reconstructed prefixes `P` in lexicographic order.
    ///
    /// **Note**: Consider using [`crate::AsView::view_at`] as an alternative.
    ///
    /// This mirrors [`JointPrefixSet::children`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixSet;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = JointPrefixSet::<P>::new();
    /// ps.insert(p!("10.0.0.0/22"));
    /// ps.insert(p!("10.0.0.0/23"));
    /// ps.insert(p!("10.0.2.0/23"));
    /// ps.insert(p!("10.0.0.0/24"));
    /// ps.insert(p!("10.0.2.0/24"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedJointPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     set.children(&p!("10.0.0.0/23")).collect::<Vec<_>>(),
    ///     vec![p!("10.0.0.0/23"), p!("10.0.0.0/24")],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn children<'a>(&'a self, prefix: &P) -> Keys<'a, P, ()> {
        match prefix.p1_or_p2_ref() {
            Left(p) => Keys {
                i1: self.t1.children(p),
                i2: Default::default(),
            },
            Right(p) => Keys {
                i1: Default::default(),
                i2: self.t2.children(p),
            },
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
    /// This mirrors [`JointPrefixSet::iter_from`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixSet;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = JointPrefixSet::<P>::new();
    /// ps.insert(p!("10.0.0.0/24"));
    /// ps.insert(p!("10.0.1.0/24"));
    /// ps.insert(p!("10.0.2.0/24"));
    /// ps.insert(p!("2001:db8::/96"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedJointPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     set.iter_from(&p!("10.0.0.0/24"), false).take(2).collect::<Vec<_>>(),
    ///     vec![p!("10.0.1.0/24"), p!("10.0.2.0/24")],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
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
    /// This mirrors [`JointPrefixSet::cover`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::joint::JointPrefixSet;
    /// # use prefix_trie::rkyv::ArchivedJointPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::IpNet;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = JointPrefixSet::<P>::new();
    /// ps.insert(p!("10.0.0.0/8"));
    /// ps.insert(p!("10.1.0.0/16"));
    /// ps.insert(p!("10.1.1.0/24"));
    /// ps.insert(p!("10.1.2.0/24")); // disjoint prefixes are not covered
    /// ps.insert(p!("10.1.1.0/25")); // more specific prefixes are not covered
    /// ps.insert(p!("11.0.0.0/8"));  // unrelated branches are skipped
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedJointPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     set.cover(&p!("10.1.1.0/24")).collect::<Vec<_>>(),
    ///     vec![p!("10.0.0.0/8"), p!("10.1.0.0/16"), p!("10.1.1.0/24")],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn cover<'a>(&'a self, prefix: &P) -> CoverKeys<'a, P, ()> {
        match prefix.p1_or_p2_ref() {
            Left(p) => CoverKeys::P1(self.t1.cover(p)),
            Right(p) => CoverKeys::P2(self.t2.cover(p)),
        }
    }
}

impl<'a, P: JointPrefix> IntoIterator for &'a ArchivedJointPrefixSet<P> {
    type Item = P;
    type IntoIter = Keys<'a, P, ()>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<P: JointPrefix> Eq for ArchivedJointPrefixSet<P> {}

impl<P: JointPrefix> PartialEq for ArchivedJointPrefixSet<P> {
    fn eq(&self, other: &Self) -> bool {
        self.t1 == other.t1 && self.t2 == other.t2
    }
}

impl<P> Debug for ArchivedJointPrefixSet<P>
where
    P::P1: Debug,
    P::P2: Debug,
    P: JointPrefix + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("JointPrefixSet")
            .field("t1", &self.t1)
            .field("t2", &self.t2)
            .finish()
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
    /// The iterator corresponding to the first prefix type.
    P1(super::map::Cover<'a, P::P1, T>),
    /// The iterator corresponding to the second prefix type.
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
    /// The iterator corresponding to the first prefix type.
    P1(super::map::CoverKeys<'a, P::P1, T>),
    /// The iterator corresponding to the second prefix type.
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
    /// The iterator corresponding to the first prefix type.
    P1(super::map::CoverValues<'a, P::P1, T>),
    /// The iterator corresponding to the second prefix type.
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
