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
    node::{
        child_bit, child_cover_mask, data_bit, data_cover_mask, data_lpm_mask, extend_repr,
        lex_after_child, lex_after_data, Key, LexElem, DATA_BIT_TO_PREFIX, LEX_ORDER,
    },
    table::{reconstruct_prefix, K, NUM_CHILDREN, NUM_DATA},
    Prefix,
};
// needed for doc references.
#[allow(unused_imports)]
use crate::{PrefixMap, PrefixSet};

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
    /// This mirrors [`PrefixMap::address_count`], but operates on the archived map.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("192.0.2.0/24"), 1);
    /// pm.insert(p!("192.0.2.128/25"), 2);
    /// pm.insert(p!("198.51.100.0/24"), 3);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(map.address_count(), Some(512));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
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
    /// This mirrors [`PrefixMap::get`], but operates on the archived map and yields a reference to
    /// the archived value.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.1.0/24"), 1);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(map.get(&p!("10.0.1.0/24")).map(|v| v.to_native()), Some(1));
    /// assert_eq!(map.get(&p!("10.0.2.0/24")), None);
    /// assert_eq!(map.get(&p!("10.0.0.0/23")), None);
    /// assert_eq!(map.get(&p!("10.0.1.128/25")), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn get<'a>(&'a self, prefix: &P) -> Option<&'a T::Archived> {
        let (key, prefix_len) = key_prefix_len(prefix);
        let (loc, _) = self.find_loc(key, prefix_len)?;
        let bit = data_bit(key, prefix_len);
        let data_loc = self.nodes[loc.idx()].data_loc(bit)?;
        Some(&self.data[data_loc.idx()])
    }

    /// Check if a key is present in the datastructure
    ///
    /// This mirrors [`PrefixMap::contains_key`], but operates on the archived map.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.1.0/24"), 1);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
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
        let (key, prefix_len) = key_prefix_len(prefix);
        let Some((loc, _)) = self.find_loc(key, prefix_len) else {
            return false;
        };
        let bit = data_bit(key, prefix_len);
        self.nodes[loc.idx()].data_loc(bit).is_some()
    }

    /// Get the value of an element by matching exactly on the prefix, plus the (canonical version)
    /// of the matched prefix.
    ///
    /// **Warning**: The table does not store the prefix, but it is reconstructed. This means that
    /// any bits in the host part will be truncated.
    ///
    /// This mirrors [`PrefixMap::get_key_value`], but operates on the archived map and yields a
    /// reference to the archived value.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let prefix = p!("10.0.1.0/24");
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(prefix, 1);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// let (key, value) = map.get_key_value(&prefix).unwrap();
    /// assert_eq!((key, value.to_native()), (prefix, 1));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn get_key_value<'a>(&'a self, prefix: &P) -> Option<(P, &'a T::Archived)> {
        let (key, prefix_len) = key_prefix_len(prefix);
        let (loc, depth) = self.find_loc(key, prefix_len)?;
        let bit = data_bit(key, prefix_len);
        let data_loc = self.nodes[loc.idx()].data_loc(bit)?;
        let prefix = reconstruct_prefix(key, depth, data_loc.bit as usize);
        Some((prefix, &self.data[data_loc.idx()]))
    }

    /// Get the value of an address or prefix using longest prefix matching.
    ///
    /// This mirrors [`PrefixMap::get_lpm`], but operates on the archived map and yields a reference
    /// to the archived value.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.1.0/24"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
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
        let (key, prefix_len) = key_prefix_len(prefix);
        let (data_loc, depth) = self.find_lpm(key, prefix_len)?;
        let prefix = reconstruct_prefix(key, depth, data_loc.bit as usize);
        Some((prefix, &self.data[data_loc.idx()]))
    }

    /// Get the longest prefix in the map that contains `prefix`.
    ///
    /// This mirrors [`PrefixMap::get_lpm_prefix`], but operates on the archived map.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.1.0/24"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
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
        let (key, prefix_len) = key_prefix_len(prefix);
        let (data_loc, depth) = self.find_lpm(key, prefix_len)?;
        let prefix = reconstruct_prefix(key, depth, data_loc.bit as usize);
        Some(prefix)
    }

    /// Get the value of an address or prefix using shortest prefix matching.
    ///
    /// This mirrors [`PrefixMap::get_spm`], but operates on the archived map and yields a reference
    /// to the archived value.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.1.0/24"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
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
        let (key, prefix_len) = key_prefix_len(prefix);
        let (data_loc, depth) = self.find_spm(key, prefix_len)?;
        let prefix = reconstruct_prefix(key, depth, data_loc.bit as usize);
        Some((prefix, &self.data[data_loc.idx()]))
    }

    /// Get the shortest prefix in the map that contains `prefix`.
    ///
    /// This mirrors [`PrefixMap::get_spm_prefix`], but operates on the archived map.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.1.0/24"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
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
        let (key, prefix_len) = key_prefix_len(prefix);
        let (data_loc, depth) = self.find_spm(key, prefix_len)?;
        let prefix = reconstruct_prefix(key, depth, data_loc.bit as usize);
        Some(prefix)
    }

    /// An iterator visiting all key-value pairs in lexicographic order. The iterator element type
    /// is `(P, &T::Archived)`, with reconstructed prefixes `P`.
    ///
    /// This mirrors [`PrefixMap::iter`], but operates on the archived map and yields references to
    /// archived values.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/22"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    /// pm.insert(p!("10.0.2.0/23"), 3);
    /// pm.insert(p!("10.0.0.0/24"), 4);
    /// pm.insert(p!("10.0.2.0/24"), 5);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     map.iter().map(|(p, v)| (p, v.to_native())).collect::<Vec<_>>(),
    ///     vec![
    ///         (p!("10.0.0.0/22"), 1),
    ///         (p!("10.0.0.0/23"), 2),
    ///         (p!("10.0.0.0/24"), 4),
    ///         (p!("10.0.2.0/23"), 3),
    ///         (p!("10.0.2.0/24"), 5),
    ///     ],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn iter(&self) -> Iter<'_, P, T> {
        Iter::new(self)
    }

    /// An iterator visiting all keys in lexicographic order. The iterator element type is
    /// reconstructed prefixes `P`.
    ///
    /// This mirrors [`PrefixMap::keys`], but operates on the archived map.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/22"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    /// pm.insert(p!("10.0.2.0/23"), 3);
    /// pm.insert(p!("10.0.0.0/24"), 4);
    /// pm.insert(p!("10.0.2.0/24"), 5);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     map.keys().collect::<Vec<_>>(),
    ///     vec![
    ///         p!("10.0.0.0/22"),
    ///         p!("10.0.0.0/23"),
    ///         p!("10.0.0.0/24"),
    ///         p!("10.0.2.0/23"),
    ///         p!("10.0.2.0/24"),
    ///     ],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn keys(&self) -> Keys<'_, P, T> {
        Keys(Iter::new(self))
    }

    /// An iterator visiting all values in lexicographic order. The iterator element type is
    /// `&T::Archived`.
    ///
    /// This mirrors [`PrefixMap::values`], but operates on the archived map and yields references to
    /// archived values.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/22"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    /// pm.insert(p!("10.0.2.0/23"), 3);
    /// pm.insert(p!("10.0.0.0/24"), 4);
    /// pm.insert(p!("10.0.2.0/24"), 5);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     map.values().map(|v| v.to_native()).collect::<Vec<_>>(),
    ///     vec![1, 2, 4, 3, 5],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn values(&self) -> Values<'_, P, T> {
        Values(Iter::new(self))
    }

    /// Get an iterator over the node itself and all children. All elements returned have a prefix
    /// that is contained within `prefix` itself (or are the same). The iterator yields
    /// `(P, &'a T)`, with reconstructed prefixes `P`. The iterator yields elements in
    /// lexicographic order.
    ///
    /// **Note**: Consider using [`crate::AsView::view_at`] as an alternative.
    ///
    /// This mirrors [`PrefixMap::children`], but operates on the archived map and yields references
    /// to archived values.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/22"), 1);
    /// pm.insert(p!("10.0.0.0/23"), 2);
    /// pm.insert(p!("10.0.2.0/23"), 3);
    /// pm.insert(p!("10.0.0.0/24"), 4);
    /// pm.insert(p!("10.0.2.0/24"), 5);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
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
        let (key, prefix_len) = key_prefix_len(prefix);
        let Some(lex) = self.build_children_lex_iter(key, prefix_len) else {
            return Default::default();
        };
        Iter::at_node(self, lex)
    }

    /// Return an iterator starting at the given prefix in lexicographic order. This function can be
    /// used to implement paginated access without remembering state (of the iterator position).
    ///
    /// - If `inclusive` is `true`, the iterator includes the entry at `prefix` (if present).
    /// - If `inclusive` is `false`, the iterator starts after `prefix`. Prefixes that are contained
    ///   within (are children of) `prefix` are still yielded.
    ///
    /// If `prefix` is not present in the map, the iterator starts at the first entry that
    /// would come after `prefix` in lexicographic order, regardless of `inclusive`.
    ///
    /// This mirrors [`PrefixMap::iter_from`], but operates on the archived map and yields references
    /// to archived values.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/8"), 1);
    /// pm.insert(p!("10.1.0.0/16"), 2);
    /// pm.insert(p!("10.2.0.0/16"), 3);
    /// pm.insert(p!("10.2.0.0/24"), 4);
    /// pm.insert(p!("10.3.0.0/16"), 5);
    /// pm.insert(p!("10.4.0.0/16"), 6);
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     map.iter_from(&p!("10.2.0.0/16"), true)
    ///         .take(3)
    ///         .map(|(p, v)| (p, v.to_native()))
    ///         .collect::<Vec<_>>(),
    ///     vec![
    ///         (p!("10.2.0.0/16"), 3),
    ///         (p!("10.2.0.0/24"), 4),
    ///         (p!("10.3.0.0/16"), 5),
    ///     ],
    /// );
    ///
    /// assert_eq!(
    ///     map.iter_from(&p!("10.2.0.0/16"), false)
    ///         .take(3)
    ///         .map(|(p, v)| (p, v.to_native()))
    ///         .collect::<Vec<_>>(),
    ///     vec![
    ///         (p!("10.2.0.0/24"), 4),
    ///         (p!("10.3.0.0/16"), 5),
    ///         (p!("10.4.0.0/16"), 6),
    ///     ],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn iter_from<'a>(&'a self, prefix: &P, inclusive: bool) -> Iter<'a, P, T> {
        let (key, prefix_len) = key_prefix_len(prefix);
        let stack = self.build_iter_stack_at(key, prefix_len, inclusive);
        Iter::from_stack(self, stack)
    }

    /// Iterate over all entries in the map that cover the given `prefix` (including `prefix` itself
    /// if that is present in the map). The returned iterator yields `(P, &'a T::Archived)`, with
    /// reconstructed prefixes `P`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// This mirrors [`PrefixMap::cover`], but operates on the archived map and yields references to
    /// archived values.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/8"), 0);
    /// pm.insert(p!("10.1.0.0/16"), 1);
    /// pm.insert(p!("10.1.1.0/24"), 2);
    /// pm.insert(p!("10.1.2.0/24"), 3); // disjoint prefixes are not covered
    /// pm.insert(p!("10.1.1.0/25"), 4); // more specific prefixes are not covered
    /// pm.insert(p!("11.0.0.0/8"), 5);  // branch points without a value are skipped
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
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
        Cover::new(self, prefix)
    }

    /// Iterate over all prefixes in the map that cover the given `prefix` (including `prefix` itself
    /// if that is present in the map). The returned iterator yields reconstructed prefixes `P`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// This mirrors [`PrefixMap::cover_keys`], but operates on the archived map.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/8"), 0);
    /// pm.insert(p!("10.1.0.0/16"), 1);
    /// pm.insert(p!("10.1.1.0/24"), 2);
    /// pm.insert(p!("10.1.2.0/24"), 3); // disjoint prefixes are not covered
    /// pm.insert(p!("10.1.1.0/25"), 4); // more specific prefixes are not covered
    /// pm.insert(p!("11.0.0.0/8"), 5);  // branch points without a value are skipped
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
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
        CoverKeys(Cover::new(self, prefix))
    }

    /// Iterate over all values of prefixes in the map that cover the given `prefix` (including
    /// `prefix` itself if that is present in the map). The returned iterator yields
    /// `&'a T::Archived`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// This mirrors [`PrefixMap::cover_values`], but operates on the archived map and yields
    /// references to archived values.
    ///
    /// ```
    /// # use prefix_trie::PrefixMap;
    /// # use prefix_trie::rkyv::ArchivedPrefixMap;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut pm = PrefixMap::<P, i32>::new();
    /// pm.insert(p!("10.0.0.0/8"), 0);
    /// pm.insert(p!("10.1.0.0/16"), 1);
    /// pm.insert(p!("10.1.1.0/24"), 2);
    /// pm.insert(p!("10.1.2.0/24"), 3); // disjoint prefixes are not covered
    /// pm.insert(p!("10.1.1.0/25"), 4); // more specific prefixes are not covered
    /// pm.insert(p!("11.0.0.0/8"), 5);  // branch points without a value are skipped
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&pm)?;
    /// let map: &ArchivedPrefixMap<P, i32> = rkyv::access::<_, Error>(&bytes)?;
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
        CoverValues(Cover::new(self, prefix))
    }
}

/// An iterator over all entries of an [`ArchivedPrefixMap`] in lexicographic order.
pub struct Iter<'a, P: Prefix, T: Archive> {
    map: Option<&'a ArchivedPrefixMap<P, T>>,
    stack: Vec<MaskedLexIter<'a, P::R>>,
}

impl<'a, P: Prefix, T: Archive> Default for Iter<'a, P, T> {
    fn default() -> Self {
        Self {
            map: None,
            stack: Vec::new(),
        }
    }
}

impl<'a, P: Prefix, T: Archive> Iter<'a, P, T> {
    pub(super) fn new(map: &'a ArchivedPrefixMap<P, T>) -> Self {
        Self::at_node(map, MaskedLexIter::root(map))
    }

    pub(super) fn at_node(map: &'a ArchivedPrefixMap<P, T>, lex: MaskedLexIter<'a, P::R>) -> Self {
        let stack = vec![lex];
        Self {
            map: Some(map),
            stack,
        }
    }

    pub(super) fn from_stack(
        map: &'a ArchivedPrefixMap<P, T>,
        stack: Vec<MaskedLexIter<'a, P::R>>,
    ) -> Self {
        Self {
            map: Some(map),
            stack,
        }
    }
}

impl<'a, P: Prefix, T: Archive> Iterator for Iter<'a, P, T> {
    type Item = (P, &'a T::Archived);

    fn next(&mut self) -> Option<Self::Item> {
        let map = self.map?;
        while let Some(lex_iter) = self.stack.last_mut() {
            let Some(next) = lex_iter.next() else {
                self.stack.pop();
                continue;
            };

            match next {
                LexIterElem::Data(loc, depth) => {
                    let p = reconstruct_prefix(lex_iter.key, depth, loc.bit as usize);
                    return Some((p, &map.data[loc.idx()]));
                }
                LexIterElem::Child(next_loc, depth, next_key) => self
                    .stack
                    .push(MaskedLexIter::new(next_loc, depth, next_key, map)),
            }
        }
        None
    }
}

/// An iterator over all prefixes of an [`ArchivedPrefixMap`] in lexicographic order.
pub struct Keys<'a, P: Prefix, T: Archive>(pub(super) Iter<'a, P, T>);

impl<'a, P: Prefix, T: Archive> Default for Keys<'a, P, T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<'a, P: Prefix, T: Archive> Iterator for Keys<'a, P, T> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(p, _)| p)
    }
}

/// An iterator over all values of an [`ArchivedPrefixMap`] in lexicographic order of their
/// prefixes.
pub struct Values<'a, P: Prefix, T: Archive>(Iter<'a, P, T>);

impl<'a, P: Prefix, T: Archive> Default for Values<'a, P, T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<'a, P: Prefix, T: Archive> Iterator for Values<'a, P, T> {
    type Item = &'a T::Archived;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, t)| t)
    }
}

/// An iterator that yields all elements in an `ArchivedPrefixMap` that cover (are a superset of) a
/// given prefix (including the prefix itself if present).
///
/// See [`PrefixMap::cover`] for an example.
pub struct Cover<'a, P: Prefix, T: Archive> {
    map: &'a ArchivedPrefixMap<P, T>,
    loc: Loc,
    depth: u32,
    lpm_elements: Vec<Loc>,
    key: P::R,
    prefix_len: u32,
}

impl<'a, P: Prefix, T: Archive> Cover<'a, P, T> {
    pub(super) fn new(map: &'a ArchivedPrefixMap<P, T>, prefix: &P) -> Self {
        let (key, prefix_len) = key_prefix_len(prefix);
        let mut s = Self {
            map,
            loc: Loc::root(),
            lpm_elements: Vec::new(),
            depth: 0,
            key,
            prefix_len,
        };
        s.populate_lpm_elements();
        s
    }

    fn step(&mut self) -> Option<()> {
        // check if we can still take one step
        if self.prefix_len < self.depth + K {
            return None;
        }

        let child_bit = child_bit(self.depth, self.key);
        self.loc = self.map.nodes[self.loc.idx()].child_loc(child_bit)?;
        self.depth += K;
        self.populate_lpm_elements();
        Some(())
    }

    fn populate_lpm_elements(&mut self) {
        self.lpm_elements = self.map.nodes[self.loc.idx()]
            .data_lpm_locs(self.depth, self.key, self.prefix_len)
            .rev()
            .collect();
    }
}

impl<'a, P: Prefix, T: Archive> Iterator for Cover<'a, P, T> {
    type Item = (P, &'a T::Archived);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // if we already have some elements in the LPM list, pop those.
            if let Some(data_loc) = self.lpm_elements.pop() {
                let prefix = reconstruct_prefix(self.key, self.depth, data_loc.bit as usize);
                return Some((prefix, &self.map.data[data_loc.idx()]));
            };

            self.step()?
        }
    }
}

/// An iterator that yields all prefixes in an `ArchivedPrefixMap` that cover (are a superset of) a
/// given prefix (including the prefix itself if present).
///
/// See [`PrefixMap::cover_keys`] for an example.
pub struct CoverKeys<'a, P: Prefix, T: Archive>(Cover<'a, P, T>);

impl<'a, P: Prefix, T: Archive> Iterator for CoverKeys<'a, P, T> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(p, _)| p)
    }
}

/// An iterator that yields all values of prefixes in an `ArchivedPrefixMap` that cover (are a
/// superset of) a given prefix (including the prefix itself if present).
///
/// See [`PrefixMap::cover_values`] for an example.
pub struct CoverValues<'a, P: Prefix, T: Archive>(Cover<'a, P, T>);

impl<'a, P: Prefix, T: Archive> Iterator for CoverValues<'a, P, T> {
    type Item = &'a T::Archived;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, t)| t)
    }
}

impl<'a, P: Prefix, T: Archive> IntoIterator for &'a ArchivedPrefixMap<P, T> {
    type Item = (P, &'a T::Archived);
    type IntoIter = Iter<'a, P, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<P, T> Eq for ArchivedPrefixMap<P, T>
where
    T: Archive,
    T::Archived: Eq,
{
}

impl<P, T> PartialEq for ArchivedPrefixMap<P, T>
where
    T: Archive,
    T::Archived: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        // We can directly compare nodes and data due to the canonical representation.
        self.nodes == other.nodes && self.data == other.data
    }
}

// Private functions
impl<P: Prefix, T: Archive> ArchivedPrefixMap<P, T> {
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

    /// Find the shortest-prefix match and return the position of the data of the LPM match, plus the
    /// depth of the node containing this data.
    #[inline(always)]
    fn find_spm<R: Key>(&self, key: R, prefix_len: u32) -> Option<(Loc, u32)> {
        let mut loc = Loc::root();
        let mut depth = 0;

        loop {
            let node = &self.nodes[loc.idx()];
            if let Some(data_loc) = node.data_spm_loc(depth, key, prefix_len) {
                return Some((data_loc, depth));
            }
            if prefix_len < depth + K {
                return None;
            }
            let child_bit = child_bit(depth, key);
            // SAFETY: `loc` starts as `Loc::root()` and is only updated to the result
            // of a prior `child()` call, which always returns a valid `Loc`.
            loc = self.nodes[loc.idx()].child_loc(child_bit)?;
            depth += K;
        }
    }

    /// Build a lex iter to iterate all children of the prefix.
    fn build_children_lex_iter(
        &self,
        key: P::R,
        prefix_len: u32,
    ) -> Option<MaskedLexIter<'_, P::R>> {
        let (loc, depth) = self.find_loc(key, prefix_len)?;
        let mut lex = MaskedLexIter::new(loc, depth, key, self);
        // Only take those that are children of the prefix
        lex.apply_data_mask(data_cover_mask(depth, key, prefix_len));
        lex.apply_child_mask(child_cover_mask(depth, key, prefix_len));
        Some(lex)
    }

    /// Build an iterator stack positioned at a given prefix in lex order.
    ///
    /// Navigates from the root toward `(key, prefix_len)`, pushing lex iterators onto the stack
    /// with entries before the target masked out. If `inclusive` is false, the exact target
    /// data slot is also excluded.
    fn build_iter_stack_at(
        &self,
        key: P::R,
        prefix_len: u32,
        inclusive: bool,
    ) -> Vec<MaskedLexIter<'_, P::R>> {
        let mut stack = Vec::new();
        let mut loc = Loc::root();
        let mut depth = 0u32;

        loop {
            let mut lex = MaskedLexIter::new(loc, depth, key, self);

            if prefix_len < depth + K {
                // Target falls within this node as a data slot.
                let data_bit = data_bit(key, prefix_len);
                let (data_mask, child_mask) = lex_after_data(data_bit);
                let data_mask = if inclusive {
                    data_mask
                } else {
                    data_mask & !(1 << data_bit)
                };
                lex.apply_data_mask(data_mask);
                lex.apply_child_mask(child_mask);
                stack.push(lex);
                break;
            }

            // Target is deeper; follow the child pointer.
            let child_bit = child_bit(depth, key);
            let (data_mask, child_mask) = lex_after_child(child_bit);
            lex.apply_data_mask(data_mask);
            lex.apply_child_mask(child_mask);
            stack.push(lex);

            // SAFETY: `loc` is valid (see above); `child()` returns a valid `Loc` if present.
            match self.nodes[loc.idx()].child_loc(child_bit) {
                Some(next) => {
                    loc = next;
                    depth += K;
                }
                None => break, // child doesn't exist; entries after it are already in the mask
            }
        }

        stack
    }
}

fn key_prefix_len<P: Prefix>(prefix: &P) -> (P::R, u32) {
    let key = prefix.repr();
    let prefix_len = prefix.prefix_len() as u32;
    (key, prefix_len)
}

/// Rkyv representation of a node with compacted indices
#[derive(Archive, Serialize, Default)]
#[rkyv(derive(Debug, Default, PartialEq, Eq, Hash))]
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
            Some(Loc::new(self.data_bitmap(), self.data_idx(), bit))
        } else {
            None
        }
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
        Some(Loc::new(self.data_bitmap(), self.data_idx(), msb_bit))
    }

    /// Get the data loc of the shortest prefix match in this node (if it exists).
    /// Returns Loc with bit (bitmap position) and computed slot.
    #[inline(always)]
    fn data_spm_loc<R: Key>(&self, depth: u32, key: R, prefix_len: u32) -> Option<Loc> {
        let nodes_present = self.data_bitmap & data_lpm_mask(depth, key, prefix_len);
        if nodes_present == 0 {
            return None;
        }
        let lsb_bit = nodes_present.trailing_zeros();
        Some(Loc::new(self.data_bitmap(), self.data_idx(), lsb_bit))
    }

    /// Get an iterator over all indices of data that cover (or equal) the prefix, i.e.,
    /// `(key, prefix_len)`.
    #[inline(always)]
    pub(super) fn data_lpm_locs<R: Key>(
        &self,
        depth: u32,
        key: R,
        prefix_len: u32,
    ) -> impl DoubleEndedIterator<Item = Loc> + 'static {
        let bitmap = self.data_bitmap();
        let filter = bitmap & data_lpm_mask(depth, key, prefix_len);
        bitmap_offset_locs(bitmap, filter, self.data_idx())
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
            Some(Loc::new(self.child_bitmap(), self.children_idx(), bit))
        } else {
            None
        }
    }

    /// Get an iterator over all children.
    #[inline(always)]
    pub(super) fn child_locs(&self) -> impl DoubleEndedIterator<Item = Loc> + 'static {
        let bitmap = self.child_bitmap();
        bitmap_offset_locs(bitmap, bitmap, self.children_idx())
    }
}

/// `bitmap` is used to compute the popcount (offset), while `filter` is used for filtering.
#[inline(always)]
fn bitmap_offset_locs(
    bitmap: u32,
    filter: u32,
    offset: u32,
) -> impl DoubleEndedIterator<Item = Loc> + 'static {
    (0..(NUM_CHILDREN as u32))
        .filter(move |&bit| filter & (1 << bit) != 0)
        .map(move |bit| Loc::new(bitmap, offset, bit))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct Loc {
    idx: u32,
    bit: u32,
}

impl Loc {
    #[inline(always)]
    pub(super) fn root() -> Self {
        Self { idx: 0, bit: 0 }
    }

    #[inline(always)]
    pub(super) fn new(bitmap: u32, offset: u32, bit: u32) -> Self {
        Loc {
            idx: offset + compute_slot(bitmap, bit),
            bit,
        }
    }

    #[inline(always)]
    pub(super) fn idx(&self) -> usize {
        self.idx as usize
    }
}

pub(super) struct MaskedLexIter<'a, R> {
    iter: std::slice::Iter<'static, LexElem>,
    depth: u32,
    key: R,
    // Original (unmasked) node: kept for correct POPCNT slot computation.
    node: &'a ArchivedNodeRepr,
    // Separate filter fields: apply_*_mask modifies these, not the node bitmaps.
    data_filter: u32,
    child_filter: u32,
}

#[derive(Clone, Copy)]
pub(super) enum LexIterElem<R> {
    Data(Loc, u32),
    Child(Loc, u32, R),
}

impl<'a, R> MaskedLexIter<'a, R> {
    pub(crate) fn root<P, T>(map: &'a ArchivedPrefixMap<P, T>) -> Self
    where
        P: Prefix<R = R>,
        R: Zero,
        T: Archive,
    {
        Self::new(Loc::root(), 0, R::zero(), map)
    }

    pub(crate) fn new<P, T>(loc: Loc, depth: u32, key: R, map: &'a ArchivedPrefixMap<P, T>) -> Self
    where
        P: Prefix<R = R>,
        T: Archive,
    {
        Self {
            iter: LEX_ORDER.iter(),
            depth,
            key,
            node: &map.nodes[loc.idx()],
            data_filter: u32::MAX,
            child_filter: u32::MAX,
        }
    }

    pub(crate) fn apply_data_mask(&mut self, mask: u32) {
        // Only reduce the set of offsets to yield; keep node.data_bitmap intact for POPCNT.
        self.data_filter &= mask;
    }

    pub(crate) fn apply_child_mask(&mut self, mask: u32) {
        self.child_filter &= mask;
    }
}

impl<'a, R: Key> Iterator for MaskedLexIter<'a, R> {
    type Item = LexIterElem<R>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let next = *self.iter.next()?;
            match next.decode() {
                Ok(data_bit) => {
                    // Check original bitmap (for existence) AND filter (for masking).
                    if self.data_filter & (1 << data_bit) != 0 {
                        if let Some(loc) = self.node.data_loc(data_bit) {
                            return Some(LexIterElem::Data(loc, self.depth));
                        }
                    }
                }
                Err(child_bit) => {
                    if self.node.has_child_bit(child_bit)
                        && (self.child_filter & (1 << child_bit)) != 0
                    {
                        return Some(LexIterElem::Child(
                            Loc::new(
                                self.node.child_bitmap(),
                                self.node.children_idx(),
                                child_bit,
                            ),
                            self.depth + K,
                            extend_repr(self.key, self.depth, child_bit),
                        ));
                    }
                }
            }
        }
    }
}

/// The `rkyv` resolver for [`ArchivedPrefixMap`] and [`super::ArchivedPrefixSet`].
pub struct PrefixMapResolver {
    pub(super) nodes: VecResolver,
    pub(super) nodes_len: usize,
    pub(super) data: VecResolver,
    pub(super) data_len: usize,
}
