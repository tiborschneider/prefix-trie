//! Module containing the archived prefix set and access methods.

use rkyv::{bytecheck::CheckBytes, Portable};

// needed for doc references.
#[allow(unused_imports)]
use crate::PrefixSet;
use crate::{
    rkyv::{
        map::{CoverKeys, Keys},
        ArchivedPrefixMap,
    },
    Prefix,
};

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
pub struct ArchivedPrefixSet<P>(pub(super) ArchivedPrefixMap<P, ()>);

impl<P> ArchivedPrefixSet<P> {
    /// Returns the number of prefixes stored in the set.
    ///
    /// This is the number of stored prefixes, not the number of addresses they cover (see
    /// [`address_count`](Self::address_count)).
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the set contains no prefixes.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<P: Prefix> ArchivedPrefixSet<P> {
    /// Count the number of unique addresses covered by all prefixes in the set. If the entire trie
    /// is fully covered, the function returns `None` (as it contains `P::R::MAX + 1` addresses).
    /// Overlapping prefixes are not double-counted.
    ///
    /// To avoid double-counting, the function traverses the (partial) trie once, skipping nodes
    /// that are already covered.
    ///
    /// This mirrors [`PrefixSet::address_count`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::PrefixSet;
    /// # use prefix_trie::rkyv::ArchivedPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = PrefixSet::<P>::new();
    /// ps.insert(p!("192.0.2.0/24"));
    /// ps.insert(p!("198.51.100.0/24"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(set.address_count(), Some(512));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn address_count(&self) -> Option<P::R> {
        self.0.address_count()
    }

    /// Check whether `prefix` is present in the set.
    ///
    /// This mirrors [`PrefixSet::contains`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::PrefixSet;
    /// # use prefix_trie::rkyv::ArchivedPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = PrefixSet::<P>::new();
    /// ps.insert(p!("10.0.1.0/24"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert!(set.contains(&p!("10.0.1.0/24")));
    /// assert!(!set.contains(&p!("10.0.2.0/24")));
    /// assert!(!set.contains(&p!("10.0.0.0/23")));
    /// assert!(!set.contains(&p!("10.0.1.128/25")));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn contains(&self, prefix: &P) -> bool {
        self.0.contains_key(prefix)
    }

    /// Get the canonical (reconstructed) prefix that matches `prefix` exactly.
    ///
    /// Prefixes are not stored verbatim. They are reconstructed from the trie position, so host
    /// bits are not preserved.
    ///
    /// This mirrors [`PrefixSet::get`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::PrefixSet;
    /// # use prefix_trie::rkyv::ArchivedPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = PrefixSet::<P>::new();
    /// ps.insert(p!("10.0.1.0/24"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(set.get(&p!("10.0.1.0/24")), Some(p!("10.0.1.0/24")));
    /// assert_eq!(set.get(&p!("10.0.2.0/24")), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn get(&self, prefix: &P) -> Option<P> {
        self.0.get_key_value(prefix).map(|(p, _)| p)
    }

    /// Get the longest prefix in the set that contains `prefix`.
    ///
    /// This mirrors [`PrefixSet::get_lpm`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::PrefixSet;
    /// # use prefix_trie::rkyv::ArchivedPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = PrefixSet::<P>::new();
    /// ps.insert(p!("10.0.1.0/24"));
    /// ps.insert(p!("10.0.0.0/23"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(set.get_lpm(&p!("10.0.1.1/32")), Some(p!("10.0.1.0/24")));
    /// assert_eq!(set.get_lpm(&p!("10.0.0.0/24")), Some(p!("10.0.0.0/23")));
    /// assert_eq!(set.get_lpm(&p!("10.0.2.0/24")), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn get_lpm(&self, prefix: &P) -> Option<P> {
        self.0.get_lpm_prefix(prefix)
    }

    /// Get the shortest prefix in the set that contains `prefix`.
    ///
    /// This mirrors [`PrefixSet::get_spm`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::PrefixSet;
    /// # use prefix_trie::rkyv::ArchivedPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = PrefixSet::<P>::new();
    /// ps.insert(p!("10.0.1.0/24"));
    /// ps.insert(p!("10.0.0.0/23"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(set.get_spm(&p!("10.0.1.1/32")), Some(p!("10.0.0.0/23")));
    /// assert_eq!(set.get_spm(&p!("10.0.0.0/23")), Some(p!("10.0.0.0/23")));
    /// assert_eq!(set.get_spm(&p!("10.0.2.0/24")), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn get_spm(&self, prefix: &P) -> Option<P> {
        self.0.get_spm_prefix(prefix)
    }

    /// Check whether `prefix` is covered by the set, i.e., whether the set contains `prefix` itself
    /// or any less-specific prefix that contains it.
    ///
    /// This is equivalent to `self.cover(prefix).next().is_some()`, but stops at the first (shortest)
    /// covering prefix. See [`cover`](Self::cover) to iterate over the covering prefixes themselves.
    ///
    /// This function does not perform aggregation. That means that, even if both the left and right
    /// children of `p` are present in the set, `is_covered(p)` may still return `false`. See
    /// [`is_covered_in_aggregate`](Self::is_covered_in_aggregate) for that case.
    ///
    /// This mirrors [`PrefixSet::is_covered`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::PrefixSet;
    /// # use prefix_trie::rkyv::ArchivedPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = PrefixSet::<P>::new();
    /// ps.insert(p!("10.0.0.0/8"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert!(set.is_covered(&p!("10.0.0.0/8")));
    /// assert!(set.is_covered(&p!("10.1.2.0/24")));
    /// assert!(!set.is_covered(&p!("11.0.0.0/8")));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn is_covered(&self, prefix: &P) -> bool {
        self.0.is_covered(prefix)
    }

    /// Check whether every address in `prefix` is covered by the set, i.e., whether `prefix`'s
    /// entire range is tiled by members of the set, even if no single member covers `prefix` on
    /// its own. See [`is_covered`](Self::is_covered) for the (cheaper, stricter) single-member
    /// check.
    ///
    /// This mirrors [`PrefixSet::is_covered_in_aggregate`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::PrefixSet;
    /// # use prefix_trie::rkyv::ArchivedPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = PrefixSet::<P>::new();
    /// ps.insert(p!("10.0.0.0/9"));
    /// ps.insert(p!("10.128.0.0/9"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert!(!set.is_covered(&p!("10.0.0.0/8")));
    /// assert!(set.is_covered_in_aggregate(&p!("10.0.0.0/8")));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn is_covered_in_aggregate(&self, prefix: &P) -> bool {
        self.0.is_covered_in_aggregate(prefix)
    }

    /// An iterator visiting all keys in lexicographic order. The iterator element type is
    /// reconstructed prefixes `P`.
    ///
    /// This mirrors [`PrefixSet::iter`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::PrefixSet;
    /// # use prefix_trie::rkyv::ArchivedPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = PrefixSet::<P>::new();
    /// ps.insert(p!("10.0.0.0/23"));
    /// ps.insert(p!("10.0.0.0/24"));
    /// ps.insert(p!("10.0.2.0/23"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     set.iter().collect::<Vec<_>>(),
    ///     vec![p!("10.0.0.0/23"), p!("10.0.0.0/24"), p!("10.0.2.0/23")],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn iter(&self) -> Keys<'_, P, ()> {
        self.0.keys()
    }

    /// Iterate over `prefix` and all more-specific prefixes contained within it, including `prefix`
    /// itself if it is present. The iterator yields reconstructed prefixes `P` in lexicographic
    /// order.
    ///
    /// **Note**: Consider using [`crate::AsView::view_at`] as an alternative.
    ///
    /// This mirrors [`PrefixSet::children`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::PrefixSet;
    /// # use prefix_trie::rkyv::ArchivedPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = PrefixSet::<P>::new();
    /// ps.insert(p!("10.0.0.0/22"));
    /// ps.insert(p!("10.0.0.0/23"));
    /// ps.insert(p!("10.0.2.0/23"));
    /// ps.insert(p!("10.0.0.0/24"));
    /// ps.insert(p!("10.0.2.0/24"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
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
        Keys(self.0.children(prefix))
    }

    /// Iterate over all prefixes starting at `prefix`, in lexicographic order.
    ///
    /// This enables stateless, cursor-based pagination: pass the last-seen prefix to resume.
    ///
    /// - If `inclusive` is `true`, the iterator includes `prefix` (if present).
    /// - If `inclusive` is `false`, the iterator starts after `prefix`. Prefixes more specific than
    ///   `prefix` (its children) are still yielded.
    ///
    /// If `prefix` is not present in the set, the iterator starts at the first prefix that would
    /// come after `prefix` in lexicographic order, regardless of `inclusive`.
    ///
    /// This mirrors [`PrefixSet::iter_from`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::PrefixSet;
    /// # use prefix_trie::rkyv::ArchivedPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = PrefixSet::<P>::new();
    /// ps.insert(p!("10.0.0.0/8"));
    /// ps.insert(p!("10.1.0.0/16"));
    /// ps.insert(p!("10.2.0.0/16"));
    /// ps.insert(p!("10.3.0.0/16"));
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
    ///
    /// assert_eq!(
    ///     set.iter_from(&p!("10.1.0.0/16"), false).take(2).collect::<Vec<_>>(),
    ///     vec![p!("10.2.0.0/16"), p!("10.3.0.0/16")],
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(all(feature = "rkyv", feature = "ipnet")))]
    /// # fn main() {}
    /// ```
    pub fn iter_from<'a>(&'a self, prefix: &P, inclusive: bool) -> Keys<'a, P, ()> {
        Keys(self.0.iter_from(prefix, inclusive))
    }

    /// Iterate over all prefixes in the set that cover `prefix`, including `prefix` itself if it is
    /// present. The returned iterator yields reconstructed prefixes `P`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// This mirrors [`PrefixSet::cover`], but operates on the archived set.
    ///
    /// ```
    /// # use prefix_trie::PrefixSet;
    /// # use prefix_trie::rkyv::ArchivedPrefixSet;
    /// # use rkyv::rancor::Error;
    /// # #[cfg(all(feature = "rkyv", feature = "ipnet"))]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # type P = ipnet::Ipv4Net;
    /// # macro_rules! p { ($s:literal) => { $s.parse::<P>()? } }
    /// let mut ps = PrefixSet::<P>::new();
    /// ps.insert(p!("10.0.0.0/8"));
    /// ps.insert(p!("10.1.0.0/16"));
    /// ps.insert(p!("10.1.1.0/24"));
    /// ps.insert(p!("10.1.2.0/24")); // disjoint prefixes are not covered
    /// ps.insert(p!("10.1.1.0/25")); // more specific prefixes are not covered
    /// ps.insert(p!("11.0.0.0/8"));  // unrelated branches are skipped
    ///
    /// let bytes = rkyv::to_bytes::<Error>(&ps)?;
    /// let set: &ArchivedPrefixSet<P> = rkyv::access::<_, Error>(&bytes)?;
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
        self.0.cover_keys(prefix)
    }
}

impl<'a, P: Prefix> IntoIterator for &'a ArchivedPrefixSet<P> {
    type Item = P;
    type IntoIter = Keys<'a, P, ()>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<P> std::fmt::Debug for ArchivedPrefixSet<P>
where
    P: Prefix + std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<P> Eq for ArchivedPrefixSet<P> {}

impl<P> PartialEq for ArchivedPrefixSet<P> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
