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
    /// Returns the number of elements stored in `self`.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the map contains no elements.
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
    /// See [`PrefixSet::address_count`] for an example.
    #[inline(always)]
    pub fn address_count(&self) -> Option<P::R> {
        self.0.address_count()
    }

    /// Check whether some (exact) prefix is present in the set, without using longest prefix match.
    ///
    /// See [`PrefixSet::contains`] for an example.
    #[inline(always)]
    pub fn contains(&self, prefix: &P) -> bool {
        self.0.contains_key(prefix)
    }

    /// Get the canonical (reconstructed) prefix by exact prefix matching.
    ///
    /// Prefixes are not stored verbatim. They are reconstructed from the trie position, so host
    /// bits are not preserved.
    #[inline(always)]
    pub fn get(&self, prefix: &P) -> Option<P> {
        self.0.get_key_value(prefix).map(|(p, _)| p)
    }

    /// Get the longest prefix in the set that contains `prefix`.
    ///
    /// See [`PrefixSet::get_lpm`] for an example.
    #[inline(always)]
    pub fn get_lpm(&self, prefix: &P) -> Option<P> {
        self.0.get_lpm_prefix(prefix)
    }

    /// Get the shortest prefix in the set that contains `prefix`.
    ///
    /// See [`PrefixSet::get_spm`] for an example.
    #[inline(always)]
    pub fn get_spm(&self, prefix: &P) -> Option<P> {
        self.0.get_spm_prefix(prefix)
    }

    /// An iterator visiting all keys in lexicographic order. The iterator element type is
    /// reconstructed prefixes `P`.
    ///
    /// See [`PrefixSet::iter`] for an example.
    pub fn iter(&self) -> Keys<'_, P, ()> {
        self.0.keys()
    }

    /// Get an iterator over the node itself and all children. All elements returned have a prefix
    /// that is contained within `prefix` itself (or are the same). The iterator yields
    /// reconstructed prefixes `P` in lexicographic order.
    ///
    /// **Note**: Consider using [`crate::AsView::view_at`] as an alternative.
    ///
    /// See [`PrefixSet::children`] for an example.
    pub fn children<'a>(&'a self, prefix: &P) -> Keys<'a, P, ()> {
        Keys(self.0.children(prefix))
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
    /// See [`PrefixSet::iter_from`] for an example.
    pub fn iter_from<'a>(&'a self, prefix: &P, inclusive: bool) -> Keys<'a, P, ()> {
        Keys(self.0.iter_from(prefix, inclusive))
    }

    /// Iterate over all prefixes in the set that cover the given `prefix` (including `prefix` itself
    /// if that is present in the map). The returned iterator yields reconstructed prefixes `P`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// See [`PrefixSet::cover`] for an example.
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
