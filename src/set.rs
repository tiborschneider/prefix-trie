//! Prefix set implemented on top of [`PrefixMap`].

use std::fmt::{Debug, Formatter, Result as FmtResult};

use crate::Prefix;

use super::{
    map::{CoverKeys, PrefixMap},
    trieview::{AsView, TrieRef, TrieRefMut, TrieView},
};

/// Set of prefixes, organized in a dense prefix trie.
///
/// This structure gives efficient access to the longest prefix in the set that contains another
/// prefix. Prefixes returned from this set are reconstructed from the trie and are therefore
/// returned by value. Host bits outside the prefix length are not preserved.
///
/// You can perform union, intersection, and difference operations by creating a view with
/// [`AsView`].
#[derive(Clone)]
pub struct PrefixSet<P>(pub(crate) PrefixMap<P, ()>);

impl<P: Prefix> PrefixSet<P> {
    /// Create a new, empty prefix set.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// assert!(set.is_empty());
    /// # }
    /// ```
    pub fn new() -> Self {
        Self(Default::default())
    }

    /// Returns the number of prefixes stored in `self`.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// assert_eq!(set.len(), 0);
    /// set.insert("192.168.0.0/24".parse()?);
    /// set.insert("192.168.1.0/24".parse()?);
    /// assert_eq!(set.len(), 2);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the set contains no prefixes.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// assert!(set.is_empty());
    /// set.insert("192.168.0.0/24".parse()?);
    /// assert!(!set.is_empty());
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the amount of memory used by this data structure in bytes.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// let before = set.mem_size();
    /// set.insert("192.168.0.0/24".parse()?);
    /// assert!(set.mem_size() >= before);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn mem_size(&self) -> usize {
        self.0.mem_size()
    }

    /// Check whether `prefix` is present in the set using exact prefix matching.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// set.insert("192.168.1.0/24".parse()?);
    /// assert!(set.contains(&"192.168.1.0/24".parse()?));
    /// assert!(!set.contains(&"192.168.2.0/24".parse()?));
    /// assert!(!set.contains(&"192.168.0.0/23".parse()?));
    /// assert!(!set.contains(&"192.168.1.128/25".parse()?));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn contains(&self, prefix: &P) -> bool {
        self.0.contains_key(prefix)
    }

    /// Get the canonical reconstructed prefix by exact prefix matching.
    ///
    /// Prefixes are not stored verbatim. They are reconstructed from the trie position, so host
    /// bits masked out by the prefix length are not preserved.
    pub fn get(&self, prefix: &P) -> Option<P> {
        self.0.get_key_value(prefix).map(|(p, _)| p)
    }

    /// Get the longest prefix in the set that contains `prefix`.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// set.insert("192.168.1.0/24".parse()?);
    /// set.insert("192.168.0.0/23".parse()?);
    /// assert_eq!(set.get_lpm(&"192.168.1.1/32".parse()?), Some("192.168.1.0/24".parse()?));
    /// assert_eq!(set.get_lpm(&"192.168.1.0/24".parse()?), Some("192.168.1.0/24".parse()?));
    /// assert_eq!(set.get_lpm(&"192.168.0.0/24".parse()?), Some("192.168.0.0/23".parse()?));
    /// assert_eq!(set.get_lpm(&"192.168.2.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_lpm(&self, prefix: &P) -> Option<P> {
        self.0.get_lpm_prefix(prefix)
    }

    /// Get the shortest prefix in the set that contains `prefix`.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// set.insert("192.168.1.0/24".parse()?);
    /// set.insert("192.168.0.0/23".parse()?);
    /// assert_eq!(set.get_spm(&"192.168.1.1/32".parse()?), Some("192.168.0.0/23".parse()?));
    /// assert_eq!(set.get_spm(&"192.168.1.0/24".parse()?), Some("192.168.0.0/23".parse()?));
    /// assert_eq!(set.get_spm(&"192.168.0.0/23".parse()?), Some("192.168.0.0/23".parse()?));
    /// assert_eq!(set.get_spm(&"192.168.2.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_spm(&self, prefix: &P) -> Option<P> {
        self.0.get_spm_prefix(prefix)
    }

    /// Adds a prefix to the set.
    ///
    /// Returns whether the prefix was newly inserted.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// assert!(set.insert("192.168.0.0/23".parse()?));
    /// assert!(set.insert("192.168.1.0/24".parse()?));
    /// assert!(!set.insert("192.168.1.0/24".parse()?));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn insert(&mut self, prefix: P) -> bool {
        self.0.insert(prefix, ()).is_none()
    }

    /// Removes `prefix` from the set and returns whether it was present.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// let prefix = "192.168.1.0/24".parse()?;
    /// set.insert(prefix);
    /// assert!(set.contains(&prefix));
    /// assert!(set.remove(&prefix));
    /// assert!(!set.contains(&prefix));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn remove(&mut self, prefix: &P) -> bool {
        self.0.remove(prefix).is_some()
    }

    /// Removes `prefix` from the set and may leave empty trie nodes in place.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// let prefix = "192.168.1.0/24".parse()?;
    /// set.insert(prefix);
    /// assert!(set.contains(&prefix));
    /// assert!(set.remove_keep_tree(&prefix));
    /// assert!(!set.contains(&prefix));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn remove_keep_tree(&mut self, prefix: &P) -> bool {
        self.0.remove_keep_tree(prefix).is_some()
    }

    /// Remove all prefixes that are contained within `prefix`.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// set.insert("192.168.0.0/22".parse()?);
    /// set.insert("192.168.0.0/23".parse()?);
    /// set.insert("192.168.0.0/24".parse()?);
    /// set.insert("192.168.2.0/23".parse()?);
    /// set.insert("192.168.2.0/24".parse()?);
    /// set.remove_children(&"192.168.0.0/23".parse()?);
    /// assert!(!set.contains(&"192.168.0.0/23".parse()?));
    /// assert!(!set.contains(&"192.168.0.0/24".parse()?));
    /// assert!(set.contains(&"192.168.2.0/23".parse()?));
    /// assert!(set.contains(&"192.168.2.0/24".parse()?));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn remove_children(&mut self, prefix: &P) {
        self.0.remove_children(prefix)
    }

    /// Clear the set while keeping allocated memory for reuse.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// set.insert("192.168.0.0/24".parse()?);
    /// set.insert("192.168.1.0/24".parse()?);
    /// set.clear();
    /// assert!(set.is_empty());
    /// assert!(!set.contains(&"192.168.0.0/24".parse()?));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn clear(&mut self) {
        self.0.clear()
    }

    /// Iterate over all prefixes in lexicographic order.
    ///
    /// The iterator yields canonical owned prefixes.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// set.insert("192.168.0.0/23".parse()?);
    /// set.insert("192.168.0.0/24".parse()?);
    /// set.insert("192.168.2.0/23".parse()?);
    /// assert_eq!(
    ///     set.iter().collect::<Vec<_>>(),
    ///     vec![
    ///         "192.168.0.0/23".parse()?,
    ///         "192.168.0.0/24".parse()?,
    ///         "192.168.2.0/23".parse()?,
    ///     ]
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn iter(&self) -> Iter<'_, P> {
        self.into_iter()
    }

    /// Return an iterator starting at the given prefix in lexicographic order.
    ///
    /// If `inclusive` is `true`, the iterator includes `prefix` (if present).
    /// If `inclusive` is `false`, the iterator starts after `prefix`.
    ///
    /// If `prefix` is not present in the set, the iterator starts at the first prefix that
    /// would come after it in lexicographic order, regardless of `inclusive`.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// set.insert("10.0.0.0/8".parse()?);
    /// set.insert("10.1.0.0/16".parse()?);
    /// set.insert("10.2.0.0/16".parse()?);
    /// set.insert("10.3.0.0/16".parse()?);
    ///
    /// // Cursor pagination: skip last seen, fetch next page
    /// let page: Vec<_> = set.iter_from(&"10.1.0.0/16".parse()?, false).take(2).collect();
    /// assert_eq!(page, vec!["10.2.0.0/16".parse()?, "10.3.0.0/16".parse()?]);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn iter_from<'a>(&'a self, prefix: &P, inclusive: bool) -> Iter<'a, P> {
        Iter(self.0.iter_from(prefix, inclusive))
    }

    /// Keep only prefixes that satisfy the predicate `f`.
    ///
    /// ```
    /// use prefix_trie::{Prefix, PrefixSet};
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// set.insert("192.168.0.0/24".parse()?);
    /// set.insert("192.168.1.0/24".parse()?);
    /// set.insert("192.168.2.0/24".parse()?);
    /// set.insert("192.168.2.0/25".parse()?);
    /// set.retain(|p| p.prefix_len() == 24);
    /// assert!(set.contains(&"192.168.0.0/24".parse()?));
    /// assert!(set.contains(&"192.168.1.0/24".parse()?));
    /// assert!(set.contains(&"192.168.2.0/24".parse()?));
    /// assert!(!set.contains(&"192.168.2.0/25".parse()?));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&P) -> bool,
    {
        self.0.retain(|p, _| f(p));
    }

    /// Get an iterator over `prefix` and all more-specific prefixes contained within it.
    ///
    /// The iterator yields canonical owned prefixes in lexicographic order.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// set.insert("192.168.0.0/22".parse()?);
    /// set.insert("192.168.0.0/23".parse()?);
    /// set.insert("192.168.2.0/23".parse()?);
    /// set.insert("192.168.0.0/24".parse()?);
    /// set.insert("192.168.2.0/24".parse()?);
    /// assert_eq!(
    ///     set.children(&"192.168.0.0/23".parse()?).collect::<Vec<_>>(),
    ///     vec![
    ///         "192.168.0.0/23".parse()?,
    ///         "192.168.0.0/24".parse()?,
    ///     ]
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn children<'a>(&'a self, prefix: &P) -> Iter<'a, P> {
        Iter(self.0.children(prefix))
    }

    /// Iterate over all prefixes in the set that cover `prefix`.
    ///
    /// This includes `prefix` itself if it is present in the set. The iterator yields canonical
    /// owned prefixes ordered by prefix length.
    ///
    /// ```
    /// use prefix_trie::PrefixSet;
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// let p0 = "10.0.0.0/8".parse()?;
    /// let p1 = "10.1.0.0/16".parse()?;
    /// let p2 = "10.1.1.0/24".parse()?;
    /// set.insert(p0);
    /// set.insert(p1);
    /// set.insert(p2);
    /// set.insert("10.1.2.0/24".parse()?);
    /// set.insert("10.1.1.0/25".parse()?);
    /// set.insert("11.0.0.0/8".parse()?);
    /// assert_eq!(set.cover(&p2).collect::<Vec<_>>(), vec![p0, p1, p2]);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn cover<'a>(&'a self, prefix: &P) -> CoverKeys<'a, P, ()> {
        self.0.cover_keys(prefix)
    }
}

impl<P: Prefix> Default for PrefixSet<P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P> PartialEq for PrefixSet<P>
where
    P: Prefix,
{
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.view().eq_keys(other)
    }
}

impl<P> Eq for PrefixSet<P> where P: Prefix {}

impl<P> Debug for PrefixSet<P>
where
    P: Prefix + Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_set().entries(self.iter()).finish()
    }
}

/// An iterator over all prefixes of a [`PrefixSet`] in lexicographic order.
///
/// This iterator yields canonical owned prefixes.
#[derive(Clone, Default)]
pub struct Iter<'a, P: Prefix>(crate::map::Iter<'a, P, ()>);

impl<P: Prefix> Iterator for Iter<'_, P> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(p, _)| p)
    }
}

/// A consuming iterator over all prefixes of a [`PrefixSet`] in lexicographic order.
#[derive(Clone)]
pub struct IntoIter<P: Prefix>(crate::map::IntoIter<P, ()>);

impl<P: Prefix> Iterator for IntoIter<P> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(p, _)| p)
    }
}

impl<P: Prefix> IntoIterator for PrefixSet<P> {
    type Item = P;

    type IntoIter = IntoIter<P>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

impl<'a, P: Prefix> IntoIterator for &'a PrefixSet<P> {
    type Item = P;

    type IntoIter = Iter<'a, P>;

    fn into_iter(self) -> Self::IntoIter {
        Iter(self.0.iter())
    }
}

impl<P: Prefix> FromIterator<P> for PrefixSet<P> {
    fn from_iter<I: IntoIterator<Item = P>>(iter: I) -> Self {
        let mut set = Self::new();
        for p in iter {
            set.insert(p);
        }
        set
    }
}

impl<'a, P: Prefix> AsView<'a> for &'a PrefixSet<P> {
    type P = P;
    type View = TrieRef<'a, P, ()>;

    fn view(self) -> Self::View {
        TrieRef::new_root(self.0.table())
    }
}

impl<'a, P: Prefix> AsView<'a> for &'a mut PrefixSet<P> {
    type P = P;
    type View = TrieRefMut<'a, P, ()>;

    fn view(self) -> Self::View {
        let raw = self.0.table_mut().raw_cells();
        TrieRefMut::new_root(self.0.table(), raw)
    }
}
