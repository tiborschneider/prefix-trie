//! PrefixSet, that is implemened as a simple binary tree, based on the [`PrefixMap`].

use crate::{map::CoverKeys, Prefix, PrefixMap};

mod difference;
mod intersection;
mod union;
pub use difference::Difference;
pub use intersection::Intersection;
pub use union::Union;

/// Set of prefixes, organized in a tree. This strucutre gives efficient access to the longest
/// prefix in the set that contains another prefix.
#[derive(Clone)]
pub struct PrefixSet<P>(pub(crate) PrefixMap<P, ()>);

impl<P: Prefix> PrefixSet<P> {
    /// Create a new, empty prefixset.
    pub fn new() -> Self {
        Self(Default::default())
    }

    /// Check wether some prefix is present in the set, without using longest prefix match.
    ///
    /// ```
    /// # use prefix_trie::*;
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

    /// Get the longest prefix in the set that contains the given preifx.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// set.insert("192.168.1.0/24".parse()?);
    /// set.insert("192.168.0.0/23".parse()?);
    /// assert_eq!(set.get_lpm(&"192.168.1.1/32".parse()?), Some(&"192.168.1.0/24".parse()?));
    /// assert_eq!(set.get_lpm(&"192.168.1.0/24".parse()?), Some(&"192.168.1.0/24".parse()?));
    /// assert_eq!(set.get_lpm(&"192.168.0.0/24".parse()?), Some(&"192.168.0.0/23".parse()?));
    /// assert_eq!(set.get_lpm(&"192.168.2.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_lpm<'a>(&'a self, prefix: &P) -> Option<&'a P> {
        self.0.get_lpm(prefix).map(|(p, _)| p)
    }

    /// Get the shortest prefix in the set that contains the given preifx.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// set.insert("192.168.1.0/24".parse()?);
    /// set.insert("192.168.0.0/23".parse()?);
    /// assert_eq!(set.get_spm(&"192.168.1.1/32".parse()?), Some(&"192.168.0.0/23".parse()?));
    /// assert_eq!(set.get_spm(&"192.168.1.0/24".parse()?), Some(&"192.168.0.0/23".parse()?));
    /// assert_eq!(set.get_spm(&"192.168.0.0/23".parse()?), Some(&"192.168.0.0/23".parse()?));
    /// assert_eq!(set.get_spm(&"192.168.2.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_spm<'a>(&'a self, prefix: &P) -> Option<&'a P> {
        self.0.get_spm_prefix(prefix)
    }

    /// Adds a value to the set.
    ///
    /// Returns whether the value was newly inserted. That is:
    /// - If the set did not previously contain this value, `true` is returned.
    /// - If the set already contained this value, `false` is returned.
    ///
    /// ```
    /// # use prefix_trie::*;
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

    /// Removes a value from the set. Returns whether the value was present in the set.
    ///
    /// ```
    /// # use prefix_trie::*;
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

    /// Removes a prefix from the set, returning wether the prefix was present or not. In contrast
    /// to [`Self::remove`], his operation will keep the tree structure as is, but only remove the
    /// element from it. This allows any future `insert` on the same prefix to be faster. However
    /// future reads from the tree might be a bit slower because they need to traverse more nodes.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// let prefix = "192.168.1.0/24".parse()?;
    /// set.insert(prefix);
    /// assert!(set.contains(&prefix));
    /// assert!(set.remove_keep_tree(&prefix));
    /// assert!(!set.contains(&prefix));
    ///
    /// // future inserts of the same key are now faster!
    /// set.insert(prefix);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn remove_keep_tree(&mut self, prefix: &P) -> bool {
        self.0.remove_keep_tree(prefix).is_some()
    }

    /// Remove all elements that are contained within `prefix`. This will change the tree
    /// structure. This operation is `O(n)`, as the entries must be freed up one-by-one.
    ///
    /// ```
    /// # use prefix_trie::*;
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

    /// Clear the set but keep the allocated memory.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// set.insert("192.168.0.0/24".parse()?);
    /// set.insert("192.168.1.0/24".parse()?);
    /// set.clear();
    /// assert!(!set.contains(&"192.168.0.0/24".parse()?));
    /// assert!(!set.contains(&"192.168.1.0/24".parse()?));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn clear(&mut self) {
        self.0.clear()
    }

    /// Iterate over all prefixes in the set
    pub fn iter(&self) -> Iter<'_, P> {
        self.into_iter()
    }

    /// Keep only the elements in the map that satisfy the given condition `f`.
    ///
    /// ```
    /// # use prefix_trie::*;
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
        let _ = self.0._retain(0, None, false, None, false, |p, _| f(p));
    }

    /// Return an iterator that traverses both trees simultaneously and yields the union of both
    /// sets in lexicographic order.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set_a: PrefixSet<ipnet::Ipv4Net> = PrefixSet::from_iter([
    ///     "192.168.0.0/22".parse()?,
    ///     "192.168.0.0/24".parse()?,
    ///     "192.168.2.0/23".parse()?,
    /// ]);
    /// let mut set_b: PrefixSet<ipnet::Ipv4Net> = PrefixSet::from_iter([
    ///     "192.168.0.0/22".parse()?,
    ///     "192.168.0.0/23".parse()?,
    ///     "192.168.2.0/24".parse()?,
    /// ]);
    /// assert_eq!(
    ///     set_a.union(&set_b).copied().collect::<Vec<_>>(),
    ///     vec![
    ///         "192.168.0.0/22".parse()?,
    ///         "192.168.0.0/23".parse()?,
    ///         "192.168.0.0/24".parse()?,
    ///         "192.168.2.0/23".parse()?,
    ///         "192.168.2.0/24".parse()?,
    ///     ]
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn union<'a>(&'a self, other: &'a Self) -> Union<'a, P> {
        Union {
            set_a: &self.0,
            set_b: &other.0,
            nodes: vec![union::UnionIndex::Both(0, 0)],
        }
    }

    /// Return an iterator that traverses both trees simultaneously and yields the intersection of
    /// both sets in lexicographic order.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set_a: PrefixSet<ipnet::Ipv4Net> = PrefixSet::from_iter([
    ///     "192.168.0.0/22".parse()?,
    ///     "192.168.0.0/24".parse()?,
    ///     "192.168.2.0/23".parse()?,
    /// ]);
    /// let mut set_b: PrefixSet<ipnet::Ipv4Net> = PrefixSet::from_iter([
    ///     "192.168.0.0/22".parse()?,
    ///     "192.168.0.0/24".parse()?,
    ///     "192.168.2.0/24".parse()?,
    /// ]);
    /// assert_eq!(
    ///     set_a.intersection(&set_b).copied().collect::<Vec<_>>(),
    ///     vec!["192.168.0.0/22".parse()?, "192.168.0.0/24".parse()?]
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn intersection<'a>(&'a self, other: &'a Self) -> Intersection<'a, P> {
        Intersection {
            set_a: &self.0,
            set_b: &other.0,
            nodes: vec![intersection::IntersectionIndex::Both(0, 0)],
        }
    }

    /// Return an iterator that traverses both trees simultaneously and yields the difference of
    /// both sets in lexicographic order.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set_a: PrefixSet<ipnet::Ipv4Net> = PrefixSet::from_iter([
    ///     "192.168.0.0/22".parse()?,
    ///     "192.168.0.0/24".parse()?,
    ///     "192.168.2.0/23".parse()?,
    /// ]);
    /// let mut set_b: PrefixSet<ipnet::Ipv4Net> = PrefixSet::from_iter([
    ///     "192.168.0.0/22".parse()?,
    ///     "192.168.0.0/24".parse()?,
    ///     "192.168.2.0/24".parse()?,
    /// ]);
    /// assert_eq!(
    ///     set_a.difference(&set_b).copied().collect::<Vec<_>>(),
    ///     vec!["192.168.2.0/23".parse()?]
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn difference<'a>(&'a self, other: &'a Self) -> Difference<'a, P> {
        Difference {
            set_a: &self.0,
            set_b: &other.0,
            nodes: vec![difference::DifferenceIndex::Both(0, 0)],
        }
    }

    /// Iterate over all prefixes in the set that covers the given `prefix` (including `prefix`
    /// itself if that is present in the set). The returned iterator yields `&'a P`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut set: PrefixSet<ipnet::Ipv4Net> = PrefixSet::new();
    /// let p0 = "10.0.0.0/8".parse()?;
    /// let p1 = "10.1.0.0/16".parse()?;
    /// let p2 = "10.1.1.0/24".parse()?;
    /// set.insert(p0);
    /// set.insert(p1);
    /// set.insert(p2);
    /// set.insert("10.1.2.0/24".parse()?); // disjoint prefixes are not covered
    /// set.insert("10.1.1.0/25".parse()?); // more specific prefixes are not covered
    /// set.insert("11.0.0.0/8".parse()?);  // Branch points that don't contain values are skipped
    /// assert_eq!(set.cover(&p2).collect::<Vec<_>>(), vec![&p0, &p1, &p2]);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn cover<'a>(&'a self, prefix: &'a P) -> CoverKeys<'a, P, ()> {
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
    P: Prefix + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.iter().zip(other.iter()).all(|(a, b)| a == b)
    }
}

impl<P> Eq for PrefixSet<P> where P: Prefix + Eq {}

#[derive(Clone)]
/// An iterator over all entries of a [`PrefixSet`] in lexicographic order.
pub struct Iter<'a, P>(crate::map::Iter<'a, P, ()>);

impl<'a, P: Prefix> Iterator for Iter<'a, P> {
    type Item = &'a P;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(p, _)| p)
    }
}

#[derive(Clone)]
/// A consuming iterator over all entries of a [`PrefixSet`] in lexicographic order.
pub struct IntoIter<P>(crate::map::IntoIter<P, ()>);

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
    type Item = &'a P;

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
