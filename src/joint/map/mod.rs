//! Module that defines the JointPrefixMap

use super::JointPrefix;
use crate::PrefixMap;
#[cfg(test)]
#[cfg(feature = "ipnet")]
mod test;

use either::{Left, Right};

/// A Joint prefix map, implemented as two separate prefix trees.
#[derive(Clone)]
pub struct JointPrefixMap<P, T>
where
    P: JointPrefix,
{
    /// PrefixMap that corresponds to the first prefix type
    pub t1: PrefixMap<P::P1, T>,
    /// PrefixMap that corresponds to the second prefix type
    pub t2: PrefixMap<P::P2, T>,
}

impl<P, T> Default for JointPrefixMap<P, T>
where
    P: JointPrefix,
{
    fn default() -> Self {
        Self {
            t1: Default::default(),
            t2: Default::default(),
        }
    }
}

impl<P: JointPrefix, T> JointPrefixMap<P, T> {
    /// Create an empty prefix map
    pub fn new() -> Self {
        Self {
            t1: PrefixMap::new(),
            t2: PrefixMap::new(),
        }
    }

    /// Returns the number of elements stored in `self`.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut map: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::default();
    /// map.insert("192.168.1.0/24".parse()?, 1u32);
    /// map.insert("192.168.1.0/25".parse()?, 2u32);
    /// map.insert("2001::1:0:0/96".parse()?, 3u32);
    /// # let map = map.clone();
    /// assert_eq!(map.len(), 3);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.t1.len() + self.t2.len()
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut map: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// assert!(map.is_empty());
    /// map.insert("2001::1:0:0/96".parse()?, 1u32);
    /// assert!(!map.is_empty());
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the value of an element by matching exactly on the prefix.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// pm.insert("2001::1:0:0/96".parse()?, 2);
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&1));
    /// assert_eq!(pm.get(&"192.168.2.0/24".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.0.0/23".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.1.128/25".parse()?), None);
    /// assert_eq!(pm.get(&"2001::1:0:0/96".parse()?), Some(&2));
    /// assert_eq!(pm.get(&"0ca8:1::/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get<'a>(&'a self, prefix: &P) -> Option<&'a T> {
        fork_ref!(self, prefix, get)
    }

    /// Get a mutable reference to a value of an element by matching exactly on the prefix.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// let prefix = "2001::/32".parse()?;
    /// pm.insert(prefix, 1);
    /// assert_eq!(pm.get(&prefix), Some(&1));
    /// *pm.get_mut(&prefix).unwrap() += 1;
    /// assert_eq!(pm.get(&prefix), Some(&2));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_mut<'a>(&'a mut self, prefix: &P) -> Option<&'a mut T> {
        fork_ref!(self, prefix, get_mut)
    }

    /// Get the value of an element by matching exactly on the prefix. Notice, that the returned
    /// prefix may differ from the one provided in the host-part of the address.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// let prefix = "2001::/32".parse()?;
    /// pm.insert(prefix, 1);
    /// assert_eq!(pm.get_key_value(&prefix), Some((prefix, &1)));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_key_value<'a>(&'a self, prefix: &P) -> Option<(P, &'a T)> {
        fork_ref!(self, prefix as (P, T), get_key_value)
    }

    /// Get a value of an element by using longest prefix matching
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// assert_eq!(pm.get_lpm(&"192.168.1.1/32".parse()?), Some(("192.168.1.0/24".parse()?, &1)));
    /// assert_eq!(pm.get_lpm(&"192.168.1.0/24".parse()?), Some(("192.168.1.0/24".parse()?, &1)));
    /// assert_eq!(pm.get_lpm(&"192.168.0.0/24".parse()?), Some(("192.168.0.0/23".parse()?, &2)));
    /// assert_eq!(pm.get_lpm(&"192.168.2.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_lpm<'a>(&'a self, prefix: &P) -> Option<(P, &'a T)> {
        fork_ref!(self, prefix as (P, T), get_lpm)
    }

    /// Get a mutable reference to a value of an element by using longest prefix matching
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// assert_eq!(pm.get_lpm(&"192.168.1.1/32".parse()?), Some(("192.168.1.0/24".parse()?, &1)));
    /// *pm.get_lpm_mut(&"192.168.1.64/26".parse()?).unwrap().1 += 1;
    /// assert_eq!(pm.get_lpm(&"192.168.1.1/32".parse()?), Some(("192.168.1.0/24".parse()?, &2)));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_lpm_mut<'a>(&'a mut self, prefix: &P) -> Option<(P, &'a mut T)> {
        fork_ref!(self, prefix as (P, T), get_lpm_mut)
    }

    /// Check if a key is present in the datastructure.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// assert!(pm.contains_key(&"192.168.1.0/24".parse()?));
    /// assert!(!pm.contains_key(&"192.168.2.0/24".parse()?));
    /// assert!(!pm.contains_key(&"192.168.0.0/23".parse()?));
    /// assert!(!pm.contains_key(&"192.168.1.128/25".parse()?));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn contains_key(&self, prefix: &P) -> bool {
        fork_ref!(self, prefix, contains_key)
    }

    /// Get the longest prefix in the datastructure that matches the given `prefix`.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// assert_eq!(pm.get_lpm_prefix(&"192.168.1.1/32".parse()?), Some("192.168.1.0/24".parse()?));
    /// assert_eq!(pm.get_lpm_prefix(&"192.168.1.0/24".parse()?), Some("192.168.1.0/24".parse()?));
    /// assert_eq!(pm.get_lpm_prefix(&"192.168.0.0/24".parse()?), Some("192.168.0.0/23".parse()?));
    /// assert_eq!(pm.get_lpm_prefix(&"192.168.2.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_lpm_prefix(&self, prefix: &P) -> Option<P> {
        fork_ref!(self, prefix as P, get_lpm_prefix)
    }

    /// Get a value of an element by using shortest prefix matching.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// assert_eq!(pm.get_spm(&"192.168.1.1/32".parse()?), Some(("192.168.0.0/23".parse()?, &2)));
    /// assert_eq!(pm.get_spm(&"192.168.1.0/24".parse()?), Some(("192.168.0.0/23".parse()?, &2)));
    /// assert_eq!(pm.get_spm(&"192.168.0.0/23".parse()?), Some(("192.168.0.0/23".parse()?, &2)));
    /// assert_eq!(pm.get_spm(&"192.168.2.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    pub fn get_spm<'a>(&'a self, prefix: &P) -> Option<(P, &'a T)> {
        fork_ref!(self, prefix as (P, T), get_spm)
    }

    /// Get the shortest prefix in the datastructure that contains the given `prefix`.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// pm.insert("192.168.1.1/24".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// assert_eq!(pm.get_spm_prefix(&"192.168.1.1/32".parse()?), Some("192.168.0.0/23".parse()?));
    /// assert_eq!(pm.get_spm_prefix(&"192.168.1.0/24".parse()?), Some("192.168.0.0/23".parse()?));
    /// assert_eq!(pm.get_spm_prefix(&"192.168.0.0/23".parse()?), Some("192.168.0.0/23".parse()?));
    /// assert_eq!(pm.get_spm_prefix(&"192.168.2.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    pub fn get_spm_prefix(&self, prefix: &P) -> Option<P> {
        fork_ref!(self, prefix as P, get_spm_prefix)
    }

    /// Insert a new item into the prefix-map. This function may return any value that existed
    /// before.
    ///
    /// In case the node already exists in the tree, its prefix will be replaced by the provided
    /// argument. This allows you to store additional information in the host part of the prefix.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// assert_eq!(pm.insert("192.168.0.0/23".parse()?, 1), None);
    /// assert_eq!(pm.insert("192.168.1.0/24".parse()?, 2), None);
    /// assert_eq!(pm.insert("192.168.1.0/24".parse()?, 3), Some(2));
    /// assert_eq!(pm.insert("2001::1:0:0/96".parse()?, 4), None);
    /// assert_eq!(pm.insert("2001::1:0:0/97".parse()?, 5), None);
    /// assert_eq!(pm.insert("2001::1:0:0/97".parse()?, 6), Some(5));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn insert(&mut self, prefix: P, value: T) -> Option<T> {
        fork!(self, prefix, insert, value)
    }

    /// Gets the given key’s corresponding entry in the map for in-place manipulation. In case you
    /// eventually insert an element into the map, this operation will also replace the prefix in
    /// the node with the existing one. That is if you store additional information in the host part
    /// of the address (the one that is masked out).
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, vec![1]);
    /// pm.entry("192.168.1.0/24".parse()?).or_default().push(2);
    /// pm.entry("192.168.1.0/25".parse()?).or_default().push(3);
    /// pm.entry("c0a8:1::/24".parse()?).or_default().push(4);
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&vec![1, 2]));
    /// assert_eq!(pm.get(&"192.168.1.0/25".parse()?), Some(&vec![3]));
    /// assert_eq!(pm.get(&"c0a8:1::/24".parse()?), Some(&vec![4]));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn entry(&mut self, prefix: P) -> Entry<'_, P, T> {
        match prefix.p1_or_p2() {
            Left(p1) => match self.t1.entry(p1) {
                crate::map::Entry::Vacant(e) => Entry::Vacant(VacantEntry::P1(e)),
                crate::map::Entry::Occupied(e) => Entry::Occupied(OccupiedEntry::P1(e)),
            },
            Right(p2) => match self.t2.entry(p2) {
                crate::map::Entry::Vacant(e) => Entry::Vacant(VacantEntry::P2(e)),
                crate::map::Entry::Occupied(e) => Entry::Occupied(OccupiedEntry::P2(e)),
            },
        }
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the
    /// map. In contrast to [`Self::remove_keep_tree`], this operation will modify the tree
    /// structure. As a result, this operation takes longer than `remove_keep_tree`, as does
    /// inserting the same element again. However, future reads may be faster as less nodes need to
    /// be traversed. Further, it reduces the memory footprint to its minimum.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// let prefix = "192.168.1.0/24".parse()?;
    /// pm.insert(prefix, 1);
    /// assert_eq!(pm.get(&prefix), Some(&1));
    /// assert_eq!(pm.remove(&prefix), Some(1));
    /// assert_eq!(pm.get(&prefix), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn remove(&mut self, prefix: &P) -> Option<T> {
        fork_ref!(self, prefix, remove)
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the
    /// map. In contrast to [`Self::remove`], his operation will keep the tree structure as is, but
    /// only remove the element from it. This allows any future `insert` on the same prefix to be
    /// faster. However future reads from the tree might be a bit slower because they need to
    /// traverse more nodes.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// let prefix = "192.168.1.0/24".parse()?;
    /// pm.insert(prefix, 1);
    /// assert_eq!(pm.get(&prefix), Some(&1));
    /// assert_eq!(pm.remove_keep_tree(&prefix), Some(1));
    /// assert_eq!(pm.get(&prefix), None);
    ///
    /// // future inserts of the same key are now faster!
    /// pm.insert(prefix, 1);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn remove_keep_tree(&mut self, prefix: &P) -> Option<T> {
        fork_ref!(self, prefix, remove_keep_tree)
    }

    /// Remove all entries that are contained within `prefix`. This will change the tree
    /// structure. This operation is `O(n)`, as the entries must be freed up one-by-one.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// pm.insert("192.168.0.0/22".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// pm.insert("192.168.0.0/24".parse()?, 3);
    /// pm.insert("192.168.2.0/23".parse()?, 4);
    /// pm.insert("192.168.2.0/24".parse()?, 5);
    /// pm.remove_children(&"192.168.0.0/23".parse()?);
    /// assert_eq!(pm.get(&"192.168.0.0/23".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.0.0/24".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.2.0/23".parse()?), Some(&4));
    /// assert_eq!(pm.get(&"192.168.2.0/24".parse()?), Some(&5));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn remove_children(&mut self, prefix: &P) {
        fork_ref!(self, prefix, remove_children)
    }

    /// Clear the map but keep the allocated memory.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// pm.insert("192.168.0.0/24".parse()?, 1);
    /// pm.insert("192.168.1.0/24".parse()?, 2);
    /// pm.insert("2001::1:0:0/96".parse()?, 3);
    /// pm.clear();
    /// assert_eq!(pm.get(&"192.168.0.0/24".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), None);
    /// assert_eq!(pm.get(&"2001::1:0:0/96".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn clear(&mut self) {
        self.t1.clear();
        self.t2.clear();
    }

    /// Keep only the elements in the map that satisfy the given condition `f`.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// pm.insert("192.168.0.0/24".parse()?, 1);
    /// pm.insert("192.168.1.0/24".parse()?, 2);
    /// pm.insert("192.168.2.0/24".parse()?, 3);
    /// pm.insert("192.168.2.0/25".parse()?, 4);
    /// pm.insert("2001::1:0:0/24".parse()?, 5);
    /// pm.insert("2001::1:0:0/25".parse()?, 6);
    /// pm.retain(|_, t| *t % 2 == 0); // only keep the even values.
    /// assert_eq!(pm.get(&"192.168.0.0/24".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&2));
    /// assert_eq!(pm.get(&"192.168.2.0/24".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.2.0/25".parse()?), Some(&4));
    /// assert_eq!(pm.get(&"2001::1:0:0/24".parse()?), None);
    /// assert_eq!(pm.get(&"2001::1:0:0/25".parse()?), Some(&6));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(P, &T) -> bool,
    {
        self.t1.retain(|p, t| f(P::from_p1(p), t));
        self.t2.retain(|p, t| f(P::from_p2(p), t));
    }

    /// Iterate over all entries in the map that covers the given `prefix` (including `prefix`
    /// itself if that is present in the map). The returned iterator yields `(&'a P, &'a T)`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// let p0 = "10.0.0.0/8".parse()?;
    /// let p1 = "10.1.0.0/16".parse()?;
    /// let p2 = "10.1.1.0/24".parse()?;
    /// pm.insert(p0, 0);
    /// pm.insert(p1, 1);
    /// pm.insert(p2, 2);
    /// pm.insert("10.1.2.0/24".parse()?, 3); // disjoint prefixes are not covered
    /// pm.insert("10.1.1.0/25".parse()?, 4); // more specific prefixes are not covered
    /// pm.insert("11.0.0.0/8".parse()?, 5);  // Branch points that don't contain values are skipped
    /// assert_eq!(
    ///     pm.cover(&p2).collect::<Vec<_>>(),
    ///     vec![(p0, &0), (p1, &1), (p2, &2)]
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    ///
    /// This function also yields the root note *if* it is part of the map:
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// let root = "0.0.0.0/0".parse()?;
    /// pm.insert(root, 0);
    /// assert_eq!(pm.cover(&"10.0.0.0/8".parse()?).collect::<Vec<_>>(), vec![(root, &0)]);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn cover<'a, 'p>(&'a self, prefix: &'p P) -> Cover<'a, 'p, P, T> {
        match prefix.p1_or_p2_ref() {
            Left(p1) => Cover::P1(self.t1.cover(p1)),
            Right(p2) => Cover::P2(self.t2.cover(p2)),
        }
    }

    /// Iterate over all keys (prefixes) in the map that covers the given `prefix` (including
    /// `prefix` itself if that is present in the map). The returned iterator yields `&'a P`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// let p0 = "10.0.0.0/8".parse()?;
    /// let p1 = "10.1.0.0/16".parse()?;
    /// let p2 = "10.1.1.0/24".parse()?;
    /// pm.insert(p0, 0);
    /// pm.insert(p1, 1);
    /// pm.insert(p2, 2);
    /// pm.insert("10.1.2.0/24".parse()?, 3); // disjoint prefixes are not covered
    /// pm.insert("10.1.1.0/25".parse()?, 4); // more specific prefixes are not covered
    /// pm.insert("11.0.0.0/8".parse()?, 5);  // Branch points that don't contain values are skipped
    /// assert_eq!(pm.cover_keys(&p2).collect::<Vec<_>>(), vec![p0, p1, p2]);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn cover_keys<'a, 'p>(&'a self, prefix: &'p P) -> CoverKeys<'a, 'p, P, T> {
        CoverKeys(self.cover(prefix))
    }

    /// Iterate over all values in the map that covers the given `prefix` (including `prefix`
    /// itself if that is present in the map). The returned iterator yields `&'a T`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// let p0 = "10.0.0.0/8".parse()?;
    /// let p1 = "10.1.0.0/16".parse()?;
    /// let p2 = "10.1.1.0/24".parse()?;
    /// pm.insert(p0, 0);
    /// pm.insert(p1, 1);
    /// pm.insert(p2, 2);
    /// pm.insert("10.1.2.0/24".parse()?, 3); // disjoint prefixes are not covered
    /// pm.insert("10.1.1.0/25".parse()?, 4); // more specific prefixes are not covered
    /// pm.insert("11.0.0.0/8".parse()?, 5);  // Branch points that don't contain values are skipped
    /// assert_eq!(pm.cover_values(&p2).collect::<Vec<_>>(), vec![&0, &1, &2]);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn cover_values<'a, 'p>(&'a self, prefix: &'p P) -> CoverValues<'a, 'p, P, T> {
        CoverValues(self.cover(prefix))
    }
}

impl<P, L, R> PartialEq<JointPrefixMap<P, R>> for JointPrefixMap<P, L>
where
    P: JointPrefix + PartialEq,
    L: PartialEq<R>,
{
    fn eq(&self, other: &JointPrefixMap<P, R>) -> bool {
        self.iter()
            .zip(other.iter())
            .all(|((lp, lt), (rp, rt))| lt == rt && lp == rp)
    }
}

impl<P, T> Eq for JointPrefixMap<P, T>
where
    P: JointPrefix + Eq,
    T: Eq,
{
}

mod entry;
mod iter;

pub use entry::*;
pub use iter::*;
