//! Implementation of the Prefix Map.

use crate::{to_right, Prefix};

mod entry;
mod iter;

pub use entry::*;
pub use iter::*;

/// Prefix map implemented as a prefix tree.
#[derive(Clone)]
pub struct PrefixMap<P, T> {
    pub(crate) table: Vec<Node<P, T>>,
    free: Vec<usize>,
    count: usize,
}

impl<P, T> Default for PrefixMap<P, T>
where
    P: Prefix,
{
    fn default() -> Self {
        Self {
            table: vec![Node {
                prefix: P::zero(),
                value: None,
                left: None,
                right: None,
            }],
            free: Vec::new(),
            count: 0,
        }
    }
}

impl<P, T> PrefixMap<P, T>
where
    P: Prefix,
{
    /// Create an empty prefix map.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the number of elements stored in `self`.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.count
    }

    /// Returns `true` if the map contains no elements.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Get the value of an element by matching exactly on the prefix.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&1));
    /// assert_eq!(pm.get(&"192.168.2.0/24".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.0.0/23".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.1.128/25".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get(&self, prefix: &P) -> Option<&T> {
        let mut idx = 0;
        loop {
            match self.get_direction(idx, prefix) {
                Direction::Reached => return self.table[idx].value.as_ref(),
                Direction::Enter { next, .. } => idx = next,
                Direction::Missing => return None,
            }
        }
    }

    /// Get a mutable reference to a value of an element by matching exactly on the prefix.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// let prefix = "192.168.1.0/24".parse()?;
    /// pm.insert(prefix, 1);
    /// assert_eq!(pm.get(&prefix), Some(&1));
    /// *pm.get_mut(&prefix).unwrap() += 1;
    /// assert_eq!(pm.get(&prefix), Some(&2));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_mut(&mut self, prefix: &P) -> Option<&mut T> {
        let mut idx = 0;
        loop {
            match self.get_direction(idx, prefix) {
                Direction::Reached => return self.table[idx].value.as_mut(),
                Direction::Enter { next, .. } => idx = next,
                Direction::Missing => return None,
            }
        }
    }

    /// Get the value of an element by matching exactly on the prefix.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// let prefix = "192.168.1.0/24".parse()?;
    /// pm.insert(prefix, 1);
    /// assert_eq!(pm.get_key_value(&prefix), Some((&prefix, &1)));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_key_value(&self, prefix: &P) -> Option<(&P, &T)> {
        let mut idx = 0;
        loop {
            match self.get_direction(idx, prefix) {
                Direction::Reached => return self.table[idx].prefix_value(),
                Direction::Enter { next, .. } => idx = next,
                Direction::Missing => return None,
            }
        }
    }

    /// Get a value of an element by using longest prefix matching
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// assert_eq!(pm.get_lpm(&"192.168.1.1/32".parse()?), Some((&"192.168.1.0/24".parse()?, &1)));
    /// assert_eq!(pm.get_lpm(&"192.168.1.0/24".parse()?), Some((&"192.168.1.0/24".parse()?, &1)));
    /// assert_eq!(pm.get_lpm(&"192.168.0.0/24".parse()?), Some((&"192.168.0.0/23".parse()?, &2)));
    /// assert_eq!(pm.get_lpm(&"192.168.2.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_lpm<'a>(&'a self, prefix: &P) -> Option<(&'a P, &'a T)> {
        let mut idx = 0;
        let mut best_match: Option<(&P, &T)> = None;
        loop {
            best_match = self.table[idx].prefix_value().or(best_match);
            match self.get_direction(idx, prefix) {
                Direction::Enter { next, .. } => idx = next,
                _ => return best_match,
            }
        }
    }

    /// Get a mutable reference to a value of an element by using longest prefix matching
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// assert_eq!(pm.get_lpm(&"192.168.1.1/32".parse()?), Some((&"192.168.1.0/24".parse()?, &1)));
    /// *pm.get_lpm_mut(&"192.168.1.64/26".parse()?).unwrap().1 += 1;
    /// assert_eq!(pm.get_lpm(&"192.168.1.1/32".parse()?), Some((&"192.168.1.0/24".parse()?, &2)));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_lpm_mut(&mut self, prefix: &P) -> Option<(&P, &mut T)> {
        let mut idx = 0;
        let mut best_match: Option<usize> = None;
        loop {
            best_match = if self.table[idx].value.is_some() {
                Some(idx)
            } else {
                best_match
            };
            match self.get_direction(idx, prefix) {
                Direction::Enter { next, .. } => idx = next,
                _ => break,
            }
        }
        if let Some(idx) = best_match {
            self.table.get_mut(idx).unwrap().prefix_value_mut()
        } else {
            None
        }
    }

    /// Check if a key is present in the datastructure.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
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
        let mut idx = 0;
        loop {
            match self.get_direction(idx, prefix) {
                Direction::Reached => return self.table[idx].value.is_some(),
                Direction::Enter { next, .. } => idx = next,
                Direction::Missing => return false,
            }
        }
    }

    /// Get the longest prefix in the datastructure that matches the given `prefix`.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// assert_eq!(pm.get_lpm_prefix(&"192.168.1.1/32".parse()?), Some(&"192.168.1.0/24".parse()?));
    /// assert_eq!(pm.get_lpm_prefix(&"192.168.1.0/24".parse()?), Some(&"192.168.1.0/24".parse()?));
    /// assert_eq!(pm.get_lpm_prefix(&"192.168.0.0/24".parse()?), Some(&"192.168.0.0/23".parse()?));
    /// assert_eq!(pm.get_lpm_prefix(&"192.168.2.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_lpm_prefix(&self, prefix: &P) -> Option<&P> {
        let mut idx = 0;
        let mut best_match: Option<&P> = None;
        loop {
            best_match = self.table[idx]
                .prefix_value()
                .map(|(p, _)| p)
                .or(best_match);
            match self.get_direction(idx, prefix) {
                Direction::Enter { next, .. } => idx = next,
                _ => return best_match,
            }
        }
    }

    /// Get a value of an element by using shortest prefix matching.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// assert_eq!(pm.get_spm(&"192.168.1.1/32".parse()?), Some((&"192.168.0.0/23".parse()?, &2)));
    /// assert_eq!(pm.get_spm(&"192.168.1.0/24".parse()?), Some((&"192.168.0.0/23".parse()?, &2)));
    /// assert_eq!(pm.get_spm(&"192.168.0.0/23".parse()?), Some((&"192.168.0.0/23".parse()?, &2)));
    /// assert_eq!(pm.get_spm(&"192.168.2.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    pub fn get_spm<'a>(&'a self, prefix: &P) -> Option<(&'a P, &'a T)> {
        // Handle the special case, where the root is populated
        if let Some(x) = self.table[0].prefix_value() {
            return Some(x);
        }
        let mut idx = 0;
        loop {
            match self.get_direction(idx, prefix) {
                Direction::Reached => return self.table[idx].prefix_value(),
                Direction::Enter { next, .. } => {
                    // Go until the first node with a value
                    match self.table[next].prefix_value() {
                        Some(x) => return Some(x),
                        None => idx = next,
                    }
                }
                Direction::Missing => return None,
            }
        }
    }

    /// Get the shortest prefix in the datastructure that contains the given `prefix`.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.1/24".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// assert_eq!(pm.get_spm_prefix(&"192.168.1.1/32".parse()?), Some(&"192.168.0.0/23".parse()?));
    /// assert_eq!(pm.get_spm_prefix(&"192.168.1.0/24".parse()?), Some(&"192.168.0.0/23".parse()?));
    /// assert_eq!(pm.get_spm_prefix(&"192.168.0.0/23".parse()?), Some(&"192.168.0.0/23".parse()?));
    /// assert_eq!(pm.get_spm_prefix(&"192.168.2.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    pub fn get_spm_prefix(&self, prefix: &P) -> Option<&P> {
        self.get_spm(prefix).map(|(p, _)| p)
    }

    /// Insert a new item into the prefix-map. This function may return any value that existed
    /// before.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// assert_eq!(pm.insert("192.168.0.0/23".parse()?, 1), None);
    /// assert_eq!(pm.insert("192.168.1.0/24".parse()?, 2), None);
    /// assert_eq!(pm.insert("192.168.1.0/24".parse()?, 3), Some(2));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn insert(&mut self, prefix: P, value: T) -> Option<T> {
        let mut idx = 0;
        loop {
            match self.get_direction_for_insert(idx, &prefix) {
                DirectionForInsert::Enter { next, .. } => idx = next,
                DirectionForInsert::Reached => {
                    let old_value = self.table[idx].value.take();
                    if old_value.is_none() {
                        self.count += 1;
                    }
                    self.table[idx].value = Some(value);
                    return old_value;
                }
                DirectionForInsert::NewLeaf { right } => {
                    let new = self.new_node(prefix, Some(value));
                    self.set_child(idx, new, right);
                    return None;
                }
                DirectionForInsert::NewChild { right, child_right } => {
                    let new = self.new_node(prefix, Some(value));
                    let child = self.set_child(idx, new, right).unwrap();
                    self.set_child(new, child, child_right);
                    return None;
                }
                DirectionForInsert::NewBranch {
                    branch_prefix,
                    right,
                    prefix_right,
                } => {
                    let branch = self.new_node(branch_prefix, None);
                    let new = self.new_node(prefix, Some(value));
                    let child = self.set_child(idx, branch, right).unwrap();
                    self.set_child(branch, new, prefix_right);
                    self.set_child(branch, child, !prefix_right);
                    return None;
                }
            }
        }
    }

    /// Gets the given key’s corresponding entry in the map for in-place manipulation.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.0.0/23".parse()?, vec![1]);
    /// pm.entry("192.168.0.0/23".parse()?).or_default().push(2);
    /// pm.entry("192.168.0.0/24".parse()?).or_default().push(3);
    /// assert_eq!(pm.get(&"192.168.0.0/23".parse()?), Some(&vec![1, 2]));
    /// assert_eq!(pm.get(&"192.168.0.0/24".parse()?), Some(&vec![3]));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn entry(&mut self, prefix: P) -> Entry<'_, P, T> {
        let mut idx = 0;
        loop {
            match self.get_direction_for_insert(idx, &prefix) {
                DirectionForInsert::Enter { next, .. } => idx = next,
                DirectionForInsert::Reached if self.table[idx].value.is_some() => {
                    return Entry::Occupied(OccupiedEntry {
                        node: &mut self.table[idx],
                    })
                }
                direction => {
                    return Entry::Vacant(VacantEntry {
                        map: self,
                        prefix,
                        idx,
                        direction,
                    })
                }
            }
        }
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the
    /// map. In contrast to [`Self::remove_keep_tree`], this operation will modify the tree
    /// structure. As a result, this operation takes longer than `remove_keep_tree`, as does
    /// inserting the same element again. However, future reads may be faster as less nodes need to
    /// be traversed. Further, it reduces the memory footprint to its minimum.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
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
        let mut idx = 0;
        let mut grandparent = None;
        let mut grandparent_right = false;
        let mut parent = None;
        let mut parent_right = false;
        // first, search for the element
        loop {
            match self.get_direction(idx, prefix) {
                Direction::Reached => break,
                Direction::Enter { next, right } => {
                    grandparent_right = parent_right;
                    parent_right = right;
                    grandparent = parent;
                    parent = Some(idx);
                    idx = next;
                }
                Direction::Missing => return None,
            }
        }
        self._remove_node(idx, parent, parent_right, grandparent, grandparent_right)
            .0
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the
    /// map. In contrast to [`Self::remove`], his operation will keep the tree structure as is, but
    /// only remove the element from it. This allows any future `insert` on the same prefix to be
    /// faster. However future reads from the tree might be a bit slower because they need to
    /// traverse more nodes.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
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
        let mut idx = 0;
        let value = loop {
            match self.get_direction(idx, prefix) {
                Direction::Reached => break self.table[idx].value.take(),
                Direction::Enter { next, .. } => idx = next,
                Direction::Missing => break None,
            }
        };

        // decrease the count if the value is something
        if value.is_some() {
            self.count -= 1;
        }

        value
    }

    /// Remove all entries that are contained within `prefix`. This will change the tree
    /// structure. This operation is `O(n)`, as the entries must be freed up one-by-one.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
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
        if prefix.prefix_len() == 0 {
            return self.clear();
        }
        let mut parent_right = false;
        let mut parent = 0;
        let mut idx = 0;
        loop {
            match self.get_direction_for_insert(idx, prefix) {
                DirectionForInsert::Reached => {
                    return self._do_remove_children(parent, parent_right)
                }
                DirectionForInsert::Enter { next, right } => {
                    parent_right = right;
                    parent = idx;
                    idx = next
                }
                DirectionForInsert::NewLeaf { .. } | DirectionForInsert::NewBranch { .. } => return,
                DirectionForInsert::NewChild { right, .. } => {
                    return self._do_remove_children(idx, right)
                }
            }
        }
    }

    /// Clear the map but keep the allocated memory.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.0.0/24".parse()?, 1);
    /// pm.insert("192.168.1.0/24".parse()?, 2);
    /// pm.clear();
    /// assert_eq!(pm.get(&"192.168.0.0/24".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn clear(&mut self) {
        self.table.clear();
        self.free.clear();
        self.table.push(Node {
            prefix: P::zero(),
            value: None,
            left: None,
            right: None,
        });
        self.count = 0;
    }

    /// Keep only the elements in the map that satisfy the given condition `f`.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.0.0/24".parse()?, 1);
    /// pm.insert("192.168.1.0/24".parse()?, 2);
    /// pm.insert("192.168.2.0/24".parse()?, 3);
    /// pm.insert("192.168.2.0/25".parse()?, 4);
    /// pm.retain(|_, t| *t % 2 == 0);
    /// assert_eq!(pm.get(&"192.168.0.0/24".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&2));
    /// assert_eq!(pm.get(&"192.168.2.0/24".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.2.0/25".parse()?), Some(&4));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&P, &T) -> bool,
    {
        self._retain(0, None, false, None, false, f);
    }

    /// Iterate over all entries in the map that covers the given `prefix` (including `prefix`
    /// itself if that is present in the map). The returned iterator yields `(&'a P, &'a T)`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
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
    ///     vec![(&p0, &0), (&p1, &1), (&p2, &2)]
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
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// let root = "0.0.0.0/0".parse()?;
    /// pm.insert(root, 0);
    /// assert_eq!(pm.cover(&"10.0.0.0/8".parse()?).collect::<Vec<_>>(), vec![(&root, &0)]);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn cover<'a>(&'a self, prefix: &'a P) -> Cover<'a, P, T> {
        Cover {
            map: self,
            idx: None,
            prefix,
        }
    }

    /// Iterate over all keys (prefixes) in the map that covers the given `prefix` (including
    /// `prefix` itself if that is present in the map). The returned iterator yields `&'a P`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// let p0 = "10.0.0.0/8".parse()?;
    /// let p1 = "10.1.0.0/16".parse()?;
    /// let p2 = "10.1.1.0/24".parse()?;
    /// pm.insert(p0, 0);
    /// pm.insert(p1, 1);
    /// pm.insert(p2, 2);
    /// pm.insert("10.1.2.0/24".parse()?, 3); // disjoint prefixes are not covered
    /// pm.insert("10.1.1.0/25".parse()?, 4); // more specific prefixes are not covered
    /// pm.insert("11.0.0.0/8".parse()?, 5);  // Branch points that don't contain values are skipped
    /// assert_eq!(pm.cover_keys(&p2).collect::<Vec<_>>(), vec![&p0, &p1, &p2]);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn cover_keys<'a>(&'a self, prefix: &'a P) -> CoverKeys<'a, P, T> {
        CoverKeys(Cover {
            map: self,
            idx: None,
            prefix,
        })
    }

    /// Iterate over all values in the map that covers the given `prefix` (including `prefix`
    /// itself if that is present in the map). The returned iterator yields `&'a T`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
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
    pub fn cover_values<'a>(&'a self, prefix: &'a P) -> CoverValues<'a, P, T> {
        CoverValues(Cover {
            map: self,
            idx: None,
            prefix,
        })
    }
}

/// Private function implementations
impl<P, T> PrefixMap<P, T>
where
    P: Prefix,
{
    /// remove all elements from that point onwards.
    fn _do_remove_children(&mut self, idx: usize, right: bool) {
        let mut to_free = vec![self.get_child(idx, right).unwrap()];
        self.clear_child(idx, right);
        while let Some(idx) = to_free.pop() {
            let node = &mut self.table[idx];
            let value = node.value.take();
            // decrease the count if `value` is something
            if value.is_some() {
                self.count -= 1;
            }
            if let Some(left) = node.left.take() {
                to_free.push(left)
            }
            if let Some(right) = node.right.take() {
                to_free.push(right)
            }
            self.free.push(idx);
        }
    }

    /// Get the child of a node, either to the left or the right
    #[inline(always)]
    fn get_child(&self, idx: usize, right: bool) -> Option<usize> {
        if right {
            self.table[idx].right
        } else {
            self.table[idx].left
        }
    }

    /// set the child of a node (either to the left or the right), and return the index of the old child.
    #[inline(always)]
    fn set_child(&mut self, idx: usize, child: usize, right: bool) -> Option<usize> {
        if right {
            self.table[idx].right.replace(child)
        } else {
            self.table[idx].left.replace(child)
        }
    }

    /// remove a child from a node (just the reference).
    #[inline(always)]
    fn clear_child(&mut self, idx: usize, right: bool) -> Option<usize> {
        if right {
            self.table[idx].right.take()
        } else {
            self.table[idx].left.take()
        }
    }

    /// insert a new node into the table and return its index. This function also increments the
    /// count by 1, but only if `value` is `Some`.
    #[inline(always)]
    fn new_node(&mut self, prefix: P, value: Option<T>) -> usize {
        if value.is_some() {
            self.count += 1;
        }
        if let Some(idx) = self.free.pop() {
            let node = &mut self.table[idx];
            node.prefix = prefix;
            node.value = value;
            node.left = None;
            node.right = None;
            idx
        } else {
            let idx = self.table.len();
            self.table.push(Node {
                prefix,
                value,
                left: None,
                right: None,
            });
            idx
        }
    }

    /// Remove a child from the tree. If the parent was removed, return `true` as a second return parameter
    fn _remove_node(
        &mut self,
        idx: usize,
        par: Option<usize>,
        par_right: bool,
        grp: Option<usize>,
        grp_right: bool,
    ) -> (Option<T>, bool) {
        // if we reach this point, then `idx` is the element to remove, `parent` is its parent,
        // and `parent_right` stores the direction of `idx` at `parent`.
        let node = &mut self.table[idx];
        let value = node.value.take();
        let has_left = node.left.is_some();
        let has_right = node.right.is_some();

        // decrease the number of elements if value is something
        if value.is_some() {
            self.count -= 1;
        }

        if has_left && has_right {
            // if the node has both left and right set, then it must remain in the tree.
        } else if !(has_left || has_right) {
            if let Some(par) = par {
                // if the node is a leaf, simply remove it.
                self.clear_child(par, par_right);
                self.free.push(idx);
                // now, if the parent has no value, also remove the parent and replace it with the
                // current node. but only do that if the grandparent is something.
                if let Some(grp) = grp {
                    if self.table[par].value.is_none() {
                        if let Some(sibling) = self.get_child(par, !par_right) {
                            self.set_child(grp, sibling, grp_right);
                            return (value, true);
                        } else {
                            self.clear_child(grp, grp_right);
                        }
                    }
                }
            }
        } else {
            // one child remains. simply connect that child directly to the parent if the parent is Something.
            if let Some(par) = par {
                let child_right = has_right;
                let child = self.clear_child(idx, child_right).unwrap();
                self.set_child(par, child, par_right);
                self.free.push(idx);
            }
        }
        (value, false)
    }

    /// recursive retain implementation
    pub(crate) fn _retain<F>(
        &mut self,
        idx: usize,
        par: Option<usize>,
        par_right: bool,
        grp: Option<usize>,
        grp_right: bool,
        mut f: F,
    ) -> (F, bool)
    where
        F: FnMut(&P, &T) -> bool,
    {
        // first, do the recursion
        let mut idx_removed = false;
        let mut par_removed = false;
        if let Some(left) = self.table[idx].left {
            (f, idx_removed) = self._retain(left, Some(idx), false, par, par_right, f);
        }
        if let Some(right) = self.table[idx].right {
            if idx_removed {
                (f, par_removed) = self._retain(right, par, par_right, grp, grp_right, f);
            } else {
                (f, _) = self._retain(right, Some(idx), true, par, par_right, f);
            }
        }
        // then, check if we need to delete the node
        if let Some(val) = self.table[idx].value.as_ref() {
            if !f(&self.table[idx].prefix, val) {
                // deletion is necessary.
                let (_, par_del) = self._remove_node(idx, par, par_right, grp, grp_right);
                par_removed = par_del;
            }
        }
        (f, par_removed)
    }

    /// Get the directions from some node `idx` to get to `prefix`.
    #[inline(always)]
    fn get_direction(&self, cur: usize, prefix: &P) -> Direction {
        let cur_p = &self.table[cur].prefix;
        if cur_p.eq(prefix) {
            Direction::Reached
        } else {
            let right = to_right(cur_p, prefix);
            match self.get_child(cur, right) {
                Some(child) if self.table[child].prefix.contains(prefix) => {
                    Direction::Enter { next: child, right }
                }
                _ => Direction::Missing,
            }
        }
    }

    /// Get the directions from some node `idx` to get to `prefix`.
    #[inline(always)]
    fn get_direction_for_insert(&self, cur: usize, prefix: &P) -> DirectionForInsert<P> {
        let cur_p = &self.table[cur].prefix;
        if cur_p.eq(prefix) {
            DirectionForInsert::Reached
        } else {
            let right = to_right(cur_p, prefix);
            if let Some(child) = self.get_child(cur, right) {
                let child_p = &self.table[child].prefix;
                if child_p.contains(prefix) {
                    DirectionForInsert::Enter { next: child, right }
                } else if prefix.contains(child_p) {
                    DirectionForInsert::NewChild {
                        right,
                        child_right: to_right(prefix, child_p),
                    }
                } else {
                    let branch_prefix = prefix.longest_common_prefix(child_p);
                    let prefix_right = to_right(&branch_prefix, prefix);
                    DirectionForInsert::NewBranch {
                        branch_prefix,
                        right,
                        prefix_right,
                    }
                }
            } else {
                DirectionForInsert::NewLeaf { right }
            }
        }
    }
}

impl<P, T> PartialEq for PrefixMap<P, T>
where
    P: Prefix + PartialEq,
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.iter().zip(other.iter()).all(|(a, b)| a == b)
    }
}

impl<P, T> Eq for PrefixMap<P, T>
where
    P: Prefix + Eq,
    T: Eq,
{
}

/// Node kind that can either be a leaf, a node, or a forward node that summarizes multiple branches.
#[derive(Clone)]
pub(crate) struct Node<P, T> {
    pub(crate) prefix: P,
    pub(crate) value: Option<T>,
    pub(crate) left: Option<usize>,
    pub(crate) right: Option<usize>,
}

impl<P, T> Node<P, T> {
    /// get the tuple of prefix and value.
    fn prefix_value(&self) -> Option<(&P, &T)> {
        self.value.as_ref().map(|v| (&self.prefix, v))
    }

    /// get the tuple of prefix and value.
    fn prefix_value_mut(&mut self) -> Option<(&P, &mut T)> {
        self.value.as_mut().map(|v| (&self.prefix, v))
    }
}

enum Direction {
    /// The prefix is already reached.
    Reached,
    /// Enter the next index and search again.
    Enter { next: usize, right: bool },
    /// The node was not found,
    Missing,
}

enum DirectionForInsert<P> {
    /// The prefix is already reached.
    Reached,
    /// Enter the next index and search again.
    Enter { next: usize, right: bool },
    /// Insert a new child at the given position as a leaf.
    NewLeaf { right: bool },
    /// Insert a new child at the given position, moving all old children to be a child of the new
    /// prefix. `parent_right` tells where to insert the new node, while `child_right` tells where
    /// to insert the old child (on the right or the left of the new node).
    NewChild { right: bool, child_right: bool },
    /// Insert a new branch at the parent with the given prefix. `parent_right` tells where to
    /// insert the branch, while `prefix_right` tells where to insert the new node at the
    /// branch. The old child of the parent should be inserted at `!prefix_right` of the branch.
    NewBranch {
        branch_prefix: P,
        right: bool,
        prefix_right: bool,
    },
}
