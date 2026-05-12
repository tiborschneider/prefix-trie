//! This module contains the implementation for the Dense Prefix Map.

use std::marker::PhantomData;

use crate::{allocator::Loc, Prefix};

mod entry;
mod iter;
pub use entry::{Entry, OccupiedEntry, VacantEntry};
pub use iter::*;

use super::table::{ElementLoc, Location, Table, K};

/// Prefix map implemented as a TreeBitMap.
#[derive(Clone)]
pub struct PrefixMap<P, T> {
    table: Table<T>,
    count: usize,
    marker: PhantomData<P>,
}

impl<P: Prefix + PartialEq, T: PartialEq> PartialEq for PrefixMap<P, T> {
    fn eq(&self, other: &Self) -> bool {
        self.count == other.count && self.iter().eq(other.iter())
    }
}

impl<P, T> Default for PrefixMap<P, T> {
    fn default() -> Self {
        Self {
            table: Table::default(),
            count: 0,
            marker: PhantomData,
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

    /// Returns the amount of memory used by this datastructure in bytes.
    ///
    /// **Warning**: This number does not include any heap allocations of T!
    pub fn mem_size(&self) -> usize {
        self.table.mem_size() + std::mem::size_of::<Self>()
    }

    /// Return a reference to the underlying table (crate-internal use only).
    #[inline(always)]
    pub(crate) fn table(&self) -> &Table<T> {
        &self.table
    }

    /// Return a reference to the underlying table (crate-internal use only).
    #[inline(always)]
    pub(crate) fn table_mut(&mut self) -> &mut Table<T> {
        &mut self.table
    }

    /// Get the value of an element by matching exactly on the prefix.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
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
    pub fn get<'a>(&'a self, prefix: &P) -> Option<&'a T> {
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        let element = self.table.find_element(key, prefix_len).present()?;
        Some(self.table.get_data(element))
    }

    /// Get a mutable reference to a value of an element by matching exactly on the prefix.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// let prefix = "192.168.1.0/24".parse()?;
    /// pm.insert(prefix, 1);
    /// assert_eq!(pm.get_mut(&prefix), Some(&mut 1));
    /// *pm.get_mut(&prefix).unwrap() += 1;
    /// assert_eq!(pm.get_mut(&prefix), Some(&mut 2));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_mut<'a>(&'a mut self, prefix: &P) -> Option<&'a mut T> {
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        let element = self.table.find_element(key, prefix_len).present()?;
        Some(self.table.get_data_mut(element))
    }

    /// Get the value of an element by matching exactly on the prefix.
    ///
    /// Prefixes are not stored verbatim. They are reconstructed from the trie position, so host
    /// bits masked out by the prefix length are not preserved.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// let prefix = "192.168.1.0/24".parse()?;
    /// pm.insert(prefix, 1);
    /// assert_eq!(pm.get_key_value(&prefix), Some((prefix, &1)));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    ///
    /// **Warning** The table does not store the prefix, but it is reconstructed. This means, that
    /// any bits in the host part will be truncated:
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// let prefix = "192.168.1.0/24".parse()?;
    /// pm.insert(prefix, 1);
    /// assert_eq!(pm.get_key_value(&prefix), Some((prefix.trunc(), &1)));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_key_value<'a>(&'a self, prefix: &P) -> Option<(P, &'a T)> {
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        let element = self.table.find_element(key, prefix_len).present()?;
        Some((element.prefix(key), self.table.get_data(element)))
    }

    /// Get a value of an element by using longest prefix matching
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
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
    ///
    /// **Warning** The table does not store the prefix, but it is reconstructed. This means, that
    /// any bits in the host part will be truncated:
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.1/24".parse()?, 1);
    /// assert_eq!(pm.get_lpm(&"192.168.1.1/32".parse()?), Some(("192.168.1.0/24".parse()?, &1)));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_lpm<'a>(&'a self, prefix: &P) -> Option<(P, &'a T)> {
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        let element = self.table.find_lpm(key, prefix_len)?;
        Some((element.prefix(key), self.table.get_data(element)))
    }

    /// Get a mutable reference to a value of an element by using longest prefix matching
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// assert_eq!(pm.get_lpm_mut(&"192.168.1.1/32".parse()?), Some(("192.168.1.0/24".parse()?, &mut 1)));
    /// *pm.get_lpm_mut(&"192.168.1.64/26".parse()?).unwrap().1 += 1;
    /// assert_eq!(pm.get_lpm_mut(&"192.168.1.1/32".parse()?), Some(("192.168.1.0/24".parse()?, &mut 2)));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    ///
    /// **Warning** The table does not store the prefix, but it is reconstructed. This means, that
    /// any bits in the host part will be truncated.
    pub fn get_lpm_mut<'a>(&'a mut self, prefix: &P) -> Option<(P, &'a mut T)> {
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        let element = self.table.find_lpm(key, prefix_len)?;
        Some((element.prefix(key), self.table.get_data_mut(element)))
    }

    /// Get the longest prefix in the datastructure that matches the given `prefix`.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
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
    ///
    /// **Warning** The table does not store the prefix, but it is reconstructed. This means, that
    /// any bits in the host part will be truncated:
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.1/24".parse()?, 1);
    /// assert_eq!(pm.get_lpm_prefix(&"192.168.1.1/32".parse()?), Some("192.168.1.0/24".parse()?));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_lpm_prefix(&self, prefix: &P) -> Option<P> {
        self.get_lpm(prefix).map(|(p, _)| p)
    }

    /// Check if a key is present in the datastructure.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
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
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        self.table.find_element(key, prefix_len).present().is_some()
    }

    /// Get a value of an element by using shortest prefix matching.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
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
    /// ```
    ///
    /// **Warning** The table does not store the prefix, but it is reconstructed. This means, that
    /// any bits in the host part will be truncated.
    pub fn get_spm<'a>(&'a self, prefix: &P) -> Option<(P, &'a T)> {
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        let element = self.table.find_spm(key, prefix_len)?;
        Some((element.prefix(key), self.table.get_data(element)))
    }

    /// Get the shortest prefix in the datastructure that contains the given `prefix`.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
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
    /// ```
    ///
    /// **Warning** The table does not store the prefix, but it is reconstructed. This means, that
    /// any bits in the host part will be truncated.
    pub fn get_spm_prefix(&self, prefix: &P) -> Option<P> {
        self.get_spm(prefix).map(|(p, _)| p)
    }

    /// Insert a new item into the prefix-map. This function may return any value that existed
    /// before.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
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
    ///
    /// **Warning**: You *cannot* store additional information in the host-part of the prefix.
    /// Prefixes are reconstructed from the trie position, so host bits are not preserved.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    ///
    /// pm.insert("192.168.0.1/24".parse()?, 1);
    /// assert_eq!(
    ///     pm.get_key_value(&"192.168.0.0/24".parse()?),
    ///     Some(("192.168.0.0/24".parse()?, &1)) // notice that the host part is zero.
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn insert(&mut self, prefix: P, value: T) -> Option<T> {
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        let element = self.table.find_node_or_insert(key, prefix_len);

        match element {
            Ok(present) => Some(self.table.replace_data(present, value)),
            Err(empty) => {
                self.table.set_data(empty, value);
                self.count += 1;
                None
            }
        }
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// Prefixes are not stored verbatim. They are reconstructed from the trie position, so host
    /// bits masked out by the prefix length are not preserved. See the documentation of
    /// [`Entry`], [`OccupiedEntry`], and [`VacantEntry`].
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, Vec<i32>> = PrefixMap::new();
    /// pm.insert("192.168.0.0/23".parse()?, vec![1]);
    /// pm.entry("192.168.0.1/23".parse()?).or_default().push(2);
    /// pm.entry("192.168.0.0/24".parse()?).or_default().push(3);
    /// assert_eq!(pm.get(&"192.168.0.0/23".parse()?), Some(&vec![1, 2]));
    /// assert_eq!(pm.get(&"192.168.0.0/24".parse()?), Some(&vec![3]));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn entry(&mut self, prefix: P) -> Entry<'_, P, T> {
        // search the entry
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        match self.table.find_element(key, prefix_len) {
            Location::Present(present) => {
                Entry::Occupied(OccupiedEntry::new(self, present, prefix))
            }
            Location::Empty(empty) => Entry::Vacant(VacantEntry::empty(self, empty, prefix)),
            Location::NoNode(no_node) => Entry::Vacant(VacantEntry::no_node(self, no_node, prefix)),
        }
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the
    /// map. In contrast to [`Self::remove_keep_tree`], this operation may prune empty trie nodes,
    /// reducing the memory footprint.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
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
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        let (element, mut path) = self.table.find_element_with_path(key, prefix_len)?;

        // remove the node if it exists
        let mut old_value = None;
        if let Ok(present) = element {
            old_value = Some(self.table.take_data(present));
            self.count -= 1;
        }

        // clean up the tree
        if !element.node().is_empty() {
            self.table.cleanup_tree(element.node(), &mut path);
        }

        old_value
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the
    /// map. In contrast to [`Self::remove`], this operation only removes the stored value and may
    /// leave empty trie nodes in place.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// let prefix = "192.168.1.0/24".parse()?;
    /// pm.insert(prefix, 1);
    /// assert_eq!(pm.get(&prefix), Some(&1));
    /// assert_eq!(pm.remove_keep_tree(&prefix), Some(1));
    /// assert_eq!(pm.get(&prefix), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn remove_keep_tree(&mut self, prefix: &P) -> Option<T> {
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        let element = self.table.find_element(key, prefix_len).present()?;
        self.count -= 1;
        Some(self.table.take_data(element))
    }

    /// Remove all entries that are contained within `prefix`. This will change the tree
    /// structure. This operation is `O(n)`, as the entries must be freed up one-by-one.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.0.0/21".parse()?, 1);
    /// pm.insert("192.168.0.0/22".parse()?, 2);
    /// pm.insert("192.168.0.0/23".parse()?, 3);
    /// pm.insert("192.168.0.0/24".parse()?, 4);
    /// pm.insert("192.168.4.0/22".parse()?, 5);
    /// pm.insert("192.168.4.0/23".parse()?, 6);
    ///
    /// assert_eq!(pm.len(), 6);
    /// pm.remove_children(&"192.168.0.0/22".parse()?);
    /// assert_eq!(pm.len(), 3);
    ///
    /// assert_eq!(pm.get(&"192.168.0.0/22".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.0.0/23".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.0.0/24".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.4.0/22".parse()?), Some(&5));
    /// assert_eq!(pm.get(&"192.168.4.0/23".parse()?), Some(&6));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn remove_children(&mut self, prefix: &P) {
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;

        if prefix_len == 0 {
            return self.clear();
        }

        let Some(element) = self.table.find_element(key, prefix_len).into_node() else {
            return;
        };
        let node = element.node();
        let depth = element.depth();

        // fast-track delete this index if it covers the entire node
        if prefix_len % K == 0 {
            self.count -= self.table.clear_node_and_children(node);
            return;
        }

        // delete all elements within this node that are covered.
        // Iterate in reverse bit order to avoid shifting lower-bit elements.
        // This ensures that removing a higher-bit element doesn't shift the physical slot
        // of a lower-bit element, maintaining slot validity across removals.
        let covered = self
            .table
            .data_descendants(element.node(), depth, key, prefix_len);
        for loc in covered.rev() {
            // Refresh the loc against the current node state: a prior take_data on the same
            // node may have triggered a tier downgrade, changing data_idx and slot positions.
            let loc = loc.refresh(&self.table);
            self.table.take_data(loc);
            self.count -= 1;
        }

        // Collect bitmap bits of covered children (from original bitmap).
        let covered_child_bits: Vec<u32> = self
            .table
            .node(node)
            .child_cover_locs(depth, key, prefix_len)
            .map(|loc| loc.bit)
            .collect();

        // First: clear each covered child's subtree using the original Loc (parent bitmap unchanged).
        for &child_bit in &covered_child_bits {
            let child_loc = self
                .table
                .child(node, child_bit)
                .expect("child_bit should exist in bitmap");
            self.count -= self.table.clear_node_and_children(child_loc);
        }

        // Then: remove covered children from parent in reverse bit order so that removing a
        // higher-bit child does not shift the physical slot of a lower-bit child.
        for &child_bit in covered_child_bits.iter().rev() {
            self.table.remove_child_at(node, child_bit);
        }
    }

    /// Clear the map but keep the allocated memory.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
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
        let deleted = self.table.clear_node_and_children(Loc::root());
        debug_assert_eq!(deleted, self.count);
        self.count = 0;
    }

    /// Keep only the elements in the map that satisfy the given condition `f`.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
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
    ///
    /// You can also use the prefix for filtering
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.0.0/24".parse()?, 1);
    /// pm.insert("192.168.1.0/24".parse()?, 2);
    /// pm.insert("192.168.2.0/24".parse()?, 3);
    /// pm.insert("192.168.2.0/25".parse()?, 4);
    /// pm.retain(|p, _| p.prefix_len() > 24);
    /// assert_eq!(pm.get(&"192.168.0.0/24".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.2.0/24".parse()?), None);
    /// assert_eq!(pm.get(&"192.168.2.0/25".parse()?), Some(&4));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&P, &T) -> bool,
    {
        let removed = self.table.retain_all::<P, _>(&mut f);
        self.count -= removed;
    }

    /// Iterate over all entries in the map that covers the given `prefix` (including `prefix`
    /// itself if that is present in the map). The returned iterator yields `(P, &'a T)`, with
    /// reconstructed prefixes `P`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
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
    ///     vec![(p0, &0), (p1, &1), (p2, &2)]
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    ///
    /// This function also yields the root node *if* it is part of the map:
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// let root = "0.0.0.0/0".parse()?;
    /// pm.insert(root, 0);
    /// assert_eq!(pm.cover(&"10.0.0.0/8".parse()?).collect::<Vec<_>>(), vec![(root, &0)]);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn cover<'a>(&'a self, prefix: &P) -> Cover<'a, P, T> {
        Cover::new(self, prefix)
    }

    /// Iterate over all keys (prefixes) in the map that covers the given `prefix` (including
    /// `prefix` itself if that is present in the map). The returned iterator yields reconstructed
    /// prefixes `P`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
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
    /// assert_eq!(pm.cover_keys(&p2).collect::<Vec<_>>(), vec![p0, p1, p2]);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn cover_keys<'a>(&'a self, prefix: &P) -> CoverKeys<'a, P, T> {
        CoverKeys(Cover::new(self, prefix))
    }

    /// Iterate over all values in the map that covers the given `prefix` (including `prefix`
    /// itself if that is present in the map). The returned iterator yields `&'a T`.
    ///
    /// The iterator will always yield elements ordered by their prefix length, i.e., their depth in
    /// the tree.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
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
    pub fn cover_values<'a>(&'a self, prefix: &P) -> CoverValues<'a, P, T> {
        CoverValues(Cover::new(self, prefix))
    }

    /// An iterator visiting all key-value pairs in lexicographic order. The iterator element type
    /// is `(P, &T)`, with reconstructed prefixes `P`.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.0.0/22".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// pm.insert("192.168.2.0/23".parse()?, 3);
    /// pm.insert("192.168.0.0/24".parse()?, 4);
    /// pm.insert("192.168.2.0/24".parse()?, 5);
    /// assert_eq!(
    ///     pm.iter().collect::<Vec<_>>(),
    ///     vec![
    ///         ("192.168.0.0/22".parse()?, &1),
    ///         ("192.168.0.0/23".parse()?, &2),
    ///         ("192.168.0.0/24".parse()?, &4),
    ///         ("192.168.2.0/23".parse()?, &3),
    ///         ("192.168.2.0/24".parse()?, &5),
    ///     ]
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn iter(&self) -> Iter<'_, P, T> {
        self.into_iter()
    }

    /// Get a mutable iterator over all key-value pairs. The order of this iterator is lexicographic.
    pub fn iter_mut(&mut self) -> IterMut<'_, P, T> {
        IterMut::new(&mut self.table)
    }

    /// An iterator visiting all keys in lexicographic order. The iterator element type is
    /// reconstructed prefixes `P`.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.0.0/22".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// pm.insert("192.168.2.0/23".parse()?, 3);
    /// pm.insert("192.168.0.0/24".parse()?, 4);
    /// pm.insert("192.168.2.0/24".parse()?, 5);
    /// assert_eq!(
    ///     pm.keys().collect::<Vec<_>>(),
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
    #[inline(always)]
    pub fn keys(&self) -> Keys<'_, P, T> {
        Keys(self.iter())
    }

    /// Creates a consuming iterator visiting all keys in lexicographic order. The iterator element
    /// type is reconstructed prefixes `P`.
    #[inline(always)]
    pub fn into_keys(self) -> IntoKeys<P, T> {
        IntoKeys(self.into_iter())
    }

    /// An iterator visiting all values in lexicographic order. The iterator element type is `&T`.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.0.0/22".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// pm.insert("192.168.2.0/23".parse()?, 3);
    /// pm.insert("192.168.0.0/24".parse()?, 4);
    /// pm.insert("192.168.2.0/24".parse()?, 5);
    /// assert_eq!(pm.values().collect::<Vec<_>>(), vec![&1, &2, &4, &3, &5]);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn values(&self) -> Values<'_, P, T> {
        Values(self.iter())
    }

    /// Creates a consuming iterator visiting all values in lexicographic order. The iterator
    /// element type is `T`.
    #[inline(always)]
    pub fn into_values(self) -> IntoValues<P, T> {
        IntoValues(self.into_iter())
    }

    /// Get a mutable iterator over all values. The order of this iterator is lexicographic.
    pub fn values_mut(&mut self) -> ValuesMut<'_, P, T> {
        ValuesMut(self.iter_mut())
    }
}

impl<P, T> PrefixMap<P, T>
where
    P: Prefix,
{
    /// Get an iterator over the node itself and all children. All elements returned have a prefix
    /// that is contained within `prefix` itself (or are the same). The iterator yields
    /// `(P, &'a T)`, with reconstructed prefixes `P`. The iterator yields elements in
    /// lexicographic order.
    ///
    /// **Note**: Consider using [`crate::AsView::view_at`] as an alternative.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.0.0/22".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// pm.insert("192.168.2.0/23".parse()?, 3);
    /// pm.insert("192.168.0.0/24".parse()?, 4);
    /// pm.insert("192.168.2.0/24".parse()?, 5);
    /// assert_eq!(
    ///     pm.children(&"192.168.0.0/23".parse()?).collect::<Vec<_>>(),
    ///     vec![
    ///         ("192.168.0.0/23".parse()?, &2),
    ///         ("192.168.0.0/24".parse()?, &4),
    ///     ]
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn children<'a>(&'a self, prefix: &P) -> Iter<'a, P, T> {
        let lex = iter::lpm_children_iter_start(&self.table, prefix);
        Iter::at_node(&self.table, lex)
    }

    /// Get an iterator of mutable references of the node itself and all its children. All elements
    /// returned have a prefix that is contained within `prefix` itself (or are the same). The
    /// iterator yields `(P, &'a mut T)`, with reconstructed prefixes `P`. The iterator yields
    /// elements in lexicographic order.
    ///
    /// **Note**: Consider using [`crate::AsView::view_at`] on a mutable map reference as an
    /// alternative.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.0.0/22".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// pm.insert("192.168.0.0/24".parse()?, 3);
    /// pm.insert("192.168.2.0/23".parse()?, 4);
    /// pm.insert("192.168.2.0/24".parse()?, 5);
    /// pm.children_mut(&"192.168.0.0/23".parse()?).for_each(|(_, x)| *x *= 10);
    /// assert_eq!(
    ///     pm.into_iter().collect::<Vec<_>>(),
    ///     vec![
    ///         ("192.168.0.0/22".parse()?, 1),
    ///         ("192.168.0.0/23".parse()?, 20),
    ///         ("192.168.0.0/24".parse()?, 30),
    ///         ("192.168.2.0/23".parse()?, 4),
    ///         ("192.168.2.0/24".parse()?, 5),
    ///     ]
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn children_mut<'a>(&'a mut self, prefix: &P) -> IterMut<'a, P, T> {
        let lex = iter::lpm_children_iter_start(&self.table, prefix);
        IterMut::at_node(&mut self.table, lex)
    }

    /// Get an iterator over the node itself and all children with a value. All elements returned
    /// have a prefix that is contained within `prefix` itself (or are the same). This function will
    /// consume `self`, returning an iterator over all owned children.
    ///
    /// ```
    /// # use prefix_trie::*; use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.0.0/22".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// pm.insert("192.168.2.0/23".parse()?, 3);
    /// pm.insert("192.168.0.0/24".parse()?, 4);
    /// pm.insert("192.168.2.0/24".parse()?, 5);
    /// assert_eq!(
    ///     pm.into_children(&"192.168.0.0/23".parse()?).collect::<Vec<_>>(),
    ///     vec![
    ///         ("192.168.0.0/23".parse()?, 2),
    ///         ("192.168.0.0/24".parse()?, 4),
    ///     ]
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn into_children(self, prefix: &P) -> IntoIter<P, T> {
        let lex = iter::lpm_children_iter_start(&self.table, prefix);
        IntoIter::at_node(self.table, lex)
    }

    /// Check the allocator: No memory should be unreferenced, and no memory should be aliased
    /// (double referenced). This function returns `true` if the allocator is in a correct state,
    /// and `false` if the memory is corrupt.
    #[cfg(test)]
    pub fn check_memory_alloc(&self) -> bool {
        self.table.check_memory_alloc()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prefix::Prefix;

    // Minimal prefix type: (repr, len)
    type P = (u32, u8);

    fn p(repr: u32, len: u8) -> P {
        P::from_repr_len(repr, len)
    }

    fn map_from(entries: &[(u32, u8, i32)]) -> PrefixMap<P, i32> {
        let mut m = PrefixMap::new();
        for &(repr, len, val) in entries {
            m.insert(p(repr, len), val);
        }
        m
    }

    fn iter_keys(m: &PrefixMap<P, i32>) -> Vec<P> {
        m.iter().map(|(p, _)| p).collect()
    }

    struct DropCounter(std::rc::Rc<std::cell::Cell<usize>>);

    impl Drop for DropCounter {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    // ---- basic storage ----

    #[test]
    fn test_insert_and_get_root() {
        // /0 prefix (the single root prefix covering everything)
        let mut m = PrefixMap::new();
        m.insert(p(0, 0), 42);
        assert_eq!(m.get(&p(0, 0)), Some(&42));
        assert_eq!(m.len(), 1);
    }

    #[test]
    fn test_insert_root_and_child_separate() {
        // /0 and 0/1 must be stored as distinct entries
        let mut m = PrefixMap::new();
        m.insert(p(0, 0), 1);
        m.insert(p(0, 1), 2);
        assert_eq!(m.len(), 2);
        assert_eq!(m.get(&p(0, 0)), Some(&1));
        assert_eq!(m.get(&p(0, 1)), Some(&2));
    }

    #[test]
    fn test_insert_sibling_prefixes() {
        // 0/1 (left half) and 0x80000000/1 (right half)
        let mut m = PrefixMap::new();
        m.insert(p(0x00000000, 1), 1);
        m.insert(p(0x80000000, 1), 2);
        assert_eq!(m.len(), 2);
        assert_eq!(m.get(&p(0x00000000, 1)), Some(&1));
        assert_eq!(m.get(&p(0x80000000, 1)), Some(&2));
    }

    #[test]
    fn test_drop_drops_values() {
        let drops = std::rc::Rc::new(std::cell::Cell::new(0));
        {
            let mut m = PrefixMap::new();
            m.insert(p(0, 0), DropCounter(drops.clone()));
            m.insert(p(0, 1), DropCounter(drops.clone()));
            m.insert(p(0x80000000, 1), DropCounter(drops.clone()));
        }
        assert_eq!(drops.get(), 3);
    }

    #[test]
    fn test_partial_into_iter_drop_drops_remaining_values() {
        let drops = std::rc::Rc::new(std::cell::Cell::new(0));
        {
            let mut m = PrefixMap::new();
            m.insert(p(0, 0), DropCounter(drops.clone()));
            m.insert(p(0, 1), DropCounter(drops.clone()));
            m.insert(p(0x80000000, 1), DropCounter(drops.clone()));

            let mut iter = m.into_iter();
            drop(iter.next().unwrap());
            assert_eq!(drops.get(), 1);
        }
        assert_eq!(drops.get(), 3);
    }

    #[test]
    fn test_children() {
        let mut m = PrefixMap::new();
        m.insert(p(0x0a000000, 8), 1);
        m.insert(p(0x0a010000, 16), 2);
        m.insert(p(0x0a020000, 16), 3);
        m.insert(p(0x0a010000, 24), 4);
        // View at 10.1.0.0/16: should include /16 and /24, not /8 or 10.2.0.0/16
        let got: Vec<_> = m
            .children(&p(0x0a010000, 16))
            .map(|(p, x)| (p, *x))
            .collect();
        assert_eq!(got, vec![(p(0x0a010000, 16), 2), (p(0x0a010000, 24), 4)]);
    }

    // ---- iterator ordering ----

    #[test]
    fn test_iter_order_root_before_child() {
        // /0 must come before 0/1 in iteration
        let m = map_from(&[(0, 0, 1), (0, 1, 2)]);
        let keys = iter_keys(&m);
        assert_eq!(keys, vec![p(0, 0), p(0, 1)], "root must precede child");
    }

    #[test]
    fn test_iter_order_left_before_right() {
        // 0/1 must come before 0x80000000/1
        let m = map_from(&[(0x00000000, 1, 1), (0x80000000, 1, 2)]);
        let keys = iter_keys(&m);
        assert_eq!(
            keys,
            vec![p(0x00000000, 1), p(0x80000000, 1)],
            "left sibling must precede right sibling"
        );
    }

    #[test]
    fn test_iter_order_root_then_siblings() {
        // /0, 0/1, 0x80000000/1: root first, then left, then right
        let m = map_from(&[(0, 0, 0), (0x00000000, 1, 1), (0x80000000, 1, 2)]);
        let keys = iter_keys(&m);
        assert_eq!(keys, vec![p(0, 0), p(0, 1), p(0x80000000, 1)]);
    }

    #[test]
    fn test_iter_order_matches_hashmap_sort() {
        // The key invariant: PrefixMap iter order == sorted-by-Ord order of keys.
        // (Both share the property that parent comes before child and left before right,
        // since Prefix::Ord orders by (repr, len) which puts containing prefixes earlier.)
        let entries: &[(u32, u8, i32)] = &[
            (0x00000000, 0, 10),
            (0x00000000, 1, 20),
            (0x80000000, 1, 30),
            (0x00000000, 2, 40),
            (0x40000000, 2, 50),
        ];
        let m = map_from(entries);
        let mut expected: Vec<P> = entries.iter().map(|&(r, l, _)| p(r, l)).collect();
        expected.sort();
        assert_eq!(iter_keys(&m), expected);
    }

    #[test]
    fn test_iter_order_5_6() {
        let entries = &[(0xd0000000, 5, 1), (0xd0000000, 6, 2)];
        let m = map_from(entries);
        let mut expected: Vec<P> = entries.iter().map(|&(r, l, _)| p(r, l)).collect();
        expected.sort();
        assert_eq!(iter_keys(&m), expected);
    }

    #[test]
    fn test_remove_children_leak() {
        // Reproduce the quickcheck minimal failing case exactly
        use crate::fuzzing::TestPrefix;
        let tp = |repr: u32, len: u8| -> TestPrefix { crate::Prefix::from_repr_len(repr, len) };
        let mut pmap: PrefixMap<TestPrefix, i32> = PrefixMap::new();
        // Minimal case from quickcheck: /6 contains /7, remove_children(/6) should remove both
        pmap.insert(tp(0x00000000, 6), 0);
        pmap.insert(tp(0x00000000, 7), 0);
        assert!(pmap.check_memory_alloc(), "leak before remove_children");
        pmap.remove_children(&tp(0x00000000, 6));
        assert!(pmap.check_memory_alloc(), "leak after remove_children");
    }

    #[test]
    fn test_retain_leak() {
        use crate::fuzzing::TestPrefix;
        let tp = |repr: u32, len: u8| -> TestPrefix { crate::Prefix::from_repr_len(repr, len) };
        let mut pmap: PrefixMap<TestPrefix, i32> = PrefixMap::new();
        pmap.insert(tp(0xf0000000, 5), 0);
        pmap.insert(tp(0xf8000000, 5), 0);
        assert!(pmap.check_memory_alloc(), "leak before retain");
        pmap.retain(|pp, _| pp.prefix_len() < 2);
        assert!(pmap.check_memory_alloc(), "leak after retain");
    }

    #[test]
    fn test_remove_children_minimal() {
        use crate::Prefix;

        let mut pmap: PrefixMap<(u32, u8), i32> = PrefixMap::new();

        let p1 = <(u32, u8) as Prefix>::from_repr_len(0u32, 1);
        let p2 = <(u32, u8) as Prefix>::from_repr_len(0x40000000u32, 2); // bit 30 set
        let p3 = <(u32, u8) as Prefix>::from_repr_len(0x80000000u32, 2); // bit 31 set

        pmap.insert(p1, 0);
        pmap.insert(p2, 1);
        pmap.insert(p3, 0);

        pmap.remove_children(&p1);

        let want: Vec<_> = vec![(p3, 0)];
        let actual: Vec<_> = pmap.into_iter().collect();

        assert_eq!(want, actual, "mismatch in remove_children result");
    }

    #[test]
    fn test_retain_minimal() {
        use crate::Prefix;

        let mut pmap: PrefixMap<(u32, u8), i32> = PrefixMap::new();

        let p1 = <(u32, u8) as Prefix>::from_repr_len(0x50000000u32, 5);
        let p2 = <(u32, u8) as Prefix>::from_repr_len(0x50000000u32, 6);
        let p3 = <(u32, u8) as Prefix>::from_repr_len(0x5c000000u32, 6);

        pmap.insert(p1, 0);
        pmap.insert(p2, 1);
        pmap.insert(p3, 1);

        // Retain: keep elements where !(root.contains(p) && p.1 >= root.1 + 2)
        let predicate = |_: &(u32, u8), v: &i32| *v == 0;

        let want: Vec<_> = pmap
            .iter()
            .filter(|(p, v)| predicate(p, v))
            .map(|(p, v)| (p, *v))
            .collect();

        pmap.retain(predicate);

        let actual: Vec<_> = pmap.into_iter().collect();

        assert_eq!(want, actual, "mismatch in retain result");
    }

    // /32 host routes require depth=30 with K=5, which means depth+K=35 > 32 (num_bits).
    // The `data_offset` and `get_mask` functions compute a shift of `32-30-5 = -3`,
    // which underflows u32: panics in debug, wraps in release causing collisions.
    mod max_prefix_length {
        use super::*;

        #[test]
        fn distinct_offsets() {
            // Four /32 addresses whose bottom 2 bits differ (bits 30-31 of the u32).
            // In a correct implementation each must map to a distinct internal offset.
            let mut m: PrefixMap<(u32, u8), i32> = PrefixMap::new();
            let addrs: &[(u32, i32)] = &[
                (0x01020300, 1), // bits 30,31 = 0b00
                (0x01020301, 2), // bits 30,31 = 0b01
                (0x01020302, 3), // bits 30,31 = 0b10
                (0x01020303, 4), // bits 30,31 = 0b11
            ];
            for &(repr, val) in addrs {
                m.insert(p(repr, 32), val);
            }
            assert_eq!(
                m.len(),
                4,
                "all four /32s must be stored as distinct entries"
            );
            for &(repr, val) in addrs {
                assert_eq!(
                    m.get(&p(repr, 32)),
                    Some(&val),
                    "wrong value for /32 addr {:#010x}",
                    repr,
                );
            }
        }

        #[test]
        fn lpm() {
            // /24 parent + /32 child: LPM on the /32 address must return the /32 value.
            let mut m: PrefixMap<(u32, u8), i32> = PrefixMap::new();
            m.insert(p(0x01020300, 24), 10); // 1.2.3.0/24
            m.insert(p(0x01020304, 32), 42); // 1.2.3.4/32
            assert_eq!(
                m.get_lpm(&p(0x01020304, 32)),
                Some((p(0x01020304, 32), &42))
            );
            assert_eq!(
                m.get_lpm(&p(0x01020305, 32)),
                Some((p(0x01020300, 24), &10))
            );
        }

        #[test]
        fn iter() {
            // All /32 entries must appear in the iterator with correct (prefix, value) pairs.
            let addrs: &[(u32, i32)] = &[
                (0xc0000000, 10),
                (0xc0000001, 20),
                (0xc0000002, 30),
                (0xc0000003, 40),
            ];
            let mut m: PrefixMap<(u32, u8), i32> = PrefixMap::new();
            for &(repr, val) in addrs {
                m.insert(p(repr, 32), val);
            }
            let mut got: Vec<_> = m.iter().map(|(k, v)| (k.0, *v)).collect();
            got.sort_by_key(|&(r, _)| r);
            let want: Vec<_> = addrs.to_vec();
            assert_eq!(got, want);
        }

        #[test]
        fn remove() {
            // Insert four /32s, remove two, verify the remaining two are correct.
            let mut m: PrefixMap<(u32, u8), i32> = PrefixMap::new();
            m.insert(p(0x01020300, 32), 1);
            m.insert(p(0x01020301, 32), 2);
            m.insert(p(0x01020302, 32), 3);
            m.insert(p(0x01020303, 32), 4);

            assert_eq!(m.remove(&p(0x01020301, 32)), Some(2));
            assert_eq!(m.remove(&p(0x01020302, 32)), Some(3));

            assert_eq!(m.len(), 2);
            assert_eq!(m.get(&p(0x01020300, 32)), Some(&1));
            assert_eq!(m.get(&p(0x01020301, 32)), None);
            assert_eq!(m.get(&p(0x01020302, 32)), None);
            assert_eq!(m.get(&p(0x01020303, 32)), Some(&4));
        }

        #[test]
        fn remove_children_of_slash31() {
            // A /31 (no value) covers exactly two /32 host routes (.2 and .3).
            // A third /32 (.0) sits outside the /31.
            // remove_children(&/31) must drop the two covered /32s but leave the outsider.
            let mut m: PrefixMap<(u32, u8), i32> = PrefixMap::new();
            let parent = p(0x01020302, 31); // 1.2.3.2/31 (covers .2 and .3, no value)
            m.insert(p(0x01020300, 32), 10); // outside /31
            m.insert(p(0x01020302, 32), 1); // inside /31
            m.insert(p(0x01020303, 32), 2); // inside /31

            m.remove_children(&parent);

            assert_eq!(m.len(), 1);
            assert_eq!(
                m.get(&p(0x01020300, 32)),
                Some(&10),
                ".0/32 outside /31 must survive"
            );
            assert_eq!(m.get(&p(0x01020302, 32)), None, ".2/32 must be gone");
            assert_eq!(m.get(&p(0x01020303, 32)), None, ".3/32 must be gone");
        }
    }
}
