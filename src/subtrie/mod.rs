//! A [`SubTrie`] is a pointer to a specific element in a PrefixTrie, representing the sub-tree
//! rooted at that node.
//!
//! This module allows you to perform Set operations (union, intersection, difference) on
//! [`PrefixMap`]s and [`PrefixSet`]s, optionally of only a sub-trie.

use crate::{
    map::{Direction, Iter, Keys, Values},
    Prefix, PrefixMap, PrefixSet,
};

/// A trait for creating a SubTrie of `self`.
pub trait AsSubTrie {
    /// The prefix of the SubTrie
    type P: Prefix;
    /// The value of the map in the Trie.
    type T;

    /// Get a SubTrie rooted at the origin (referencing the entire trie).
    fn sub_trie(&self) -> SubTrie<'_, Self::P, Self::T>;

    /// Get a SubTrie rooted at the given `prefix`. If that `prefix` is not part of the trie, `None`
    /// is returned. Calling this function is identical to `self.sub_trie().find(prefix)`.
    fn sub_trie_at(&self, prefix: &Self::P) -> Option<SubTrie<'_, Self::P, Self::T>> {
        self.sub_trie().find(prefix)
    }
}

impl<P: Prefix, T> AsSubTrie for PrefixMap<P, T> {
    type P = P;
    type T = T;

    fn sub_trie(&self) -> SubTrie<'_, Self::P, Self::T> {
        SubTrie { map: self, idx: 0 }
    }
}

impl<P: Prefix> AsSubTrie for PrefixSet<P> {
    type P = P;
    type T = ();

    fn sub_trie(&self) -> SubTrie<'_, Self::P, Self::T> {
        SubTrie {
            map: &self.0,
            idx: 0,
        }
    }
}

/// A subtree of a prefix-trie rooted at a specific node.
#[derive(Clone, Copy)]
pub struct SubTrie<'a, P, T> {
    map: &'a PrefixMap<P, T>,
    idx: usize,
}

impl<P: std::fmt::Debug, T: std::fmt::Debug> std::fmt::Debug for SubTrie<'_, P, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Cursor")
            .field(&self.map.table[self.idx].prefix)
            .finish()
    }
}

impl<'a, P, T> SubTrie<'a, P, T>
where
    P: Prefix,
{
    /// Find `prefix`, returning a new SubTrie that points to the first node that is contained
    /// within that prefix (or `prefix` itself). Only the current sub-tree is searched. If `prefix`
    /// is not present in the sub-trie referenced by `self` (including any sub-prefix), the function
    /// returns `None`.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # use prefix_trie::subtrie::Either;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::Ipv4Net>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map: PrefixMap<ipnet::Ipv4Net, usize> = PrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), 1),
    ///     (net!("192.168.0.0/22"), 2),
    ///     (net!("192.168.0.0/24"), 3),
    ///     (net!("192.168.2.0/23"), 4),
    ///     (net!("192.168.4.0/22"), 5),
    /// ]);
    /// let sub = map.sub_trie();
    /// assert_eq!(
    ///     sub.find(&net!("192.168.0.0/21")).unwrap().keys().collect::<Vec<_>>(),
    ///     vec![
    ///         &net!("192.168.0.0/22"),
    ///         &net!("192.168.0.0/24"),
    ///         &net!("192.168.2.0/23"),
    ///         &net!("192.168.4.0/22"),
    ///     ]
    /// );
    /// assert_eq!(
    ///     sub.find(&net!("192.168.0.0/22")).unwrap().keys().collect::<Vec<_>>(),
    ///     vec![
    ///         &net!("192.168.0.0/22"),
    ///         &net!("192.168.0.0/24"),
    ///         &net!("192.168.2.0/23"),
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn find(&self, prefix: &P) -> Option<SubTrie<'a, P, T>> {
        let mut last_idx = self.idx;
        let mut idx = self.idx;
        loop {
            match self.map.get_direction(idx, prefix) {
                Direction::Enter { next, .. } => {
                    last_idx = idx;
                    idx = next;
                }
                Direction::Reached => return Some(Self { map: self.map, idx }),
                Direction::Missing if self.map.table[last_idx].prefix.contains(prefix) => {
                    return Some(Self {
                        map: self.map,
                        idx: last_idx,
                    })
                }
                Direction::Missing => return None,
            }
        }
    }

    /// Find `prefix`, returning a new SubTrie that points to that node. Only the current sub-tree is
    /// searched. If this prefix is not present in the sub-tree pointed to by `self`, the function
    /// returns `None`.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # use prefix_trie::subtrie::Either;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::Ipv4Net>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map: PrefixMap<ipnet::Ipv4Net, usize> = PrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), 1),
    ///     (net!("192.168.0.0/22"), 2),
    ///     (net!("192.168.0.0/24"), 3),
    ///     (net!("192.168.2.0/23"), 4),
    ///     (net!("192.168.4.0/22"), 5),
    /// ]);
    /// let sub = map.sub_trie();
    /// assert!(sub.find_exact(&net!("192.168.0.0/21")).is_none());
    /// assert_eq!(
    ///     sub.find_exact(&net!("192.168.0.0/22")).unwrap().keys().collect::<Vec<_>>(),
    ///     vec![
    ///         &net!("192.168.0.0/22"),
    ///         &net!("192.168.0.0/24"),
    ///         &net!("192.168.2.0/23"),
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn find_exact(&self, prefix: &P) -> Option<SubTrie<'a, P, T>> {
        let mut idx = self.idx;
        loop {
            match self.map.get_direction(idx, prefix) {
                Direction::Reached => {
                    return self.map.table[idx]
                        .value
                        .is_some()
                        .then_some(Self { map: self.map, idx })
                }
                Direction::Enter { next, .. } => idx = next,
                Direction::Missing => return None,
            }
        }
    }

    /// Find the longest match of `prefix`, returning a new cursor that points to that node. Only
    /// the given sub-tree is searched. If the prefix is not present in the sub-tree pointed to by
    /// `self`, the function returns `None`.
    ///
    /// Only cursors to nodes that are present in the map are returned, not to branching nodes.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # use prefix_trie::subtrie::Either;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::Ipv4Net>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map: PrefixMap<ipnet::Ipv4Net, usize> = PrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), 1),
    ///     (net!("192.168.0.0/22"), 2),
    ///     (net!("192.168.0.0/24"), 3),
    ///     (net!("192.168.2.0/23"), 4),
    ///     (net!("192.168.4.0/22"), 5),
    /// ]);
    /// let sub = map.sub_trie();
    /// assert_eq!(
    ///     sub.find_lpm(&net!("192.168.0.0/21")).unwrap().keys().collect::<Vec<_>>(),
    ///     vec![
    ///         &net!("192.168.0.0/20"),
    ///         &net!("192.168.0.0/22"),
    ///         &net!("192.168.0.0/24"),
    ///         &net!("192.168.2.0/23"),
    ///         &net!("192.168.4.0/22"),
    ///     ]
    /// );
    /// assert_eq!(
    ///     sub.find_lpm(&net!("192.168.0.0/22")).unwrap().keys().collect::<Vec<_>>(),
    ///     vec![
    ///         &net!("192.168.0.0/22"),
    ///         &net!("192.168.0.0/24"),
    ///         &net!("192.168.2.0/23"),
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn find_lpm(&self, prefix: &P) -> Option<SubTrie<'a, P, T>> {
        let mut idx = self.idx;
        let mut best_match = None;
        loop {
            if self.map.table[idx].value.is_some() {
                best_match = Some(idx);
            }
            match self.map.get_direction(idx, prefix) {
                Direction::Enter { next, .. } => idx = next,
                _ => return best_match.map(|idx| Self { map: self.map, idx }),
            }
        }
    }
}

impl<'a, P, T> SubTrie<'a, P, T> {
    /// Iterate over all elements in the given sub-tree (including the element itself), in
    /// lexicographic order.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # use prefix_trie::subtrie::Either;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::Ipv4Net>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map: PrefixMap<ipnet::Ipv4Net, usize> = PrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), 1),
    ///     (net!("192.168.0.0/22"), 2),
    ///     (net!("192.168.0.0/24"), 3),
    ///     (net!("192.168.2.0/23"), 4),
    /// ]);
    /// let sub = map.sub_trie_at(&net!("192.168.0.0/22")).unwrap();
    /// assert_eq!(
    ///     sub.iter().collect::<Vec<_>>(),
    ///     vec![
    ///         (&net!("192.168.0.0/22"), &2),
    ///         (&net!("192.168.0.0/24"), &3),
    ///         (&net!("192.168.2.0/23"), &4),
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn iter(&self) -> Iter<'a, P, T> {
        Iter {
            map: self.map,
            nodes: vec![self.idx],
        }
    }

    /// Iterate over all keys in the given sub-tree (including the element itself), in lexicographic
    /// order.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # use prefix_trie::subtrie::Either;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::Ipv4Net>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map: PrefixMap<ipnet::Ipv4Net, usize> = PrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), 1),
    ///     (net!("192.168.0.0/22"), 2),
    ///     (net!("192.168.0.0/24"), 3),
    ///     (net!("192.168.2.0/23"), 4),
    /// ]);
    /// let sub = map.sub_trie_at(&net!("192.168.0.0/22")).unwrap();
    /// assert_eq!(
    ///     sub.keys().collect::<Vec<_>>(),
    ///     vec![&net!("192.168.0.0/22"), &net!("192.168.0.0/24"), &net!("192.168.2.0/23")]
    /// );
    /// # }
    /// ```
    pub fn keys(&self) -> Keys<'a, P, T> {
        Keys { inner: self.iter() }
    }

    /// Iterate over all values in the given sub-tree (including the element itself), in lexicographic
    /// order.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # use prefix_trie::subtrie::Either;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::Ipv4Net>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map: PrefixMap<ipnet::Ipv4Net, usize> = PrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), 1),
    ///     (net!("192.168.0.0/22"), 2),
    ///     (net!("192.168.0.0/24"), 3),
    ///     (net!("192.168.2.0/23"), 4),
    /// ]);
    /// let sub = map.sub_trie_at(&net!("192.168.0.0/22")).unwrap();
    /// assert_eq!(sub.values().collect::<Vec<_>>(), vec![&2, &3, &4]);
    /// # }
    /// ```
    pub fn values(&self) -> Values<'a, P, T> {
        Values { inner: self.iter() }
    }
    /// Get a reference to the prefix that is currently pointed at. This prefix might not exist
    /// explicitly in the map/set, but it is used as a branching node.
    pub fn prefix(&self) -> &'a P {
        &self.map.table[self.idx].prefix
    }

    /// Get a reference to the value at this current point. This function may return `None` if
    /// `self` is pointing at a branching node.
    pub fn value(&self) -> Option<&'a T> {
        self.map.table[self.idx].value.as_ref()
    }

    /// Get a reference to both the prefix and the value. This function may return `None` if either
    /// `self` is pointing at a branching node.
    pub fn prefix_value(&self) -> Option<(&'a P, &'a T)> {
        let x = &self.map.table[self.idx];
        Some((&x.prefix, x.value.as_ref()?))
    }

    /// Get the left branch at the current pointer. The right branch contains all prefix that are
    /// contained within `self.prefix()`, and for which the next bit is set to 0.
    pub fn left(&self) -> Option<Self> {
        Some(Self {
            map: self.map,
            idx: self.map.table[self.idx].left?,
        })
    }

    /// Get the right branch at the current pointer. The right branch contains all prefix that are
    /// contained within `self.prefix()`, and for which the next bit is set to 1.
    pub fn right(&self) -> Option<Self> {
        Some(Self {
            map: self.map,
            idx: self.map.table[self.idx].right?,
        })
    }
}

mod intersection;
mod union;
pub use intersection::Intersection;
pub use union::{Either, Union, UnionLpm, UnionLpmItem};
