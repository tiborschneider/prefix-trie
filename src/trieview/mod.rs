//! A [`TrieView`] (or a [`TrieViewMut`]) is a pointer to a specific element in a PrefixTrie, representing the sub-tree
//! rooted at that node.
//!
//! This module allows you to perform Set operations (union, intersection, difference) on
//! [`PrefixMap`]s and [`PrefixSet`]s, optionally of only a trie-view.

use crate::{
    map::{Direction, Iter, IterMut, Keys, Values, ValuesMut},
    Prefix, PrefixMap, PrefixSet,
};

/// A trait for creating a [`TrieView`] of `self`.
pub trait AsView<'a, P: Prefix, T>: Sized {
    /// Get a TrieView rooted at the origin (referencing the entire trie).
    fn view(self) -> TrieView<'a, P, T>;

    /// Get a TrieView rooted at the given `prefix`. If that `prefix` is not part of the trie, `None`
    /// is returned. Calling this function is identical to `self.view().find(prefix)`.
    fn view_at(self, prefix: &P) -> Option<TrieView<'a, P, T>> {
        self.view().find(prefix)
    }
}

impl<'a, P: Prefix, T> AsView<'a, P, T> for TrieView<'a, P, T> {
    fn view(self) -> TrieView<'a, P, T> {
        self
    }
}

impl<'a, P: Prefix, T> AsView<'a, P, T> for TrieViewMut<'a, P, T> {
    fn view(self) -> TrieView<'a, P, T> {
        TrieView {
            map: self.map,
            idx: self.idx,
        }
    }
}

impl<'a, P: Prefix, T> AsView<'a, P, T> for &'a PrefixMap<P, T> {
    fn view(self) -> TrieView<'a, P, T> {
        TrieView { map: self, idx: 0 }
    }
}

impl<'a, P: Prefix> AsView<'a, P, ()> for &'a PrefixSet<P> {
    fn view(self) -> TrieView<'a, P, ()> {
        TrieView {
            map: &self.0,
            idx: 0,
        }
    }
}

/// A subtree of a prefix-trie rooted at a specific node.
pub struct TrieView<'a, P, T> {
    map: &'a PrefixMap<P, T>,
    idx: usize,
}

impl<P, T> Copy for TrieView<'_, P, T> {}

impl<P, T> Clone for TrieView<'_, P, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<P: std::fmt::Debug, T: std::fmt::Debug> std::fmt::Debug for TrieView<'_, P, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("View")
            .field(&self.map.table[self.idx].prefix)
            .finish()
    }
}

impl<'a, P, T> TrieView<'a, P, T>
where
    P: Prefix,
{
    /// Find `prefix`, returning a new view that points to the first node that is contained
    /// within that prefix (or `prefix` itself). Only the current view is searched. If `prefix`
    /// is not present in the current view referenced by `self` (including any sub-prefix of
    /// `prefix`), the function returns `None`.
    ///
    /// ```
    /// # use prefix_trie::*;
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
    /// let sub = map.view();
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
    pub fn find(&self, prefix: &P) -> Option<TrieView<'a, P, T>> {
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

    /// Find `prefix`, returning a new view that points to that node. Only the current view is
    /// searched. If this prefix is not present in the view pointed to by `self`, the function
    /// returns `None`.
    ///
    /// ```
    /// # use prefix_trie::*;
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
    /// let sub = map.view();
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
    pub fn find_exact(&self, prefix: &P) -> Option<TrieView<'a, P, T>> {
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

    /// Find the longest match of `prefix`, returning a new view that points to that node. Only
    /// the given view is searched. If the prefix is not present in the view pointed to by
    /// `self`, the function returns `None`.
    ///
    /// Only views to nodes that are present in the map are returned, not to branching nodes.
    ///
    /// ```
    /// # use prefix_trie::*;
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
    /// let sub = map.view();
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
    pub fn find_lpm(&self, prefix: &P) -> Option<TrieView<'a, P, T>> {
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

impl<'a, P, T> TrieView<'a, P, T> {
    /// Iterate over all elements in the given view (including the element itself), in
    /// lexicographic order.
    ///
    /// ```
    /// # use prefix_trie::*;
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
    /// let sub = map.view_at(&net!("192.168.0.0/22")).unwrap();
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

    /// Iterate over all keys in the given view (including the element itself), in lexicographic
    /// order.
    ///
    /// ```
    /// # use prefix_trie::*;
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
    /// let sub = map.view_at(&net!("192.168.0.0/22")).unwrap();
    /// assert_eq!(
    ///     sub.keys().collect::<Vec<_>>(),
    ///     vec![&net!("192.168.0.0/22"), &net!("192.168.0.0/24"), &net!("192.168.2.0/23")]
    /// );
    /// # }
    /// ```
    pub fn keys(&self) -> Keys<'a, P, T> {
        Keys { inner: self.iter() }
    }

    /// Iterate over all values in the given view (including the element itself), in lexicographic
    /// order.
    ///
    /// ```
    /// # use prefix_trie::*;
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
    /// let sub = map.view_at(&net!("192.168.0.0/22")).unwrap();
    /// assert_eq!(sub.values().collect::<Vec<_>>(), vec![&2, &3, &4]);
    /// # }
    /// ```
    pub fn values(&self) -> Values<'a, P, T> {
        Values { inner: self.iter() }
    }
    /// Get a reference to the prefix that is currently pointed at. This prefix might not exist
    /// explicitly in the map/set, but may be used as a branching node (or when you call
    /// `remove_keep_tree`).
    pub fn prefix(&self) -> &'a P {
        &self.map.table[self.idx].prefix
    }

    /// Get a reference to the value at the root of the current view. This function may return
    /// `None` if `self` is pointing at a branching node.
    pub fn value(&self) -> Option<&'a T> {
        self.map.table[self.idx].value.as_ref()
    }

    /// Get a reference to both the prefix and the value. This function may return `None` if either
    /// `self` is pointing at a branching node.
    pub fn prefix_value(&self) -> Option<(&'a P, &'a T)> {
        let x = &self.map.table[self.idx];
        Some((&x.prefix, x.value.as_ref()?))
    }

    /// Get the left branch at the current view. The right branch contains all prefix that are
    /// contained within `self.prefix()`, and for which the next bit is set to 0.
    pub fn left(&self) -> Option<Self> {
        Some(Self {
            map: self.map,
            idx: self.map.table[self.idx].left?,
        })
    }

    /// Get the right branch at the current view. The right branch contains all prefix that are
    /// contained within `self.prefix()`, and for which the next bit is set to 1.
    pub fn right(&self) -> Option<Self> {
        Some(Self {
            map: self.map,
            idx: self.map.table[self.idx].right?,
        })
    }
}

impl<'a, P, T> IntoIterator for TrieView<'a, P, T> {
    type Item = (&'a P, &'a T);
    type IntoIter = Iter<'a, P, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// A trait for creating a [`TrieViewMut`] of `self`.
pub trait AsViewMut<'a, P: Prefix, T>: Sized {
    /// Get a mutable view rooted at the origin (referencing the entire trie).
    fn view_mut(self) -> TrieViewMut<'a, P, T>;

    /// Get a mutable view rooted at the given `prefix`. If that `prefix` is not part of the trie, `None`
    /// is returned. Calling this function is identical to `self.view().find(prefix)`.
    fn view_mut_at(self, prefix: &P) -> Option<TrieViewMut<'a, P, T>> {
        self.view_mut().find(prefix).ok()
    }
}

impl<'a, P: Prefix, T> AsViewMut<'a, P, T> for TrieViewMut<'a, P, T> {
    fn view_mut(self) -> TrieViewMut<'a, P, T> {
        self
    }
}

impl<'a, P: Prefix, T> AsViewMut<'a, P, T> for &'a mut PrefixMap<P, T> {
    fn view_mut(self) -> TrieViewMut<'a, P, T> {
        TrieViewMut { map: self, idx: 0 }
    }
}

impl<'a, P: Prefix> AsViewMut<'a, P, ()> for &'a mut PrefixSet<P> {
    fn view_mut(self) -> TrieViewMut<'a, P, ()> {
        TrieViewMut {
            map: &mut self.0,
            idx: 0,
        }
    }
}

/// A mutable view of a prefix-trie rooted at a specific node.
pub struct TrieViewMut<'a, P, T> {
    map: &'a mut PrefixMap<P, T>,
    idx: usize,
}

impl<P: std::fmt::Debug, T: std::fmt::Debug> std::fmt::Debug for TrieViewMut<'_, P, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("ViewMut")
            .field(&self.map.table[self.idx].prefix)
            .finish()
    }
}

impl<P, T> TrieViewMut<'_, P, T>
where
    P: Prefix,
{
    /// Find `prefix`, returning a new view that points to the first node that is contained
    /// within that prefix (or `prefix` itself). Only the current view is searched. If `prefix`
    /// is not present in the current view referenced by `self` (including any sub-prefix of
    /// `prefix`), the function returns the previous view as `Err(self)`.
    ///
    /// ```
    /// # use prefix_trie::*;
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
    /// map.view_mut().find(&net!("192.168.0.0/21")).unwrap().values_mut().for_each(|x| *x += 10);
    /// assert_eq!(
    ///     map.into_iter().collect::<Vec<_>>(),
    ///     vec![
    ///         (net!("192.168.0.0/20"), 1),
    ///         (net!("192.168.0.0/22"), 12),
    ///         (net!("192.168.0.0/24"), 13),
    ///         (net!("192.168.2.0/23"), 14),
    ///         (net!("192.168.4.0/22"), 15),
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn find(self, prefix: &P) -> Result<Self, Self> {
        let mut last_idx = self.idx;
        let mut idx = self.idx;
        loop {
            match self.map.get_direction(idx, prefix) {
                Direction::Enter { next, .. } => {
                    last_idx = idx;
                    idx = next;
                }
                Direction::Reached => return Ok(Self { map: self.map, idx }),
                Direction::Missing if self.map.table[last_idx].prefix.contains(prefix) => {
                    return Ok(Self {
                        map: self.map,
                        idx: last_idx,
                    })
                }
                Direction::Missing => return Err(self),
            }
        }
    }

    /// Find `prefix`, returning a new view that points to that node. Only the current view is
    /// searched. If this prefix is not present in the view pointed to by `self`, the function
    /// returns the previous view as `Err(self)`.
    ///
    /// ```
    /// # use prefix_trie::*;
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
    /// assert!(map.view_mut().find_exact(&net!("192.168.0.0/21")).is_err());
    /// map.view_mut().find_exact(&net!("192.168.0.0/22")).unwrap().values_mut().for_each(|x| *x += 10);
    /// assert_eq!(
    ///     map.into_iter().collect::<Vec<_>>(),
    ///     vec![
    ///         (net!("192.168.0.0/20"), 1),
    ///         (net!("192.168.0.0/22"), 12),
    ///         (net!("192.168.0.0/24"), 13),
    ///         (net!("192.168.2.0/23"), 14),
    ///         (net!("192.168.4.0/22"), 5),
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn find_exact(self, prefix: &P) -> Result<Self, Self> {
        let mut idx = self.idx;
        loop {
            match self.map.get_direction(idx, prefix) {
                Direction::Reached => {
                    return if self.map.table[idx].value.is_some() {
                        Ok(Self { map: self.map, idx })
                    } else {
                        Err(self)
                    }
                }
                Direction::Enter { next, .. } => idx = next,
                Direction::Missing => return Err(self),
            }
        }
    }

    /// Find the longest match of `prefix`, returning a new view that points to that node. Only
    /// the given view is searched. If the prefix is not present in the view pointed to by
    /// `self`, the function returns the previous view as `Err(self)`.
    ///
    /// Only views to nodes that are present in the map are returned, not to branching nodes.
    ///
    /// ```
    /// # use prefix_trie::*;
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
    /// map.view_mut().find_lpm(&net!("192.168.0.0/22")).unwrap().values_mut().for_each(|x| *x += 10);
    /// map.view_mut().find_lpm(&net!("192.168.0.0/23")).unwrap().values_mut().for_each(|x| *x += 100);
    /// assert_eq!(
    ///     map.into_iter().collect::<Vec<_>>(),
    ///     vec![
    ///         (net!("192.168.0.0/20"), 1),
    ///         (net!("192.168.0.0/22"), 112),
    ///         (net!("192.168.0.0/24"), 113),
    ///         (net!("192.168.2.0/23"), 114),
    ///         (net!("192.168.4.0/22"), 5),
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn find_lpm(self, prefix: &P) -> Result<Self, Self> {
        let mut idx = self.idx;
        let mut best_match = None;
        loop {
            if self.map.table[idx].value.is_some() {
                best_match = Some(idx);
            }
            match self.map.get_direction(idx, prefix) {
                Direction::Enter { next, .. } => idx = next,
                _ => {
                    return if let Some(idx) = best_match {
                        Ok(Self { map: self.map, idx })
                    } else {
                        Err(self)
                    }
                }
            }
        }
    }
}

impl<'a, P, T> TrieViewMut<'a, P, T> {
    /// Iterate over all elements in the given view (including the element itself), in
    /// lexicographic order.
    pub fn iter(&self) -> Iter<'_, P, T> {
        Iter {
            map: self.map,
            nodes: vec![self.idx],
        }
    }

    /// Iterate over all elements in the given view (including the element itself), in
    /// lexicographic order, with a mutable reference to the value.
    pub fn iter_mut(&mut self) -> IterMut<'_, P, T> {
        IterMut {
            map: self.map,
            nodes: vec![self.idx],
        }
    }

    /// Iterate over all keys in the given view (including the element itself), in lexicographic
    /// order.
    pub fn keys(&self) -> Keys<'_, P, T> {
        Keys { inner: self.iter() }
    }

    /// Iterate over all values in the given view (including the element itself), in lexicographic
    /// order.
    pub fn values(&self) -> Values<'_, P, T> {
        Values { inner: self.iter() }
    }

    /// Iterate over mutable references to all values in the given view (including the element
    /// itself), in lexicographic order.
    pub fn values_mut(&mut self) -> ValuesMut<'_, P, T> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }

    /// Return an immutable view of the current subtrie.
    pub fn view(&self) -> TrieView<'_, P, T> {
        TrieView {
            map: self.map,
            idx: self.idx,
        }
    }

    /// Get a reference to the prefix that is currently pointed at. This prefix might not exist
    /// explicitly in the map/set, but may be used as a branching node (or when you call
    /// `remove_keep_tree`).
    pub fn prefix(&self) -> &P {
        &self.map.table[self.idx].prefix
    }

    /// Get a reference to the value at the root of the current view. This function may return
    /// `None` if `self` is pointing at a branching node.
    pub fn value(&self) -> Option<&T> {
        self.map.table[self.idx].value.as_ref()
    }

    /// Get a mutable reference to the value at the root of the current view. This function may
    /// return `None` if `self` is pointing at a branching node.
    pub fn value_mut(&mut self) -> Option<&mut T> {
        self.map.table[self.idx].value.as_mut()
    }

    /// Get a reference to both the prefix and the value. This function may return `None` if either
    /// `self` is pointing at a branching node.
    pub fn prefix_value(&self) -> Option<(&P, &T)> {
        let x = &self.map.table[self.idx];
        Some((&x.prefix, x.value.as_ref()?))
    }

    /// Get a reference to both the prefix and the value (the latter is mutable). This function may
    /// return `None` if either `self` is pointing at a branching node.
    pub fn prefix_value_mut(&mut self) -> Option<(&P, &mut T)> {
        let x = &mut self.map.table[self.idx];
        Some((&x.prefix, x.value.as_mut()?))
    }

    /// Remove the element at the current position of the view. The tree structure is not modified
    /// (similar to calling [`PrefixMap::remove_keep_tree`].)
    ///
    /// ```
    /// # use prefix_trie::*;
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
    /// let mut view = map.view_mut_at(&net!("192.168.0.0/22")).unwrap();
    /// assert_eq!(view.remove(), Some(2));
    /// assert_eq!(
    ///     view.iter().collect::<Vec<_>>(),
    ///     vec![
    ///         (&net!("192.168.0.0/24"), &3),
    ///         (&net!("192.168.2.0/23"), &4),
    ///     ]
    /// );
    /// assert_eq!(
    ///     map.into_iter().collect::<Vec<_>>(),
    ///     vec![
    ///         (net!("192.168.0.0/20"), 1),
    ///         (net!("192.168.0.0/24"), 3),
    ///         (net!("192.168.2.0/23"), 4),
    ///         (net!("192.168.4.0/22"), 5),
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn remove(&mut self) -> Option<T> {
        self.map.table[self.idx].value.take()
    }

    /// Insert an element at the current position of the view. The function returns the old value
    ///
    /// ```
    /// # use prefix_trie::*;
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
    /// let mut view = map.view_mut_at(&net!("192.168.0.0/22")).unwrap();
    /// assert_eq!(view.insert(22), Some(2));
    /// assert_eq!(
    ///     view.iter().collect::<Vec<_>>(),
    ///     vec![
    ///         (&net!("192.168.0.0/22"), &22),
    ///         (&net!("192.168.0.0/24"), &3),
    ///         (&net!("192.168.2.0/23"), &4),
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn insert(&mut self, value: T) -> Option<T> {
        self.map.table[self.idx].value.replace(value)
    }

    /// Get the left branch at the current view. The right branch contains all prefix that are
    /// contained within `self.prefix()`, and for which the next bit is set to 0. If the node has no
    /// children to the left, the function will return the previous view as `Err(self)`.
    pub fn left(self) -> Result<Self, Self> {
        if let Some(idx) = self.map.table[self.idx].left {
            Ok(Self { map: self.map, idx })
        } else {
            Err(self)
        }
    }

    /// Get the right branch at the current view. The right branch contains all prefix that are
    /// contained within `self.prefix()`, and for which the next bit is set to 1. If the node has no
    /// children to the right, the function will return the previous view as `Err(self)`.
    pub fn right(self) -> Result<Self, Self> {
        if let Some(idx) = self.map.table[self.idx].right {
            Ok(Self { map: self.map, idx })
        } else {
            Err(self)
        }
    }

    /// Returns `True` whether `self` has children to the left.
    pub fn has_left(&self) -> bool {
        self.map.table[self.idx].left.is_some()
    }

    /// Returns `True` whether `self` has children to the right.
    pub fn has_right(&self) -> bool {
        self.map.table[self.idx].right.is_some()
    }

    /// Split `self` into two views, one pointing to the left and one pointing to the right child.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::Ipv4Net>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map: PrefixMap<ipnet::Ipv4Net, usize> = PrefixMap::from_iter([
    ///     (net!("192.168.0.0/21"), 1),
    ///     (net!("192.168.0.0/22"), 2),
    ///     (net!("192.168.0.0/24"), 3),
    ///     (net!("192.168.2.0/23"), 4),
    ///     (net!("192.168.4.0/22"), 5),
    /// ]);
    /// let view = map.view_mut_at(&net!("192.168.0.0/21")).unwrap();
    /// assert!(view.has_left());
    /// assert!(view.has_right());
    /// let (Some(left), Some(right)) = view.split() else { unreachable!() };
    /// assert_eq!(
    ///     left.iter().collect::<Vec<_>>(),
    ///     vec![
    ///         (&net!("192.168.0.0/22"), &2),
    ///         (&net!("192.168.0.0/24"), &3),
    ///         (&net!("192.168.2.0/23"), &4),
    ///     ],
    /// );
    /// assert_eq!(
    ///     right.iter().collect::<Vec<_>>(),
    ///     vec![(&net!("192.168.4.0/22"), &5)],
    /// );
    /// # }
    /// ```
    pub fn split(self) -> (Option<Self>, Option<Self>) {
        let left = self.map.table[self.idx].left;
        let right = self.map.table[self.idx].right;

        let map_1 = self.map;
        let map_2: &'a mut PrefixMap<P, T>;
        // Safety: the view can only access its own elements! Therefore, splitting the view up into
        // two does not create aliasing.
        unsafe {
            map_2 = &mut *(map_1 as *mut PrefixMap<P, T>);
        }
        (
            left.map(|idx| Self { map: map_1, idx }),
            right.map(|idx| Self { map: map_2, idx }),
        )
    }
}

impl<'a, P, T> IntoIterator for TrieViewMut<'a, P, T> {
    type Item = (&'a P, &'a mut T);
    type IntoIter = IterMut<'a, P, T>;

    fn into_iter(self) -> Self::IntoIter {
        IterMut {
            map: self.map,
            nodes: vec![self.idx],
        }
    }
}

mod difference;
mod intersection;
mod union;
pub use difference::{
    CoveringDifference, CoveringDifferenceMut, Difference, DifferenceItem, DifferenceMut,
    DifferenceMutItem,
};
pub use intersection::{Intersection, IntersectionMut};
pub use union::{Union, UnionItem, UnionMut};
