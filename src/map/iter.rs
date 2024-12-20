//! Module that contains the implementation for the iterators

use crate::*;

use super::Node;

/// An iterator over all entries of a [`PrefixMap`] in lexicographic order.
#[derive(Clone)]
pub struct Iter<'a, P, T> {
    pub(crate) map: &'a PrefixMap<P, T>,
    pub(crate) nodes: Vec<usize>,
}

impl<'a, P, T> Iterator for Iter<'a, P, T> {
    type Item = (&'a P, &'a T);

    fn next(&mut self) -> Option<(&'a P, &'a T)> {
        while let Some(cur) = self.nodes.pop() {
            let node = &self.map.table[cur];
            if let Some(right) = node.right {
                self.nodes.push(right);
            }
            if let Some(left) = node.left {
                self.nodes.push(left);
            }
            if let Some(v) = &node.value {
                return Some((&node.prefix, v));
            }
        }
        None
    }
}

/// An iterator over all prefixes of a [`PrefixMap`] in lexicographic order.
#[derive(Clone)]
pub struct Keys<'a, P, T> {
    pub(crate) inner: Iter<'a, P, T>,
}

impl<'a, P, T> Iterator for Keys<'a, P, T> {
    type Item = &'a P;

    fn next(&mut self) -> Option<&'a P> {
        self.inner.next().map(|(k, _)| k)
    }
}

/// An iterator over all values of a [`PrefixMap`] in lexicographic order of their associated
/// prefixes.
#[derive(Clone)]
pub struct Values<'a, P, T> {
    pub(crate) inner: Iter<'a, P, T>,
}

impl<'a, P, T> Iterator for Values<'a, P, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.inner.next().map(|(_, v)| v)
    }
}

/// An iterator over all owned entries of a [`PrefixMap`] in lexicographic order.
#[derive(Clone)]
pub struct IntoIter<P, T> {
    map: PrefixMap<P, T>,
    nodes: Vec<usize>,
}

impl<P: Prefix, T> Iterator for IntoIter<P, T> {
    type Item = (P, T);

    fn next(&mut self) -> Option<(P, T)> {
        while let Some(cur) = self.nodes.pop() {
            let node = &mut self.map.table[cur];
            if let Some(right) = node.right {
                self.nodes.push(right);
            }
            if let Some(left) = node.left {
                self.nodes.push(left);
            }
            if let Some(v) = node.value.take() {
                return Some((std::mem::replace(&mut node.prefix, P::zero()), v));
            }
        }
        None
    }
}

/// An iterator over all prefixes of a [`PrefixMap`] in lexicographic order.
#[derive(Clone)]
pub struct IntoKeys<P, T> {
    inner: IntoIter<P, T>,
}

impl<P: Prefix, T> Iterator for IntoKeys<P, T> {
    type Item = P;

    fn next(&mut self) -> Option<P> {
        self.inner.next().map(|(k, _)| k)
    }
}

/// An iterator over all values of a [`PrefixMap`] in lexicographic order of their associated
/// prefix.
#[derive(Clone)]
pub struct IntoValues<P, T> {
    inner: IntoIter<P, T>,
}

impl<P: Prefix, T> Iterator for IntoValues<P, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.inner.next().map(|(_, v)| v)
    }
}

impl<P: Prefix, T> IntoIterator for PrefixMap<P, T> {
    type Item = (P, T);

    type IntoIter = IntoIter<P, T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            map: self,
            nodes: vec![0],
        }
    }
}

impl<'a, P, T> IntoIterator for &'a PrefixMap<P, T> {
    type Item = (&'a P, &'a T);

    type IntoIter = Iter<'a, P, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            map: self,
            nodes: vec![0],
        }
    }
}

unsafe fn extend_lifetime_mut<'short, 'long, T: ?Sized>(v: &'short mut T) -> &'long mut T {
    std::mem::transmute(v)
}

/// A mutable iterator over a [`PrefixMap`]. This iterator yields elements in lexicographic order of
/// their associated prefix.
pub struct IterMut<'a, P, T> {
    pub(crate) map: &'a mut PrefixMap<P, T>,
    pub(crate) nodes: Vec<usize>,
}

impl<'a, P, T> Iterator for IterMut<'a, P, T> {
    type Item = (&'a P, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(cur) = self.nodes.pop() {
            let node: &'a mut Node<P, T>;
            // safety: map is a tree. Every node is visited exactly once during the iteration
            // (self.nodes is not public). Therefore, each in each iteration of this loop (also
            // between multiple calls to `next`), the index `cur` is different to any of the earlier
            // iterations. It is therefore safe to extend the lifetime of the elements to 'a (which
            // is the lifetime for which `self` has an exclusive reference over the map).
            unsafe {
                node = extend_lifetime_mut(&mut self.map.table[cur]);
            }
            if let Some(right) = node.right {
                self.nodes.push(right);
            }
            if let Some(left) = node.left {
                self.nodes.push(left);
            }
            if node.value.is_some() {
                let v = node.value.as_mut().unwrap();
                return Some((&node.prefix, v));
            }
        }
        None
    }
}

/// A mutable iterator over values of [`PrefixMap`]. This iterator yields elements in lexicographic
/// order.
pub struct ValuesMut<'a, P, T> {
    pub(crate) inner: IterMut<'a, P, T>,
}

impl<'a, P, T> Iterator for ValuesMut<'a, P, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
}

impl<P, T> PrefixMap<P, T> {
    /// An iterator visiting all key-value pairs in lexicographic order. The iterator element type
    /// is `(&P, &T)`.
    ///
    /// ```
    /// # use prefix_trie::*;
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
    ///         (&"192.168.0.0/22".parse()?, &1),
    ///         (&"192.168.0.0/23".parse()?, &2),
    ///         (&"192.168.0.0/24".parse()?, &4),
    ///         (&"192.168.2.0/23".parse()?, &3),
    ///         (&"192.168.2.0/24".parse()?, &5),
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
        IterMut {
            map: self,
            nodes: vec![0],
        }
    }

    /// An iterator visiting all keys in lexicographic order. The iterator element type is `&P`.
    ///
    /// ```
    /// # use prefix_trie::*;
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
    ///         &"192.168.0.0/22".parse()?,
    ///         &"192.168.0.0/23".parse()?,
    ///         &"192.168.0.0/24".parse()?,
    ///         &"192.168.2.0/23".parse()?,
    ///         &"192.168.2.0/24".parse()?,
    ///     ]
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn keys(&self) -> Keys<'_, P, T> {
        Keys { inner: self.iter() }
    }

    /// Creates a consuming iterator visiting all keys in lexicographic order. The iterator element
    /// type is `P`.
    #[inline(always)]
    pub fn into_keys(self) -> IntoKeys<P, T> {
        IntoKeys {
            inner: IntoIter {
                map: self,
                nodes: vec![0],
            },
        }
    }

    /// An iterator visiting all values in lexicographic order. The iterator element type is `&P`.
    ///
    /// ```
    /// # use prefix_trie::*;
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
        Values { inner: self.iter() }
    }

    /// Creates a consuming iterator visiting all values in lexicographic order. The iterator
    /// element type is `P`.
    #[inline(always)]
    pub fn into_values(self) -> IntoValues<P, T> {
        IntoValues {
            inner: IntoIter {
                map: self,
                nodes: vec![0],
            },
        }
    }

    /// Get a mutable iterator over all values. The order of this iterator is lexicographic.
    pub fn values_mut(&mut self) -> ValuesMut<'_, P, T> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }
}

impl<P, T> PrefixMap<P, T>
where
    P: Prefix,
{
    /// Get an iterator over the node itself and all children. All elements returned have a prefix
    /// that is contained within `prefix` itself (or are the same). The iterator yields references
    /// to both keys and values, i.e., type `(&'a P, &'a T)`. The iterator yields elements in
    /// lexicographic order.
    ///
    /// ```
    /// # use prefix_trie::*;
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
    ///         (&"192.168.0.0/23".parse()?, &2),
    ///         (&"192.168.0.0/24".parse()?, &4),
    ///     ]
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn children(&self, prefix: &P) -> Iter<'_, P, T> {
        // first, find the longest prefix containing `prefix`.
        let mut idx = 0;
        let mut cur_p = &self.table[idx].prefix;
        let nodes = loop {
            if cur_p.eq(prefix) {
                break vec![idx];
            }
            let right = to_right(cur_p, prefix);
            match self.get_child(idx, right) {
                Some(c) => {
                    cur_p = &self.table[c].prefix;
                    if cur_p.contains(prefix) {
                        // continue traversal
                        idx = c;
                    } else if prefix.contains(cur_p) {
                        break vec![c];
                    } else {
                        break vec![];
                    }
                }
                None => break vec![],
            }
        };
        Iter { map: self, nodes }
    }

    /// Get an iterator of mutable references of the node itself and all its children. All elements
    /// returned have a prefix that is contained within `prefix` itself (or are the same). The
    /// iterator yields references to the keys, and mutable references to the values, i.e., type
    /// `(&'a P, &'a mut T)`. The iterator yields elements in lexicographic order.
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
    pub fn children_mut(&mut self, prefix: &P) -> IterMut<'_, P, T> {
        // first, find the longest prefix containing `prefix`.
        let mut idx = 0;
        let mut cur_p = &self.table[idx].prefix;
        let nodes = loop {
            if cur_p.eq(prefix) {
                break vec![idx];
            }
            let right = to_right(cur_p, prefix);
            match self.get_child(idx, right) {
                Some(c) => {
                    cur_p = &self.table[c].prefix;
                    if cur_p.contains(prefix) {
                        // continue traversal
                        idx = c;
                    } else if prefix.contains(cur_p) {
                        break vec![c];
                    } else {
                        break vec![];
                    }
                }
                None => break vec![],
            }
        };
        IterMut { map: self, nodes }
    }

    /// Get an iterator over the node itself and all children with a value. All elements returned
    /// have a prefix that is contained within `prefix` itself (or are the same). This function will
    /// consume `self`, returning an iterator over all owned children.
    ///
    /// ```
    /// # use prefix_trie::*;
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
        // first, find the longest prefix containing `prefix`.
        let mut idx = 0;
        let mut cur_p = &self.table[idx].prefix;
        let nodes = loop {
            if cur_p.eq(prefix) {
                break vec![idx];
            }
            let right = to_right(cur_p, prefix);
            match self.get_child(idx, right) {
                Some(c) => {
                    cur_p = &self.table[c].prefix;
                    if cur_p.contains(prefix) {
                        // continue traversal
                        idx = c;
                    } else if prefix.contains(cur_p) {
                        break vec![c];
                    } else {
                        break vec![];
                    }
                }
                None => break vec![],
            }
        };
        IntoIter { map: self, nodes }
    }
}

impl<P, T> FromIterator<(P, T)> for PrefixMap<P, T>
where
    P: Prefix,
{
    fn from_iter<I: IntoIterator<Item = (P, T)>>(iter: I) -> Self {
        let mut map = Self::new();
        iter.into_iter().for_each(|(p, v)| {
            map.insert(p, v);
        });
        map
    }
}

/// An iterator that yields all items in a `PrefixMap` that covers a given prefix (including the
/// prefix itself if preseint). See [`PrefixMap::cover`] for how to create this iterator.
pub struct Cover<'a, P, T> {
    pub(super) map: &'a PrefixMap<P, T>,
    pub(super) idx: Option<usize>,
    pub(super) prefix: &'a P,
}

impl<'a, P, T> Iterator for Cover<'a, P, T>
where
    P: Prefix,
{
    type Item = (&'a P, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        // check if self.idx is None. If so, then check if the first branch is present in the map
        if self.idx.is_none() {
            self.idx = Some(0);
            let entry = &self.map.table[0];
            if let Some(value) = entry.value.as_ref() {
                return Some((&entry.prefix, value));
            }
        }

        // if we reach here, then self.idx is not None!

        loop {
            let map::Direction::Enter { next, .. } =
                self.map.get_direction(self.idx.unwrap(), self.prefix)
            else {
                return None;
            };
            self.idx = Some(next);
            let entry = &self.map.table[next];
            if let Some(value) = entry.value.as_ref() {
                return Some((&entry.prefix, value));
            }
        }
    }
}

/// An iterator that yields all keys (prefixes) in a `PrefixMap` that covers a given prefix
/// (including the prefix itself if preseint). See [`PrefixMap::cover_keys`] for how to create this
/// iterator.
pub struct CoverKeys<'a, P, T>(pub(super) Cover<'a, P, T>);

impl<'a, P, T> Iterator for CoverKeys<'a, P, T>
where
    P: Prefix,
{
    type Item = &'a P;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(p, _)| p)
    }
}

/// An iterator that yields all values in a `PrefixMap` that covers a given prefix (including the
/// prefix itself if preseint). See [`PrefixMap::cover_values`] for how to create this iterator.
pub struct CoverValues<'a, P, T>(pub(super) Cover<'a, P, T>);

impl<'a, P, T> Iterator for CoverValues<'a, P, T>
where
    P: Prefix,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, t)| t)
    }
}
