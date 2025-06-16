//! Module that contains the implementation for the iterators

use either::{Left, Right};

use crate::joint::JointPrefix;
use crate::trieview::AsView;

use super::JointPrefixMap;

/// An iterator over all entries of a [`JointPrefixMap`] in lexicographic order.
pub struct Iter<'a, P: JointPrefix, T> {
    pub(crate) i1: Option<crate::map::Iter<'a, P::P1, T>>,
    pub(crate) i2: Option<crate::map::Iter<'a, P::P2, T>>,
}

impl<P: JointPrefix, T> Default for Iter<'_, P, T> {
    fn default() -> Self {
        Self { i1: None, i2: None }
    }
}

impl<P: JointPrefix, T> Clone for Iter<'_, P, T> {
    fn clone(&self) -> Self {
        Self {
            i1: self.i1.clone(),
            i2: self.i2.clone(),
        }
    }
}

impl<'a, P: JointPrefix, T> Iterator for Iter<'a, P, T> {
    type Item = (P, &'a T);

    fn next(&mut self) -> Option<(P, &'a T)> {
        if let Some(i1) = self.i1.as_mut() {
            if let Some((p, t)) = i1.next() {
                return Some((P::from_p1(p), t));
            }
            // iterator 1 is empty
            self.i1 = None;
        }
        if let Some(i2) = self.i2.as_mut() {
            if let Some((p, t)) = i2.next() {
                return Some((P::from_p2(p), t));
            }
            // iterator 1 is empty
            self.i2 = None;
        }
        None
    }
}

/// An iterator over all prefixes of a [`JointPrefixMap`] in lexicographic order.
#[derive(Clone, Default)]
pub struct Keys<'a, P: JointPrefix, T> {
    pub(crate) inner: Iter<'a, P, T>,
}

impl<P: JointPrefix, T> Iterator for Keys<'_, P, T> {
    type Item = P;

    fn next(&mut self) -> Option<P> {
        self.inner.next().map(|(k, _)| k)
    }
}

/// An iterator over all values of a [`JointPrefixMap`] in lexicographic order of their associated
/// prefixes.
#[derive(Clone, Default)]
pub struct Values<'a, P: JointPrefix, T> {
    pub(crate) inner: Iter<'a, P, T>,
}

impl<'a, P: JointPrefix, T> Iterator for Values<'a, P, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.inner.next().map(|(_, v)| v)
    }
}

/// An iterator over all owned entries of a [`JointPrefixMap`] in lexicographic order.
#[derive(Clone)]
pub struct IntoIter<P: JointPrefix, T> {
    pub(crate) i1: Option<crate::map::IntoIter<P::P1, T>>,
    pub(crate) i2: Option<crate::map::IntoIter<P::P2, T>>,
}

impl<P: JointPrefix, T> Iterator for IntoIter<P, T> {
    type Item = (P, T);

    fn next(&mut self) -> Option<(P, T)> {
        if let Some(i1) = self.i1.as_mut() {
            if let Some((p, t)) = i1.next() {
                return Some((P::from_p1(&p), t));
            }
            // iterator 1 is empty
            self.i1 = None;
        }
        if let Some(i2) = self.i2.as_mut() {
            if let Some((p, t)) = i2.next() {
                return Some((P::from_p2(&p), t));
            }
            // iterator 1 is empty
            self.i2 = None;
        }
        None
    }
}

/// An iterator over all prefixes of a [`JointPrefixMap`] in lexicographic order.
#[derive(Clone)]
pub struct IntoKeys<P: JointPrefix, T> {
    inner: IntoIter<P, T>,
}

impl<P: JointPrefix, T> Iterator for IntoKeys<P, T> {
    type Item = P;

    fn next(&mut self) -> Option<P> {
        self.inner.next().map(|(k, _)| k)
    }
}

/// An iterator over all values of a [`JointPrefixMap`] in lexicographic order of their associated
/// prefix.
#[derive(Clone)]
pub struct IntoValues<P: JointPrefix, T> {
    inner: IntoIter<P, T>,
}

impl<P: JointPrefix, T> Iterator for IntoValues<P, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.inner.next().map(|(_, v)| v)
    }
}

impl<P: JointPrefix, T> IntoIterator for JointPrefixMap<P, T> {
    type Item = (P, T);

    type IntoIter = IntoIter<P, T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            i1: Some(self.t1.into_iter()),
            i2: Some(self.t2.into_iter()),
        }
    }
}

impl<'a, P: JointPrefix, T> IntoIterator for &'a JointPrefixMap<P, T> {
    type Item = (P, &'a T);

    type IntoIter = Iter<'a, P, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            i1: Some(self.t1.iter()),
            i2: Some(self.t2.iter()),
        }
    }
}

/// A mutable iterator over a [`JointPrefixMap`]. This iterator yields elements in lexicographic order of
/// their associated prefix.
pub struct IterMut<'a, P: JointPrefix, T> {
    pub(super) i1: Option<crate::map::IterMut<'a, P::P1, T>>,
    pub(super) i2: Option<crate::map::IterMut<'a, P::P2, T>>,
}

impl<P: JointPrefix, T> Default for IterMut<'_, P, T> {
    fn default() -> Self {
        Self { i1: None, i2: None }
    }
}

impl<'a, P: JointPrefix, T> Iterator for IterMut<'a, P, T> {
    type Item = (P, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(i1) = self.i1.as_mut() {
            if let Some((p, t)) = i1.next() {
                return Some((P::from_p1(p), t));
            }
            // iterator 1 is empty
            self.i1 = None;
        }
        if let Some(i2) = self.i2.as_mut() {
            if let Some((p, t)) = i2.next() {
                return Some((P::from_p2(p), t));
            }
            // iterator 1 is empty
            self.i2 = None;
        }
        None
    }
}

/// A mutable iterator over values of [`JointPrefixMap`]. This iterator yields elements in
/// lexicographic order.
#[derive(Default)]
pub struct ValuesMut<'a, P: JointPrefix, T> {
    // # Safety
    // You must ensure that there only ever exists one such iterator for each tree. You may create
    // multiple such iterators for the same tree if you start with distinct starting nodes! This
    // ensures that any one iteration will never yield elements of the other iterator.
    pub(crate) inner: IterMut<'a, P, T>,
}

impl<'a, P: JointPrefix, T> Iterator for ValuesMut<'a, P, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
}

impl<P: JointPrefix, T> JointPrefixMap<P, T> {
    /// An iterator visiting all key-value pairs in lexicographic order. The iterator element type
    /// is `(&P, &T)`. Elements of the first prefix are yielded before those of the second prefix.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// pm.insert("2001::1:0:0/97".parse()?, 6);
    /// pm.insert("2001::1:0:0/96".parse()?, 7);
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
    ///         ("2001::1:0:0/96".parse()?, &7),
    ///         ("2001::1:0:0/97".parse()?, &6),
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
            i1: Some(self.t1.iter_mut()),
            i2: Some(self.t2.iter_mut()),
        }
    }

    /// An iterator visiting all keys in lexicographic order. The iterator element type is
    /// `&P`. Elements of the first prefix are yielded before those of the second one.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// pm.insert("2001::1:0:0/97".parse()?, 6);
    /// pm.insert("2001::1:0:0/96".parse()?, 7);
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
    ///         "2001::1:0:0/96".parse()?,
    ///         "2001::1:0:0/97".parse()?,
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
            inner: self.into_iter(),
        }
    }

    /// An iterator visiting all values in lexicographic order. The iterator element type is
    /// `&P`. Elements of the first prefix are yielded before those of the second one.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
    /// pm.insert("2001::1:0:0/97".parse()?, 6);
    /// pm.insert("2001::1:0:0/96".parse()?, 7);
    /// pm.insert("192.168.0.0/22".parse()?, 1);
    /// pm.insert("192.168.0.0/23".parse()?, 2);
    /// pm.insert("192.168.2.0/23".parse()?, 3);
    /// pm.insert("192.168.0.0/24".parse()?, 4);
    /// pm.insert("192.168.2.0/24".parse()?, 5);
    /// assert_eq!(pm.values().collect::<Vec<_>>(), vec![&1, &2, &4, &3, &5, &7, &6]);
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
            inner: self.into_iter(),
        }
    }

    /// Get a mutable iterator over all values. The order of this iterator is lexicographic.
    pub fn values_mut(&mut self) -> ValuesMut<'_, P, T> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }
}

impl<P: JointPrefix, T> JointPrefixMap<P, T> {
    /// Get an iterator over the node itself and all children. All elements returned have a prefix
    /// that is contained within `prefix` itself (or are the same). The iterator yields references
    /// to both keys and values, i.e., type `(&'a P, &'a T)`. The iterator yields elements in
    /// lexicographic order.
    ///
    /// **Note**: Consider using [`crate::AsView::view_at`] as an alternative.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
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
        match prefix.p1_or_p2_ref() {
            Left(p1) => Iter {
                i1: Some(self.t1.children(p1)),
                i2: None,
            },
            Right(p2) => Iter {
                i1: None,
                i2: Some(self.t2.children(p2)),
            },
        }
    }

    /// Get an iterator of mutable references of the node itself and all its children. All elements
    /// returned have a prefix that is contained within `prefix` itself (or are the same). The
    /// iterator yields references to the keys, and mutable references to the values, i.e., type
    /// `(&'a P, &'a mut T)`. The iterator yields elements in lexicographic order.
    ///
    /// **Note**: Consider using [`crate::AsViewMut::view_mut_at`] as an alternative.
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
        match prefix.p1_or_p2_ref() {
            Left(p1) => IterMut {
                i1: Some(self.t1.children_mut(p1)),
                i2: None,
            },
            Right(p2) => IterMut {
                i1: None,
                i2: Some(self.t2.children_mut(p2)),
            },
        }
    }

    /// Get an iterator over the node itself and all children with a value. All elements returned
    /// have a prefix that is contained within `prefix` itself (or are the same). This function will
    /// consume `self`, returning an iterator over all owned children.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: JointPrefixMap<ipnet::IpNet, _> = JointPrefixMap::new();
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
        match prefix.p1_or_p2_ref() {
            Left(p1) => IntoIter {
                i1: Some(self.t1.into_children(p1)),
                i2: None,
            },
            Right(p2) => IntoIter {
                i1: None,
                i2: Some(self.t2.into_children(p2)),
            },
        }
    }

    /// Iterate over the union of two joint prefix maps. This is roughly equivalent to calling
    /// `self.t1.view().union(&other.t1).chain(self.t2.view().union(&other.t2))`.
    ///
    /// If a prefix is present in both trees, the iterator will yield both elements. Otherwise, the
    /// iterator will yield the element of one map together with the longest prefix match in
    /// the other map. Elements are of type [`UnionItem`].
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # use prefix_trie::joint::map::UnionItem;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::IpNet>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map_a: JointPrefixMap<ipnet::IpNet, usize> = JointPrefixMap::from_iter([
    ///     (net!("2001::1:0:0/96"), 1),
    ///     (net!("192.168.0.0/22"), 2),
    ///     (net!("192.168.0.0/24"), 3),
    /// ]);
    /// let mut map_b: JointPrefixMap<ipnet::IpNet, &'static str> = JointPrefixMap::from_iter([
    ///     (net!("192.168.0.0/22"), "a"),
    ///     (net!("192.168.0.0/23"), "b"),
    /// ]);
    /// assert_eq!(
    ///     map_a.union(&map_b).collect::<Vec<_>>(),
    ///     vec![
    ///         UnionItem::Both{
    ///             prefix: net!("192.168.0.0/22"),
    ///             left: &2,
    ///             right: &"a",
    ///         },
    ///         UnionItem::Right{
    ///             prefix: net!("192.168.0.0/23"),
    ///             left: Some((net!("192.168.0.0/22"), &2)),
    ///             right: &"b",
    ///         },
    ///         UnionItem::Left{
    ///             prefix: net!("192.168.0.0/24"),
    ///             left: &3,
    ///             right: Some((net!("192.168.0.0/23"), &"b")),
    ///         },
    ///         UnionItem::Left{
    ///             prefix: net!("2001::1:0:0/96"),
    ///             left: &1,
    ///             right: None,
    ///         },
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn union<'a, R>(&'a self, other: &'a JointPrefixMap<P, R>) -> Union<'a, P, T, R> {
        Union {
            i1: Some(self.t1.view().union(&other.t1)),
            i2: Some(self.t2.view().union(&other.t2)),
        }
    }

    /// Iterate over the intersection of two joint prefix maps. This is roughly equivalent to
    /// calling `self.t1.view().intersection(&other.t1).chain(self.t2.view().intersection(&other.t2))`.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::IpNet>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map_a: JointPrefixMap<ipnet::IpNet, usize> = JointPrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), 1),
    ///     (net!("192.168.0.0/22"), 2),
    ///     (net!("192.168.0.0/24"), 3),
    ///     (net!("192.168.2.0/23"), 4),
    ///     (net!("2001::1:0:0/96"), 5),
    ///     (net!("2001::1:0:0/97"), 6),
    /// ]);
    /// let mut map_b: JointPrefixMap<ipnet::IpNet, &'static str> = JointPrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), "a"),
    ///     (net!("192.168.0.0/22"), "b"),
    ///     (net!("192.168.0.0/23"), "c"),
    ///     (net!("192.168.0.0/24"), "d"),
    ///     (net!("192.168.2.0/24"), "e"),
    ///     (net!("2001::1:0:0/96"), "f"),
    ///     (net!("2001::0:0:0/97"), "g"),
    /// ]);
    /// assert_eq!(
    ///     map_a.intersection(&map_b).collect::<Vec<_>>(),
    ///     vec![
    ///         (net!("192.168.0.0/20"), &1, &"a"),
    ///         (net!("192.168.0.0/22"), &2, &"b"),
    ///         (net!("192.168.0.0/24"), &3, &"d"),
    ///         (net!("2001::1:0:0/96"), &5, &"f"),
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn intersection<'a, R>(
        &'a self,
        other: &'a JointPrefixMap<P, R>,
    ) -> Intersection<'a, P, T, R> {
        Intersection {
            i1: Some(self.t1.view().intersection(&other.t1)),
            i2: Some(self.t2.view().intersection(&other.t2)),
        }
    }

    /// Iterate over the all elements in `self` that are not present in `other`. Each item will
    /// return a reference to the prefix and value in `self`, as well as the longest prefix match of
    /// `other`.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # use prefix_trie::joint::map::DifferenceItem;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::IpNet>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map_a: JointPrefixMap<ipnet::IpNet, usize> = JointPrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), 1),
    ///     (net!("192.168.0.0/22"), 2),
    ///     (net!("192.168.0.0/24"), 3),
    ///     (net!("192.168.2.0/23"), 4),
    ///     (net!("2001::1:0:0/96"), 5),
    ///     (net!("2001::1:0:0/97"), 6),
    /// ]);
    /// let mut map_b: JointPrefixMap<ipnet::IpNet, &'static str> = JointPrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), "a"),
    ///     (net!("192.168.0.0/22"), "b"),
    ///     (net!("192.168.0.0/23"), "c"),
    ///     (net!("192.168.2.0/24"), "d"),
    ///     (net!("2001::1:0:0/96"), "e"),
    /// ]);
    /// assert_eq!(
    ///     map_a.difference(&map_b).collect::<Vec<_>>(),
    ///     vec![
    ///         DifferenceItem { prefix: net!("192.168.0.0/24"), value: &3, right: Some((net!("192.168.0.0/23"), &"c"))},
    ///         DifferenceItem { prefix: net!("192.168.2.0/23"), value: &4, right: Some((net!("192.168.0.0/22"), &"b"))},
    ///         DifferenceItem { prefix: net!("2001::1:0:0/97"), value: &6, right: Some((net!("2001::1:0:0/96"), &"e"))},
    ///     ]
    /// );
    /// # }
    /// ```
    pub fn difference<'a, R>(&'a self, other: &'a JointPrefixMap<P, R>) -> Difference<'a, P, T, R> {
        Difference {
            i1: Some(self.t1.view().difference(&other.t1)),
            i2: Some(self.t2.view().difference(&other.t2)),
        }
    }

    /// Iterate over the all elements in `self` that are not covered by `other`.
    ///
    /// ```
    /// # use prefix_trie::joint::*;
    /// # use prefix_trie::joint::map::DifferenceItem;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => {$x.parse::<ipnet::IpNet>().unwrap()}; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map_a: JointPrefixMap<ipnet::IpNet, usize> = JointPrefixMap::from_iter([
    ///     (net!("192.168.0.0/20"), 1),
    ///     (net!("192.168.0.0/22"), 2),
    ///     (net!("192.168.0.0/24"), 3),
    ///     (net!("192.168.2.0/23"), 4),
    ///     (net!("2001::0:0:0/95"), 5),
    ///     (net!("2001::1:0:0/96"), 6),
    ///     (net!("2001::1:0:0/97"), 7),
    /// ]);
    /// let mut map_b: JointPrefixMap<ipnet::IpNet, &'static str> = JointPrefixMap::from_iter([
    ///     (net!("192.168.0.0/21"), "a"),
    ///     (net!("192.168.0.0/22"), "b"),
    ///     (net!("192.168.0.0/23"), "c"),
    ///     (net!("192.168.2.0/24"), "d"),
    ///     (net!("2001::1:0:0/96"), "e"),
    /// ]);
    /// assert_eq!(
    ///     map_a.covering_difference(&map_b).collect::<Vec<_>>(),
    ///     vec![(net!("192.168.0.0/20"), &1), (net!("2001::0:0:0/95"), &5)]
    /// );
    /// # }
    /// ```
    pub fn covering_difference<'a, R>(
        &'a self,
        other: &'a JointPrefixMap<P, R>,
    ) -> CoveringDifference<'a, P, T, R> {
        CoveringDifference {
            i1: Some(self.t1.view().covering_difference(&other.t1)),
            i2: Some(self.t2.view().covering_difference(&other.t2)),
        }
    }
}

impl<P: JointPrefix, T> FromIterator<(P, T)> for JointPrefixMap<P, T> {
    fn from_iter<I: IntoIterator<Item = (P, T)>>(iter: I) -> Self {
        let mut map = Self::new();
        iter.into_iter().for_each(|(p, v)| {
            map.insert(p, v);
        });
        map
    }
}

/// An iterator that yields all items in a `JointPrefixMap` that covers a given prefix (including
/// the prefix itself if preseint). See [`crate::joint::JointPrefixMap::cover`] for how to create
/// this iterator.
pub enum Cover<'a, 'p, P: JointPrefix, T> {
    /// Cover of the first prefix variant
    P1(crate::map::Cover<'a, 'p, P::P1, T>),
    /// Cover of the second prefix variant
    P2(crate::map::Cover<'a, 'p, P::P2, T>),
}

impl<'a, P: JointPrefix, T> Iterator for Cover<'a, '_, P, T> {
    type Item = (P, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Cover::P1(cover) => cover.next().map(|(p, t)| (P::from_p1(p), t)),
            Cover::P2(cover) => cover.next().map(|(p, t)| (P::from_p2(p), t)),
        }
    }
}

/// An iterator that yields all keys (prefixes) in a `JointPrefixMap` that covers a given prefix
/// (including the prefix itself if preseint). See [`crate::joint::JointPrefixMap::cover_keys`] for
/// how to create this iterator.
pub struct CoverKeys<'a, 'p, P: JointPrefix, T>(pub(crate) Cover<'a, 'p, P, T>);

impl<P: JointPrefix, T> Iterator for CoverKeys<'_, '_, P, T> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(p, _)| p)
    }
}

/// An iterator that yields all values in a `JointPrefixMap` that covers a given prefix (including
/// the prefix itself if preseint). See [`crate::joint::JointPrefixMap::cover_values`] for how to
/// create this iterator.
pub struct CoverValues<'a, 'p, P: JointPrefix, T>(pub(super) Cover<'a, 'p, P, T>);

impl<'a, P: JointPrefix, T> Iterator for CoverValues<'a, '_, P, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, t)| t)
    }
}

/// An iterator over the union of two [`JointPrefixMap`]s. The iterator yields first prefixes of
/// `P1`, followed by those of `P2`.
pub struct Union<'a, P: JointPrefix, L, R> {
    i1: Option<crate::trieview::Union<'a, P::P1, L, R>>,
    i2: Option<crate::trieview::Union<'a, P::P2, L, R>>,
}

impl<'a, P: JointPrefix, L, R> Iterator for Union<'a, P, L, R> {
    type Item = UnionItem<'a, P, L, R>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(i1) = self.i1.as_mut() {
            if let Some(next) = i1.next() {
                return Some(UnionItem::from_p1(next));
            }
            self.i1 = None;
        }
        if let Some(i2) = self.i2.as_mut() {
            if let Some(next) = i2.next() {
                return Some(UnionItem::from_p2(next));
            }
            self.i2 = None;
        }
        None
    }
}

/// An item of the [`Union`] iterator (over a [`JointPrefixMap`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]

pub enum UnionItem<'a, P, L, R> {
    /// The prefix is only present in the left TrieView (`self`).
    Left {
        /// The prefix of the element.
        prefix: P,
        /// The value of the element in the left TrieView (`self`).
        left: &'a L,
        /// The longest prefix match in the right TrieView (`other`).
        right: Option<(P, &'a R)>,
    },

    /// The prefix is only present in the right TrieView (`other`).
    Right {
        /// The prefix of the element.
        prefix: P,
        /// The longest prefix match in the left TrieView (`self`).
        left: Option<(P, &'a L)>,
        /// The value of the element in the right TrieView (`other`).
        right: &'a R,
    },

    /// The prefix is only present in the right TrieView (`other`).
    Both {
        /// The prefix of the element.
        prefix: P,
        /// The value of the element in the left TrieView (`self`).
        left: &'a L,
        /// The value of the element in the right TrieView (`other`).
        right: &'a R,
    },
}

impl<'a, P, L, R> UnionItem<'a, P, L, R> {
    /// Get the prefix of the current element (in the exact match).
    pub fn prefix(&self) -> &P {
        match self {
            UnionItem::Left { prefix, .. }
            | UnionItem::Right { prefix, .. }
            | UnionItem::Both { prefix, .. } => prefix,
        }
    }

    /// Get the element in both the left and right map, but only if they are both present. By
    /// doing `a.union(b).filter_map(|x| x.both)`, you get an iterator that yields only elements
    /// that are present in both tries.
    pub fn both(&self) -> Option<(&P, &'a L, &'a R)> {
        match self {
            UnionItem::Left { .. } | UnionItem::Right { .. } => None,
            UnionItem::Both {
                prefix,
                left,
                right,
            } => Some((prefix, left, right)),
        }
    }

    /// Get the value of the left item (`self`). This either returns the exact match or the
    /// longest-prefix match.
    pub fn left(&self) -> Option<(&P, &'a L)> {
        match self {
            UnionItem::Right { left, .. } => left.as_ref().map(|(p, l)| (p, *l)),
            UnionItem::Left { prefix, left, .. } | UnionItem::Both { prefix, left, .. } => {
                Some((prefix, left))
            }
        }
    }

    /// Get the value of the right item (`other`). This either returns the exact match or the
    /// longest-prefix match.
    pub fn right(&self) -> Option<(&P, &'a R)> {
        match self {
            UnionItem::Left { right, .. } => right.as_ref().map(|(p, r)| (p, *r)),
            UnionItem::Right { prefix, right, .. } | UnionItem::Both { prefix, right, .. } => {
                Some((prefix, right))
            }
        }
    }
}

impl<'a, P: JointPrefix, L, R> UnionItem<'a, P, L, R> {
    fn from_p1(value: crate::trieview::UnionItem<'a, P::P1, L, R>) -> Self {
        match value {
            crate::trieview::UnionItem::Left {
                prefix,
                left,
                right,
            } => UnionItem::Left {
                prefix: P::from_p1(prefix),
                left,
                right: right.map(|(p, r)| (P::from_p1(p), r)),
            },
            crate::trieview::UnionItem::Right {
                prefix,
                left,
                right,
            } => UnionItem::Right {
                prefix: P::from_p1(prefix),
                left: left.map(|(p, l)| (P::from_p1(p), l)),
                right,
            },
            crate::trieview::UnionItem::Both {
                prefix,
                left,
                right,
            } => UnionItem::Both {
                prefix: P::from_p1(prefix),
                left,
                right,
            },
        }
    }

    fn from_p2(value: crate::trieview::UnionItem<'a, P::P2, L, R>) -> Self {
        match value {
            crate::trieview::UnionItem::Left {
                prefix,
                left,
                right,
            } => UnionItem::Left {
                prefix: P::from_p2(prefix),
                left,
                right: right.map(|(p, r)| (P::from_p2(p), r)),
            },
            crate::trieview::UnionItem::Right {
                prefix,
                left,
                right,
            } => UnionItem::Right {
                prefix: P::from_p2(prefix),
                left: left.map(|(p, l)| (P::from_p2(p), l)),
                right,
            },
            crate::trieview::UnionItem::Both {
                prefix,
                left,
                right,
            } => UnionItem::Both {
                prefix: P::from_p2(prefix),
                left,
                right,
            },
        }
    }
}

/// An iterator over the intersection of two [`JointPrefixMap`]s. The iterator yields first prefixes
/// of `P1`, followed by those of `P2`.
pub struct Intersection<'a, P: JointPrefix, L, R> {
    i1: Option<crate::trieview::Intersection<'a, P::P1, L, R>>,
    i2: Option<crate::trieview::Intersection<'a, P::P2, L, R>>,
}

impl<'a, P: JointPrefix, L, R> Iterator for Intersection<'a, P, L, R> {
    type Item = (P, &'a L, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(i1) = self.i1.as_mut() {
            if let Some((p, l, r)) = i1.next() {
                return Some((P::from_p1(p), l, r));
            }
            self.i1 = None;
        }
        if let Some(i2) = self.i2.as_mut() {
            if let Some((p, l, r)) = i2.next() {
                return Some((P::from_p2(p), l, r));
            }
            self.i2 = None;
        }
        None
    }
}

/// An iterator over the difference of two [`JointPrefixMap`]s, i.e., prefixes that are in `self`
/// but not in `other`. The iterator yields first prefixes of `P1`, followed by those of `P2`.
pub struct Difference<'a, P: JointPrefix, L, R> {
    i1: Option<crate::trieview::Difference<'a, P::P1, L, R>>,
    i2: Option<crate::trieview::Difference<'a, P::P2, L, R>>,
}

impl<'a, P: JointPrefix, L, R> Iterator for Difference<'a, P, L, R> {
    type Item = DifferenceItem<'a, P, L, R>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(i1) = self.i1.as_mut() {
            if let Some(next) = i1.next() {
                return Some(DifferenceItem::from_p1(next));
            }
            self.i1 = None;
        }
        if let Some(i2) = self.i2.as_mut() {
            if let Some(next) = i2.next() {
                return Some(DifferenceItem::from_p2(next));
            }
            self.i2 = None;
        }
        None
    }
}

/// An iterator over the covering difference of two [`JointPrefixMap`]s, i.e., prefixes of `self` that
/// are not covered by `other`. The iterator yields first prefixes of `P1`, followed by those of
/// `P2`.
pub struct CoveringDifference<'a, P: JointPrefix, L, R> {
    i1: Option<crate::trieview::CoveringDifference<'a, P::P1, L, R>>,
    i2: Option<crate::trieview::CoveringDifference<'a, P::P2, L, R>>,
}

impl<'a, P: JointPrefix, L, R> Iterator for CoveringDifference<'a, P, L, R> {
    type Item = (P, &'a L);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(i1) = self.i1.as_mut() {
            if let Some((p, l)) = i1.next() {
                return Some((P::from_p1(p), l));
            }
            self.i1 = None;
        }
        if let Some(i2) = self.i2.as_mut() {
            if let Some((p, l)) = i2.next() {
                return Some((P::from_p2(p), l));
            }
            self.i2 = None;
        }
        None
    }
}

/// An item of the [`Difference`] iterator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DifferenceItem<'a, P, L, R> {
    /// The prefix that is present in `self` but not in `other`.
    pub prefix: P,
    /// The value stored in `self`.
    pub value: &'a L,
    /// The longest-prefix-match that is present in `other`.
    pub right: Option<(P, &'a R)>,
}

impl<'a, P: JointPrefix, L, R> DifferenceItem<'a, P, L, R> {
    fn from_p1(value: crate::trieview::DifferenceItem<'a, P::P1, L, R>) -> Self {
        Self {
            prefix: P::from_p1(value.prefix),
            value: value.value,
            right: value.right.map(|(p, r)| (P::from_p1(p), r)),
        }
    }

    fn from_p2(value: crate::trieview::DifferenceItem<'a, P::P2, L, R>) -> Self {
        Self {
            prefix: P::from_p2(value.prefix),
            value: value.value,
            right: value.right.map(|(p, r)| (P::from_p2(p), r)),
        }
    }
}
