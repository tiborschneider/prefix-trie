//! Module that contains the implementation for the iterators

use crate::*;

/// An iterator over all entries of a [`PrefixMap`] in lexicographic order.
#[derive(Clone)]
pub struct Iter<'a, P, T> {
    map: &'a PrefixMap<P, T>,
    nodes: Vec<usize>,
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
    map: &'a PrefixMap<P, T>,
    nodes: Vec<usize>,
}

impl<'a, P, T> Iterator for Keys<'a, P, T> {
    type Item = &'a P;

    fn next(&mut self) -> Option<&'a P> {
        while let Some(cur) = self.nodes.pop() {
            let node = &self.map.table[cur];
            if let Some(right) = node.right {
                self.nodes.push(right);
            }
            if let Some(left) = node.left {
                self.nodes.push(left);
            }
            if node.value.is_some() {
                return Some(&node.prefix);
            }
        }
        None
    }
}

/// An iterator over all values of a [`PrefixMap`] in lexicographic order of their associated
/// prefixes.
#[derive(Clone)]
pub struct Values<'a, P, T> {
    map: &'a PrefixMap<P, T>,
    nodes: Vec<usize>,
}

impl<'a, P, T> Iterator for Values<'a, P, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        while let Some(cur) = self.nodes.pop() {
            let node = &self.map.table[cur];
            if let Some(right) = node.right {
                self.nodes.push(right);
            }
            if let Some(left) = node.left {
                self.nodes.push(left);
            }
            if let Some(v) = node.value.as_ref() {
                return Some(v);
            }
        }
        None
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
#[derive(Clone, Debug)]
pub struct IntoKeys<P, T> {
    map: PrefixMap<P, T>,
    nodes: Vec<usize>,
}

impl<P: Prefix, T> Iterator for IntoKeys<P, T> {
    type Item = P;

    fn next(&mut self) -> Option<P> {
        while let Some(cur) = self.nodes.pop() {
            let node = &mut self.map.table[cur];
            if let Some(right) = node.right {
                self.nodes.push(right);
            }
            if let Some(left) = node.left {
                self.nodes.push(left);
            }
            if node.value.is_some() {
                return Some(std::mem::replace(&mut node.prefix, P::zero()));
            }
        }
        None
    }
}

/// An iterator over all values of a [`PrefixMap`] in lexicographic order of their associated
/// prefix.
#[derive(Clone)]
pub struct IntoValues<P, T> {
    map: PrefixMap<P, T>,
    nodes: Vec<usize>,
}

impl<P, T> Iterator for IntoValues<P, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        while let Some(cur) = self.nodes.pop() {
            let node = &mut self.map.table[cur];
            if let Some(right) = node.right {
                self.nodes.push(right);
            }
            if let Some(left) = node.left {
                self.nodes.push(left);
            }
            if let Some(v) = node.value.take() {
                return Some(v);
            }
        }
        None
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

impl<P, T> PrefixMap<P, T> {
    /// An iterator visiting all key-value pairs in lexicographic order. The iterator element type
    /// is `(&P, &T)`.
    #[inline(always)]
    pub fn iter(&self) -> Iter<'_, P, T> {
        self.into_iter()
    }

    /// An iterator visiting all keys in lexicographic order. The iterator element type is `&P`.
    #[inline(always)]
    pub fn keys(&self) -> Keys<'_, P, T> {
        Keys {
            map: self,
            nodes: vec![0],
        }
    }

    /// Creates a consuming iterator visiting all keys in lexicographic order. The iterator element
    /// type is `P`.
    #[inline(always)]
    pub fn into_keys(self) -> IntoKeys<P, T> {
        IntoKeys {
            map: self,
            nodes: vec![0],
        }
    }

    /// An iterator visiting all values in lexicographic order. The iterator element type is `&P`.
    #[inline(always)]
    pub fn values(&self) -> Values<'_, P, T> {
        Values {
            map: self,
            nodes: vec![0],
        }
    }

    /// Creates a consuming iterator visiting all values in lexicographic order. The iterator
    /// element type is `P`.
    #[inline(always)]
    pub fn into_values(self) -> IntoValues<P, T> {
        IntoValues {
            map: self,
            nodes: vec![0],
        }
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
