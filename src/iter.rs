//! Module that contains the implementation for the iterators

use crate::*;

/// An iterator over all entries of a [`PrefixMap`] in lexicographic order.
#[derive(Clone, Debug)]
pub struct Iter<'a, P, T> {
    nodes: Vec<&'a Node<P, T>>,
}

impl<'a, P, T> Iterator for Iter<'a, P, T> {
    type Item = (&'a P, &'a T);

    fn next(&mut self) -> Option<(&'a P, &'a T)> {
        while let Some(cur) = self.nodes.pop() {
            match cur {
                Node::Leaf { prefix, value } => {
                    if let Some(v) = value {
                        return Some((prefix, v));
                    }
                }
                Node::Single {
                    prefix,
                    value,
                    child,
                } => {
                    self.nodes.push(child.as_ref());
                    if let Some(v) = value {
                        return Some((prefix, v));
                    }
                }
                Node::Branch {
                    prefix,
                    value,
                    left,
                    right,
                } => {
                    self.nodes.push(right.as_ref());
                    self.nodes.push(left.as_ref());
                    if let Some(v) = value {
                        return Some((prefix, v));
                    }
                }
            }
        }
        None
    }
}

/// An iterator over all prefixes of a [`PrefixMap`] in lexicographic order.
#[derive(Clone, Debug)]
pub struct Keys<'a, P, T>(Iter<'a, P, T>);

impl<'a, P, T> Iterator for Keys<'a, P, T> {
    type Item = &'a P;

    fn next(&mut self) -> Option<&'a P> {
        self.0.next().map(|(p, _)| p)
    }
}

/// An iterator over all values of a [`PrefixMap`] in lexicographic order of their associated
/// prefixes.
#[derive(Clone, Debug)]
pub struct Values<'a, P, T>(Iter<'a, P, T>);

impl<'a, P, T> Iterator for Values<'a, P, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.0.next().map(|(_, t)| t)
    }
}

/// An iterator over all mutable entries of a [`PrefixMap`] in lexicographic order.
#[derive(Debug)]
pub struct IterMut<'a, P, T> {
    nodes: Vec<&'a mut Node<P, T>>,
}

impl<'a, P, T> Iterator for IterMut<'a, P, T> {
    type Item = (&'a mut P, &'a mut T);

    fn next(&mut self) -> Option<(&'a mut P, &'a mut T)> {
        while let Some(cur) = self.nodes.pop() {
            match cur {
                Node::Leaf { prefix, value } => {
                    if let Some(v) = value {
                        return Some((prefix, v));
                    }
                }
                Node::Single {
                    prefix,
                    value,
                    child,
                } => {
                    self.nodes.push(child.as_mut());
                    if let Some(v) = value {
                        return Some((prefix, v));
                    }
                }
                Node::Branch {
                    prefix,
                    value,
                    left,
                    right,
                } => {
                    self.nodes.push(right.as_mut());
                    self.nodes.push(left.as_mut());
                    if let Some(v) = value {
                        return Some((prefix, v));
                    }
                }
            }
        }
        None
    }
}

/// An iterator over all mutable values of a [`PrefixMap`] in lexicographic order of their
/// associated prefixes.
#[derive(Debug)]
pub struct ValuesMut<'a, P, T>(IterMut<'a, P, T>);

impl<'a, P, T> Iterator for ValuesMut<'a, P, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        self.0.next().map(|(_, t)| t)
    }
}

/// An iterator over all owned entries of a [`PrefixMap`] in lexicographic order.
#[derive(Clone, Debug)]
pub struct IntoIter<P, T> {
    nodes: Vec<Node<P, T>>,
}

impl<P, T> Iterator for IntoIter<P, T> {
    type Item = (P, T);

    fn next(&mut self) -> Option<(P, T)> {
        while let Some(cur) = self.nodes.pop() {
            match cur {
                Node::Leaf { prefix, value } => {
                    if let Some(v) = value {
                        return Some((prefix, v));
                    }
                }
                Node::Single {
                    prefix,
                    value,
                    child,
                } => {
                    self.nodes.push(*child);
                    if let Some(v) = value {
                        return Some((prefix, v));
                    }
                }
                Node::Branch {
                    prefix,
                    value,
                    left,
                    right,
                } => {
                    self.nodes.push(*right);
                    self.nodes.push(*left);
                    if let Some(v) = value {
                        return Some((prefix, v));
                    }
                }
            }
        }
        None
    }
}

/// An iterator over all prefixes of a [`PrefixMap`] in lexicographic order.
#[derive(Clone, Debug)]
pub struct IntoKeys<P, T>(IntoIter<P, T>);

impl<P, T> Iterator for IntoKeys<P, T> {
    type Item = P;

    fn next(&mut self) -> Option<P> {
        self.0.next().map(|(p, _)| p)
    }
}

/// An iterator over all values of a [`PrefixMap`] in lexicographic order of their associated
/// prefix.
#[derive(Clone, Debug)]
pub struct IntoValues<P, T>(IntoIter<P, T>);

impl<P, T> Iterator for IntoValues<P, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.0.next().map(|(_, t)| t)
    }
}

impl<P, T> IntoIterator for PrefixMap<P, T> {
    type Item = (P, T);

    type IntoIter = IntoIter<P, T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            nodes: vec![self.root],
        }
    }
}

impl<'a, P, T> IntoIterator for &'a PrefixMap<P, T> {
    type Item = (&'a P, &'a T);

    type IntoIter = Iter<'a, P, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            nodes: vec![&self.root],
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

    /// An iterator visiting all key-value pairs mutably in lexicographic order. The iterator
    /// element type is `(&mut P, &mut T)`.
    #[inline(always)]
    pub fn iter_mut(&mut self) -> IterMut<'_, P, T> {
        IterMut {
            nodes: vec![&mut self.root],
        }
    }

    /// An iterator visiting all keys in lexicographic order. The iterator element type is `&P`.
    #[inline(always)]
    pub fn keys(&self) -> Keys<'_, P, T> {
        Keys(self.iter())
    }

    /// Creates a consuming iterator visiting all keys in lexicographic order. The iterator element
    /// type is `P`.
    #[inline(always)]
    pub fn into_keys(self) -> IntoKeys<P, T> {
        IntoKeys(self.into_iter())
    }

    /// An iterator visiting all values in lexicographic order. The iterator element type is `&P`.
    #[inline(always)]
    pub fn values(&self) -> Values<'_, P, T> {
        Values(self.iter())
    }

    /// An iterator visiting all values mutably in lexicographic order. The iterator element type is
    /// `&mut P`.
    #[inline(always)]
    pub fn values_mut(&mut self) -> ValuesMut<'_, P, T> {
        ValuesMut(self.iter_mut())
    }

    /// Creates a consuming iterator visiting all values in lexicographic order. The iterator
    /// element type is `P`.
    #[inline(always)]
    pub fn into_values(self) -> IntoValues<P, T> {
        IntoValues(self.into_iter())
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
