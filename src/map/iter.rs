//! Module that contains the implementation for the iterators

use num_traits::Zero;

use crate::{
    Prefix,
    {
        allocator::{Loc, RawPtr},
        node::{child_bit, LexIterElem, MaskedLexIter},
        table::{Present, Table, K},
        PrefixMap,
    },
};

/// An iterator over all entries of a [`PrefixMap`] in lexicographic order.
pub struct Iter<'a, P: Prefix, T> {
    table: Option<&'a Table<T>>,
    stack: Vec<MaskedLexIter<P::R>>,
}

impl<P: Prefix, T> Clone for Iter<'_, P, T> {
    fn clone(&self) -> Self {
        Self {
            table: self.table,
            stack: self.stack.clone(),
        }
    }
}

impl<P: Prefix, T> Default for Iter<'_, P, T> {
    fn default() -> Self {
        Self {
            table: None,
            stack: Vec::new(),
        }
    }
}

impl<'a, P: Prefix, T> Iter<'a, P, T> {
    /// Create a new iterator that iterates over all
    pub(crate) fn new(table: &'a Table<T>) -> Self {
        let lex = table.lex_iter(Loc::root(), 0, <P::R as Zero>::zero());
        Self::at_node(table, lex)
    }

    pub(crate) fn at_node(table: &'a Table<T>, lex: MaskedLexIter<P::R>) -> Self {
        let stack = vec![lex];
        Self {
            table: Some(table),
            stack,
        }
    }
}

impl<'a, P: Prefix, T> Iterator for Iter<'a, P, T> {
    type Item = (P, &'a T);

    fn next(&mut self) -> Option<(P, &'a T)> {
        let table = self.table?;
        while let Some(lex_iter) = self.stack.last_mut() {
            let key = *lex_iter.key();
            let Some(next) = lex_iter.next() else {
                self.stack.pop();
                continue;
            };

            match next {
                LexIterElem::Data(element) => {
                    return Some((element.prefix(key), table.get_data(element)));
                }
                LexIterElem::Child(next_loc, depth, next_key) => {
                    self.stack.push(table.lex_iter(next_loc, depth, next_key))
                }
            }
        }
        None
    }
}

/// An iterator over all prefixes of a [`PrefixMap`] in lexicographic order.
#[derive(Clone, Default)]
pub struct Keys<'a, P: Prefix, T>(pub(crate) Iter<'a, P, T>);

impl<'a, P: Prefix, T> Iterator for Keys<'a, P, T> {
    type Item = P;

    fn next(&mut self) -> Option<P> {
        self.0.next().map(|(k, _)| k)
    }
}

/// An iterator over all values of a [`PrefixMap`] in lexicographic order of their associated
/// prefixes.
#[derive(Clone, Default)]
pub struct Values<'a, P: Prefix, T>(pub(crate) Iter<'a, P, T>);

impl<'a, P: Prefix, T> Iterator for Values<'a, P, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.0.next().map(|(_, v)| v)
    }
}

/// A mutable iterator over a [`PrefixMap`]. This iterator yields elements in lexicographic order of
/// their associated prefix.
pub struct IterMut<'a, P: Prefix, T> {
    // SAFETY
    // 1. This structure must be created using a mutable reference to the table (see Self::new).
    // 2. The tree cannot have cycles (ensured by the way we create the tree.)
    table: Option<(&'a Table<T>, RawPtr<T>)>,
    stack: Vec<MaskedLexIter<P::R>>,
}

impl<P: Prefix, T> Default for IterMut<'_, P, T> {
    fn default() -> Self {
        Self {
            table: None,
            stack: Vec::new(),
        }
    }
}

impl<'a, P: Prefix, T> IterMut<'a, P, T> {
    /// Create a new iterator that iterates over all
    pub(crate) fn new(table: &'a mut Table<T>) -> Self {
        let lex = table.lex_iter(Loc::root(), 0, <P::R as Zero>::zero());
        Self::at_node(table, lex)
    }

    pub(crate) fn at_node(table: &'a mut Table<T>, lex: MaskedLexIter<P::R>) -> Self {
        let ptr = table.raw_cells();
        Self {
            table: Some((table, ptr)),
            stack: vec![lex],
        }
    }
}

impl<'a, P: Prefix, T> Iterator for IterMut<'a, P, T> {
    type Item = (P, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        let (table, mut ptr) = self.table?;
        while let Some(lex_iter) = self.stack.last_mut() {
            let key = *lex_iter.key();
            let Some(next) = lex_iter.next() else {
                self.stack.pop();
                continue;
            };

            match next {
                LexIterElem::Data(element) => {
                    // SAFETY:
                    // - self has exclusive reference to the entire table
                    // - the tree is acyclic, so each node will be visited at most once.
                    // - The node was already accessed before, but it immediately released again.
                    // - Internal index msut point to an initialized memory, as required by the iterator
                    //   invariant.
                    return Some((element.prefix(key), unsafe {
                        table.unsafe_get_mut(&mut ptr, element)
                    }));
                }
                LexIterElem::Child(next_idx, depth, next_key) => {
                    self.stack.push(table.lex_iter(next_idx, depth, next_key))
                }
            }
        }
        None
    }
}

/// A mutable iterator over values of [`PrefixMap`]. This iterator yields elements in lexicographic
/// order.
#[derive(Default)]
pub struct ValuesMut<'a, P: Prefix, T>(pub(crate) IterMut<'a, P, T>);

impl<'a, P: Prefix, T> Iterator for ValuesMut<'a, P, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, v)| v)
    }
}

/// An iterator over all owned entries of a [`PrefixMap`] in lexicographic order.
#[derive(Clone)]
pub struct IntoIter<P: Prefix, T> {
    table: Table<T>,
    stack: Vec<MaskedLexIter<P::R>>,
}

impl<P: Prefix, T> IntoIter<P, T> {
    /// Create a new iterator that iterates over all
    pub(crate) fn new(table: Table<T>) -> Self {
        let lex = table.lex_iter(Loc::root(), 0, <P::R as Zero>::zero());
        Self::at_node(table, lex)
    }

    pub(crate) fn at_node(table: Table<T>, lex: MaskedLexIter<P::R>) -> Self {
        let stack = vec![lex];
        Self { table, stack }
    }
}

impl<P: Prefix, T> Iterator for IntoIter<P, T> {
    type Item = (P, T);

    fn next(&mut self) -> Option<(P, T)> {
        while let Some(lex_iter) = self.stack.last_mut() {
            let key = *lex_iter.key();
            let Some(next) = lex_iter.next() else {
                self.stack.pop();
                continue;
            };

            match next {
                LexIterElem::Data(loc) => {
                    // SAFETY:
                    // 1. `loc` comes from `MaskedLexIter`, which was constructed from a
                    //    snapshot of the node's bitmap before any elements were removed, so
                    //    `loc.data.slot == compute_slot(snapshot_bitmap, loc.data.bit)` is valid.
                    // 2. `MaskedLexIter` yields each bitmap bit exactly once, so no
                    //    `bit` is passed twice (no double-free).
                    // 3. `IntoIter` owns the `Table` exclusively and drops it after the
                    //    iterator is exhausted, so no subsequent structured access (via a
                    //    freshly-computed `compute_slot`) can occur on the affected nodes.
                    return Some((loc.prefix(key), unsafe {
                        self.table.take_data_for_iter(loc)
                    }));
                }
                LexIterElem::Child(next_loc, depth, next_key) => self
                    .stack
                    .push(self.table.lex_iter(next_loc, depth, next_key)),
            }
        }
        None
    }
}

/// An iterator over all prefixes of a [`PrefixMap`] in lexicographic order.
#[derive(Clone)]
pub struct IntoKeys<P: Prefix, T>(pub(super) IntoIter<P, T>);

impl<P: Prefix, T> Iterator for IntoKeys<P, T> {
    type Item = P;

    fn next(&mut self) -> Option<P> {
        self.0.next().map(|(k, _)| k)
    }
}

/// An iterator over all values of a [`PrefixMap`] in lexicographic order of their associated
/// prefix.
#[derive(Clone)]
pub struct IntoValues<P: Prefix, T>(pub(super) IntoIter<P, T>);

impl<P: Prefix, T> Iterator for IntoValues<P, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.0.next().map(|(_, v)| v)
    }
}

impl<P: Prefix, T> IntoIterator for PrefixMap<P, T> {
    type Item = (P, T);

    type IntoIter = IntoIter<P, T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self.table)
    }
}

impl<'a, P: Prefix, T> IntoIterator for &'a PrefixMap<P, T> {
    type Item = (P, &'a T);

    type IntoIter = Iter<'a, P, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(&self.table)
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

/// An iterator that yields all items in a `PrefixMap` that cover (are a superset of) a given
/// prefix (including the prefix itself if present). See [`PrefixMap::cover`] for how to
/// create this iterator.
pub struct Cover<'a, P: Prefix, T> {
    table: &'a Table<T>,
    next_loc: Option<Loc>,
    lpm_elements: Vec<Present>,
    key: P::R,
    prefix_len: u32,
    depth: u32,
}

impl<'a, P: Prefix, T> Cover<'a, P, T> {
    pub(crate) fn new(table: &'a PrefixMap<P, T>, prefix: &P) -> Self {
        let key = prefix.repr();
        let prefix_len = prefix.prefix_len() as u32;
        let lpm_elements = Vec::new();
        let next_loc = Some(Loc::root());
        Self {
            table: &table.table,
            next_loc,
            lpm_elements,
            key,
            prefix_len,
            depth: 0,
        }
    }
}

impl<'a, P: Prefix, T> Iterator for Cover<'a, P, T>
where
    P: Prefix,
{
    type Item = (P, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let Some(loc) = self.lpm_elements.pop() else {
                // fill the lpm_nodes
                let loc = self.next_loc?; // if none, then exit.
                self.lpm_elements = self
                    .table
                    .data_ancestors(loc, self.depth, self.key, self.prefix_len)
                    .collect();
                self.lpm_elements.reverse();
                let prefix_in_this_node = self.prefix_len < self.depth + K;
                self.next_loc = if prefix_in_this_node {
                    None
                } else {
                    let child_bit = child_bit(self.depth, self.key);
                    self.table.child(loc, child_bit)
                };
                self.depth += K;
                continue;
            };

            return Some((loc.prefix(self.key), self.table.get_data(loc)));
        }
    }
}

/// An iterator that yields all keys (prefixes) in a `PrefixMap` that covers a given prefix
/// (including the prefix itself if present). See [`PrefixMap::cover_keys`] for how to create this
/// iterator.
pub struct CoverKeys<'a, P: Prefix, T>(pub(super) Cover<'a, P, T>);

impl<'a, P: Prefix, T> Iterator for CoverKeys<'a, P, T>
where
    P: Prefix,
{
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(p, _)| p)
    }
}

/// An iterator that yields all values in a `PrefixMap` that covers a given prefix (including the
/// prefix itself if present). See [`PrefixMap::cover_values`] for how to create this iterator.
pub struct CoverValues<'a, P: Prefix, T>(pub(super) Cover<'a, P, T>);

impl<'a, P: Prefix, T> Iterator for CoverValues<'a, P, T>
where
    P: Prefix,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, t)| t)
    }
}

/// Create a lex iterator that covers the given prefix.
pub(crate) fn lpm_children_iter_start<P: Prefix, T>(
    table: &Table<T>,
    prefix: &P,
) -> MaskedLexIter<P::R> {
    let key = prefix.repr();
    let prefix_len = prefix.prefix_len() as u32;
    table.lex_iter_at(key, prefix_len)
}
