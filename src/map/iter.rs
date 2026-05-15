//! Module that contains the implementation for the iterators

use num_traits::Zero;

use crate::{
    Prefix,
    {
        allocator::{Loc, RawPtr},
        node::{child_bit, LexIterElem, MaskedLexIter},
        table::{DataIdx, Table, K},
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
        // SAFETY: `Loc::root()` is always valid. The `&'a Table<T>` borrow prevents
        // structural mutations for the lifetime of the iterator, keeping all Locs valid.
        let lex = unsafe { table.lex_iter(Loc::root(), 0, <P::R as Zero>::zero()) };
        Self::at_node(table, lex)
    }

    pub(crate) fn at_node(table: &'a Table<T>, lex: MaskedLexIter<P::R>) -> Self {
        let stack = vec![lex];
        Self {
            table: Some(table),
            stack,
        }
    }

    pub(crate) fn from_stack(table: &'a Table<T>, stack: Vec<MaskedLexIter<P::R>>) -> Self {
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
                LexIterElem::Data(idx) => {
                    // SAFETY: `Iter` holds `&'a Table`; no structural changes occur during
                    // immutable iteration, so `idx.node` remains valid.
                    let Some(r) = (unsafe { idx.resolve(table) }) else {
                        continue;
                    };
                    let p = r.prefix(key);
                    return Some((p, r.get()));
                }
                LexIterElem::Child(next_loc, depth, next_key) => {
                    // SAFETY: `next_loc` came from the previous `lex_iter` step; the borrow
                    // of `table` prevents structural mutations, so `next_loc` remains valid.
                    self.stack
                        .push(unsafe { table.lex_iter(next_loc, depth, next_key) })
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
        // SAFETY: `Loc::root()` is always valid. The `&'a mut Table<T>` borrow prevents
        // structural mutations for the lifetime of the iterator, keeping all Locs valid.
        let lex = unsafe { table.lex_iter(Loc::root(), 0, <P::R as Zero>::zero()) };
        Self::at_node(table, lex)
    }

    pub(crate) fn at_node(table: &'a mut Table<T>, lex: MaskedLexIter<P::R>) -> Self {
        let ptr = table.raw_cells();
        Self {
            table: Some((table, ptr)),
            stack: vec![lex],
        }
    }

    pub(crate) fn from_stack(table: &'a mut Table<T>, stack: Vec<MaskedLexIter<P::R>>) -> Self {
        let ptr = table.raw_cells();
        Self {
            table: Some((table, ptr)),
            stack,
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
                LexIterElem::Data(idx) => {
                    // SAFETY: `IterMut` holds exclusive access to the table data; no structural
                    // changes occur, so `idx.node` remains valid.
                    let Some(r) = (unsafe { idx.resolve(table) }) else {
                        continue;
                    };
                    let p = r.prefix(key);
                    // SAFETY: `IterMut` was created from `&'a mut Table`; ptr was obtained
                    // from that same table. The tree is acyclic so each node is visited at most
                    // once, guaranteeing no two live `&mut T` references to the same slot.
                    return Some((p, unsafe { r.unsafe_get_mut(&mut ptr) }));
                }
                LexIterElem::Child(next_idx, depth, next_key) => {
                    // SAFETY: `next_idx` came from the previous `lex_iter` step; the exclusive
                    // borrow of `table` prevents structural mutations, so `next_idx` remains valid.
                    self.stack
                        .push(unsafe { table.lex_iter(next_idx, depth, next_key) })
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
        // SAFETY: `Loc::root()` is always valid. `IntoIter` owns the table, preventing
        // any external structural mutations for its lifetime.
        let lex = unsafe { table.lex_iter(Loc::root(), 0, <P::R as Zero>::zero()) };
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
                LexIterElem::Data(idx) => {
                    // SAFETY: IntoIter owns the table; no external mutations possible.
                    // `take()` clears the bitmap bit, so the MaskedLexIter snapshot may
                    // yield already-taken bits; `resolve_mut` re-checks and returns None.
                    let Some(r) = (unsafe { idx.resolve_mut(&mut self.table) }) else {
                        continue;
                    };
                    let p = r.prefix(key);
                    return Some((p, r.take()));
                }
                LexIterElem::Child(next_loc, depth, next_key) => {
                    // SAFETY: `IntoIter` owns the table and makes no structural mutations;
                    // `next_loc` came from the previous `lex_iter` step and remains valid.
                    self.stack
                        .push(unsafe { self.table.lex_iter(next_loc, depth, next_key) })
                }
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
    lpm_elements: Vec<DataIdx>,
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
                                          // SAFETY: `Cover` holds `&'a Table<T>` — no structural mutations are possible
                                          // for the lifetime `'a`. `loc` starts as `Loc::root()` and is only updated to
                                          // the result of a prior `child()` call, so it is always a valid, live node.
                self.lpm_elements = unsafe {
                    self.table
                        .data_ancestors(loc, self.depth, self.key, self.prefix_len)
                }
                .collect();
                self.lpm_elements.reverse();
                let prefix_in_this_node = self.prefix_len < self.depth + K;
                self.next_loc = if prefix_in_this_node {
                    None
                } else {
                    let child_bit = child_bit(self.depth, self.key);
                    // SAFETY: same invariant as above.
                    unsafe { self.table.child(loc, child_bit) }
                };
                self.depth += K;
                continue;
            };

            // SAFETY: `loc` came from `data_ancestors`, which only yields bits set in the
            // bitmap. `Cover` holds `&'a Table<T>` and never mutates node structure.
            let r = unsafe { loc.resolve(self.table) }
                .expect("Cover: data_ancestors yielded stale idx");
            return Some((r.prefix(self.key), r.get()));
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
