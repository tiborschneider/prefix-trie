//! Code for inserting elements and the entry pattern.

use super::*;

/// A mutable view into a single entry in a map, which may either be vacant or occupied.
pub enum Entry<'a, P, T> {
    /// The entry is not present in the tree.
    Vacant(VacantEntry<'a, P, T>),
    /// The entry is already present in the tree.
    Occupied(OccupiedEntry<'a, P, T>),
}

/// A mutable view into a missing entry. The information within this structure describes a path
/// towards that missing node, and how to insert it.
pub struct VacantEntry<'a, P, T> {
    pub(super) map: &'a mut PrefixMap<P, T>,
    pub(super) prefix: P,
    pub(super) idx: usize,
    pub(super) direction: DirectionForInsert<P>,
}

/// A mutable view into an occupied entry. An occupied entry represents a node that is already
/// present on the tree.
pub struct OccupiedEntry<'a, P, T> {
    pub(super) node: &'a mut Node<P, T>,
}

impl<'a, P, T> Entry<'a, P, T> {
    /// Get the value if it exists
    pub fn get(&self) -> Option<&T> {
        match self {
            Entry::Vacant(_) => None,
            Entry::Occupied(e) => e.node.value.as_ref(),
        }
    }

    /// Get the value if it exists
    pub fn get_mut(&mut self) -> Option<&mut T> {
        match self {
            Entry::Vacant(_) => None,
            Entry::Occupied(e) => e.node.value.as_mut(),
        }
    }

    /// get the key of the current entry
    pub fn key(&self) -> &P {
        match self {
            Entry::Vacant(e) => &e.prefix,
            Entry::Occupied(e) => &e.node.prefix,
        }
    }
}

impl<'a, P, T> Entry<'a, P, T>
where
    P: Prefix,
{
    /// Replace the current entry, and return the entry that was stored before.
    #[inline(always)]
    pub fn insert(self, v: T) -> Option<T> {
        match self {
            Entry::Vacant(e) => {
                e._insert(v);
                None
            }
            Entry::Occupied(e) => e.node.value.replace(v),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and returns a mutable
    /// reference to the value in the entry.
    #[inline(always)]
    pub fn or_insert(self, default: T) -> &'a mut T {
        match self {
            Entry::Vacant(e) => e._insert(default).value.as_mut().unwrap(),
            Entry::Occupied(e) => e.node.value.get_or_insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    #[inline(always)]
    pub fn or_insert_with<F: FnOnce() -> T>(self, default: F) -> &'a mut T {
        match self {
            Entry::Vacant(e) => e._insert(default()).value.as_mut().unwrap(),
            Entry::Occupied(e) => e.node.value.get_or_insert_with(default),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts into the
    /// map.
    #[inline(always)]
    pub fn and_modify<F: FnOnce(&mut T)>(self, f: F) -> Self {
        match self {
            Entry::Vacant(e) => Entry::Vacant(e),
            Entry::Occupied(e) => {
                e.node.value.as_mut().map(f);
                Entry::Occupied(e)
            }
        }
    }
}

impl<'a, P, T> Entry<'a, P, T>
where
    P: Prefix,
    T: Default,
{
    /// Ensures a value is in the entry by inserting the default value if empty, and returns a
    /// mutable reference to the value in the entry.
    #[inline(always)]
    pub fn or_default(self) -> &'a mut T {
        self.or_insert_with(Default::default)
    }
}

impl<'a, P, T> VacantEntry<'a, P, T>
where
    P: Prefix,
{
    fn _insert(self, v: T) -> &'a mut Node<P, T> {
        match self.direction {
            DirectionForInsert::Reached => {
                let node = &mut self.map.table[self.idx];
                node.value = Some(v);
                node
            }
            DirectionForInsert::NewLeaf { right } => {
                let new = self.map.new_node(self.prefix, Some(v));
                self.map.set_child(self.idx, new, right);
                &mut self.map.table[new]
            }
            DirectionForInsert::NewChild { right, child_right } => {
                let new = self.map.new_node(self.prefix, Some(v));
                let child = self.map.set_child(self.idx, new, right).unwrap();
                self.map.set_child(new, child, child_right);
                &mut self.map.table[new]
            }
            DirectionForInsert::NewBranch {
                branch_prefix,
                right,
                prefix_right,
            } => {
                let branch = self.map.new_node(branch_prefix, None);
                let new = self.map.new_node(self.prefix, Some(v));
                let child = self.map.set_child(self.idx, branch, right).unwrap();
                self.map.set_child(branch, new, prefix_right);
                self.map.set_child(branch, child, !prefix_right);
                &mut self.map.table[new]
            }
            DirectionForInsert::Enter { .. } => unreachable!(),
        }
    }
}

impl<'a, P, T> OccupiedEntry<'a, P, T> {
    /// Gets a reference to the key in the entry.
    pub fn key(&self) -> &P {
        &self.node.prefix
    }

    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &T {
        self.node.value.as_ref().unwrap()
    }

    /// Gets a mutable reference to the value in the entry.
    pub fn get_mut(&mut self) -> &mut T {
        self.node.value.as_mut().unwrap()
    }

    /// Insert a new value into the entry, returning the old value.
    pub fn insert(&mut self, value: T) -> T {
        self.node.value.replace(value).unwrap()
    }

    /// Remove the current value and return it.
    pub fn remove(&mut self) -> T {
        self.node.value.take().unwrap()
    }
}

impl<'a, P, T> VacantEntry<'a, P, T> {
    /// Gets a reference to the key in the entry.
    pub fn key(&self) -> &P {
        &self.prefix
    }
}

impl<'a, P, T> VacantEntry<'a, P, T>
where
    P: Prefix,
{
    /// Get a mutable reference to the value. If the value is yet empty, set it to the given default
    /// value.
    pub fn insert(self, default: T) -> &'a mut T {
        let node = self._insert(default);
        node.value.as_mut().unwrap()
    }

    /// Get a mutable reference to the value. If the value is yet empty, set it to the return value
    /// from the given function.
    pub fn insert_with<F: FnOnce() -> T>(self, default: F) -> &'a mut T {
        let node = self._insert(default());
        node.value.as_mut().unwrap()
    }
}

impl<'a, P, T> VacantEntry<'a, P, T>
where
    P: Prefix,
    T: Default,
{
    /// Get a mutable reference to the value. If the value is yet empty, set it to the default value
    /// using `Default::default()`.
    pub fn default(self) -> &'a mut T {
        let node = self._insert(Default::default());
        node.value.as_mut().unwrap()
    }
}
