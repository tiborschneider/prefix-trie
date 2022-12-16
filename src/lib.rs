//! This crate provides a simple prefix tree for IP prefixes. Any lookup performs longest-prefix
//! match.
//!
//! # Description of the Tree
//!
//! The tree consists of three different kinds of nodes. Each node may use an optional value. If the
//! value is not set, then the node is only there to give structure to the tree. The three different
//! kinds of nodes are:
//!
//! - *Leaf*: A leaf only has a prefix and an optional value.
//! - *Single*: A node of this kind has a single child. The child is not required to follow
//!   directly (i.e., the child can have any prefix length as long as it is larger than its parent).
//! - *Branch*: A branch has two children, `left` and `right`. Both children are required to have
//!   a prefix length of exactly one larger than the branch itself.
//!
//! # Operations on the tree
//!
//! There are several operations one can do on the tree. Regular inserts are handled using the
//! `Entry` structure. An `Entry` is a pointer to a location in the tree to either insert a value or
//! modify an existing one. Removals however are different. There are three kinds of removals you
//! can do:
//!
//! - [`PrefixMap::remove`] will remove an entry from the tree and modify the tree structure as if
//!   the value was never inserted before. [`PrefixMap::remove`] will always exactly revert the
//!   operation of [`PrefixMap::insert`]. When only calling this function to remove elements, you
//!   are guaranteed that the tree structure is indistinguishable to a different tree where you
//!   only inserted elements.
//! - [`PrefixMap::remove_children`] will remove all entries that are contained within the given
//!   prefix. This operation will search for the node with the shortest prefix length that is
//!   contained within the given prefix and remove it, including all of its children.
//! - [`PrefixMap::remove_keep_tree`] will not change anything in the tree structure. It will only
//!   remove a value from a node. As soon as you call `remove_keep_tree` once on a tree structure,
//!   the tree will no longer be optimal (while still respecting the rules above).

mod entry;
mod fmt;
mod iter;
mod prefix;
mod remove;
mod remove_children;
#[cfg(test)]
mod test;

pub use entry::{Entry, MissingEntry, PresentEntry};

pub use iter::*;
use prefix::mask_from_prefix_len;
pub use prefix::Prefix;

/// Prefix map, where each lookup performs a longest-prefix match..
#[derive(Clone)]
pub struct PrefixMap<P, T> {
    root: Node<P, T>,
}

impl<P, T> Default for PrefixMap<P, T>
where
    P: Prefix,
{
    fn default() -> Self {
        Self {
            root: Node::Leaf {
                value: None,
                prefix: P::zero(),
            },
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

    /// Get the value of an element by matching exactly on the prefix.
    pub fn get(&self, prefix: &P) -> Option<&T> {
        self.root.get(prefix).and_then(|x| x.value())
    }

    /// Get a mutable reference to a value of an element by matching exactly on the prefix.
    pub fn get_mut(&mut self, prefix: &P) -> Option<&mut T> {
        self.root
            .get_mut(prefix)
            .and_then(|x| x.value_mut().as_mut())
    }

    /// Get the value of an element by matching exactly on the prefix.
    pub fn get_key_value(&self, prefix: &P) -> Option<(&P, &T)> {
        self.root.get(prefix).and_then(|x| x.prefix_value())
    }

    /// Get a value of an element by using longest prefix matching
    pub fn get_lpm(&self, prefix: &P) -> Option<(&P, &T)> {
        self.root.get_lpm(prefix, None)
    }

    /// Check if a key is present in the datastructure.
    pub fn contains_key(&self, prefix: &P) -> bool {
        self.root.get(prefix).is_some()
    }

    /// Get the longest prefix in the datastructure that matches the given `prefix`.
    pub fn get_lpm_prefix(&self, prefix: &P) -> Option<&P> {
        self.root.get_lpm(prefix, None).map(|(p, _)| p)
    }

    /// Insert a new item into the prefix-map. This function may return any value that existed
    /// before.
    pub fn insert(&mut self, prefix: P, value: T) -> Option<T> {
        self.root.entry(prefix).insert(value)
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the
    /// map. In contrast to [`Self::remove`], his operation will keep the tree structure as is, but
    /// only remove the element from it. This allows any future `insert` on the same prefix to be
    /// faster. However future reads from the tree might be a bit slower because they need to
    /// traverse more nodes.
    pub fn remove_keep_tree(&mut self, prefix: &P) -> Option<T> {
        self.root.get_mut(prefix).and_then(|n| n.value_mut().take())
    }

    /// Remove all entries that are contained within `prefix`. This will change the tree structure.
    pub fn remove_children(&mut self, prefix: &P) {
        if prefix.prefix_len() == 0 {
            self.clear()
        } else {
            self.root.remove_children(prefix);
        }
    }

    /// Clear the map, removing all stored key-value pairs and deallocate all memory.
    pub fn clear(&mut self) {
        self.root = Node::Leaf {
            value: None,
            prefix: P::zero(),
        };
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the
    /// map. In contrast to [`Self::remove_keep_tree`], this operation will modify the tree
    /// structure. As a result, this operation takes longer than `remove_keep_tree`, as does
    /// inserting the same element again. However, future reads may be faster as less nodes need to
    /// be traversed. Further, it minimally reduces the memory footprint.
    pub fn remove(&mut self, prefix: &P) -> Option<T> {
        if P::zero().eq(prefix) {
            self.remove_keep_tree(prefix)
        } else {
            let value = self.root.remove(prefix, None).unwrap();
            // restore the root node if that one got simplified.
            if self.root.prefix().prefix_len() != 0 {
                take_mut::take(&mut self.root, |old_root| Node::Single {
                    prefix: P::zero(),
                    value: None,
                    child: Box::new(old_root),
                })
            }
            value
        }
    }
}

/// Node kind that can either be a leaf, a node, or a forward node that summarizes multiple branches.
#[derive(Clone)]
enum Node<P, T> {
    Leaf {
        prefix: P,
        value: Option<T>,
    },
    Single {
        prefix: P,
        value: Option<T>,
        child: Box<Node<P, T>>,
    },
    Branch {
        prefix: P,
        value: Option<T>,
        left: Box<Node<P, T>>,
        right: Box<Node<P, T>>,
    },
}

impl<P, T> Node<P, T> {
    #[inline(always)]
    fn prefix(&self) -> &P {
        match self {
            Node::Leaf { prefix, .. }
            | Node::Single { prefix, .. }
            | Node::Branch { prefix, .. } => prefix,
        }
    }

    #[inline(always)]
    fn prefix_value(&self) -> Option<(&P, &T)> {
        match self {
            Node::Leaf { prefix, value, .. }
            | Node::Single { prefix, value, .. }
            | Node::Branch { prefix, value, .. } => value.as_ref().map(|v| (prefix, v)),
        }
    }

    #[inline(always)]
    fn value(&self) -> Option<&T> {
        match self {
            Node::Leaf { value, .. } | Node::Single { value, .. } | Node::Branch { value, .. } => {
                value.as_ref()
            }
        }
    }

    #[inline(always)]
    fn value_mut(&mut self) -> &mut Option<T> {
        match self {
            Node::Leaf { value, .. } | Node::Single { value, .. } | Node::Branch { value, .. } => {
                value
            }
        }
    }
}

impl<P, T> Node<P, T>
where
    P: Prefix,
{
    /// Get the entry for a given prefix.
    fn get(&self, prefix: &P) -> Option<&Node<P, T>> {
        if self.prefix().eq(prefix) {
            Some(self)
        } else {
            debug_assert!(self.prefix().contains(prefix));
            match self {
                Node::Leaf { .. } => None,
                Node::Single { child, .. } if child.prefix().contains(prefix) => child.get(prefix),
                Node::Single { .. } => None,
                Node::Branch { right, .. } if prefix.is_bit_set(self.prefix().prefix_len()) => {
                    right.get(prefix)
                }
                Node::Branch { left, .. } => left.get(prefix),
            }
        }
    }

    /// Get the entry for a given prefix.
    fn get_mut(&mut self, prefix: &P) -> Option<&mut Node<P, T>> {
        if self.prefix().eq(prefix) {
            Some(self)
        } else {
            debug_assert!(self.prefix().contains(prefix));
            let self_prefix_len = self.prefix().prefix_len();
            match self {
                Node::Leaf { .. } => None,
                Node::Single { child, .. } if child.prefix().contains(prefix) => {
                    child.get_mut(prefix)
                }
                Node::Single { .. } => None,
                Node::Branch { right, .. } if prefix.is_bit_set(self_prefix_len) => {
                    right.get_mut(prefix)
                }
                Node::Branch { left, .. } => left.get_mut(prefix),
            }
        }
    }

    /// Get the entry for a given prefix using longest prefix matching.
    fn get_lpm<'a>(&'a self, prefix: &P, cur: Option<(&'a P, &'a T)>) -> Option<(&'a P, &'a T)> {
        let cur = self.prefix_value().or(cur);
        if self.prefix().eq(prefix) {
            cur
        } else {
            debug_assert!(self.prefix().contains(prefix));
            match self {
                Node::Single { child, .. } if child.prefix().contains(prefix) => {
                    child.get_lpm(prefix, cur)
                }
                Node::Branch { right, .. } if prefix.is_bit_set(self.prefix().prefix_len()) => {
                    right.get_lpm(prefix, cur)
                }
                Node::Branch { left, .. } => left.get_lpm(prefix, cur),
                Node::Leaf { .. } | Node::Single { .. } => cur,
            }
        }
    }
}

/// This block adds helper functions to interact with the enum variant
impl<P, T> Node<P, T>
where
    P: Prefix,
{
    /// Helper function to make the borrow checker happy.
    #[inline(always)]
    fn single_child_contains(&self, p: &P) -> bool {
        match self {
            Node::Single { child, .. } => child.prefix().contains(p),
            _ => false,
        }
    }

    /// Helper function to make the borrow checker happy.
    #[inline(always)]
    fn branch_right(&self, p: &P) -> Option<bool> {
        match self {
            Node::Branch { prefix, .. } => Some(p.is_bit_set(prefix.prefix_len())),
            _ => None,
        }
    }
}
