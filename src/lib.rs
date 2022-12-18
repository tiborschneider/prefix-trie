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

#![allow(clippy::collapsible_else_if)]

mod entry;
mod fmt;
mod iter;
mod prefix;
#[cfg(test)]
mod test;

pub use entry::{Entry, OccupiedEntry, VacantEntry};

pub use iter::*;
pub use prefix::Prefix;

/// Prefix map, where each lookup performs a longest-prefix match..
#[derive(Clone)]
pub struct PrefixMap<P, T> {
    table: Vec<Node<P, T>>,
    free: Vec<usize>,
}

impl<P, T> Default for PrefixMap<P, T>
where
    P: Prefix,
{
    fn default() -> Self {
        Self {
            table: vec![Node {
                prefix: P::zero(),
                value: None,
                left: None,
                right: None,
            }],
            free: Vec::new(),
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
        let mut idx = 0;
        loop {
            match self.get_direction(idx, prefix) {
                Direction::Reached => return self.table[idx].value.as_ref(),
                Direction::Enter { next, .. } => idx = next,
                Direction::Missing => return None,
            }
        }
    }

    /// Get a mutable reference to a value of an element by matching exactly on the prefix.
    pub fn get_mut(&mut self, prefix: &P) -> Option<&mut T> {
        let mut idx = 0;
        loop {
            match self.get_direction(idx, prefix) {
                Direction::Reached => return self.table[idx].value.as_mut(),
                Direction::Enter { next, .. } => idx = next,
                Direction::Missing => return None,
            }
        }
    }

    /// Get the value of an element by matching exactly on the prefix.
    pub fn get_key_value(&self, prefix: &P) -> Option<(&P, &T)> {
        let mut idx = 0;
        loop {
            match self.get_direction(idx, prefix) {
                Direction::Reached => return self.table[idx].prefix_value(),
                Direction::Enter { next, .. } => idx = next,
                Direction::Missing => return None,
            }
        }
    }

    /// Get a value of an element by using longest prefix matching
    pub fn get_lpm(&self, prefix: &P) -> Option<(&P, &T)> {
        let mut idx = 0;
        let mut best_match: Option<(&P, &T)> = None;
        loop {
            best_match = self.table[idx].prefix_value().or(best_match);
            match self.get_direction(idx, prefix) {
                Direction::Enter { next, .. } => idx = next,
                _ => return best_match,
            }
        }
    }

    /// Check if a key is present in the datastructure.
    pub fn contains_key(&self, prefix: &P) -> bool {
        let mut idx = 0;
        loop {
            match self.get_direction(idx, prefix) {
                Direction::Reached => return true,
                Direction::Enter { next, .. } => idx = next,
                Direction::Missing => return false,
            }
        }
    }

    /// Get the longest prefix in the datastructure that matches the given `prefix`.
    pub fn get_lpm_prefix(&self, prefix: &P) -> Option<&P> {
        let mut idx = 0;
        let mut best_match: Option<&P> = None;
        loop {
            best_match = self.table[idx]
                .prefix_value()
                .map(|(p, _)| p)
                .or(best_match);
            match self.get_direction(idx, prefix) {
                Direction::Enter { next, .. } => idx = next,
                _ => return best_match,
            }
        }
    }

    /// Insert a new item into the prefix-map. This function may return any value that existed
    /// before.
    pub fn insert(&mut self, prefix: P, value: T) -> Option<T> {
        let mut idx = 0;
        loop {
            match self.get_direction_for_insert(idx, &prefix) {
                DirectionForInsert::Enter { next, .. } => idx = next,
                DirectionForInsert::Reached => return self.table[idx].value.replace(value),
                DirectionForInsert::NewLeaf { right } => {
                    let new = self.new_node(prefix, Some(value));
                    self.set_child(idx, new, right);
                    return None;
                }
                DirectionForInsert::NewChild { right, child_right } => {
                    let new = self.new_node(prefix, Some(value));
                    let child = self.set_child(idx, new, right).unwrap();
                    self.set_child(new, child, child_right);
                    return None;
                }
                DirectionForInsert::NewBranch {
                    branch_prefix,
                    right,
                    prefix_right,
                } => {
                    let branch = self.new_node(branch_prefix, None);
                    let new = self.new_node(prefix, Some(value));
                    let child = self.set_child(idx, branch, right).unwrap();
                    self.set_child(branch, new, prefix_right);
                    self.set_child(branch, child, !prefix_right);
                    return None;
                }
            }
        }
    }

    /// Gets the given key’s corresponding entry in the map for in-place manipulation.
    pub fn entry(&mut self, prefix: P) -> Entry<'_, P, T> {
        let mut idx = 0;
        loop {
            match self.get_direction_for_insert(idx, &prefix) {
                DirectionForInsert::Enter { next, .. } => idx = next,
                DirectionForInsert::Reached if self.table[idx].value.is_some() => {
                    return Entry::Occupied(OccupiedEntry {
                        node: &mut self.table[idx],
                    })
                }
                direction => {
                    return Entry::Vacant(VacantEntry {
                        map: self,
                        prefix,
                        idx,
                        direction,
                    })
                }
            }
        }
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the
    /// map. In contrast to [`Self::remove`], his operation will keep the tree structure as is, but
    /// only remove the element from it. This allows any future `insert` on the same prefix to be
    /// faster. However future reads from the tree might be a bit slower because they need to
    /// traverse more nodes.
    pub fn remove_keep_tree(&mut self, prefix: &P) -> Option<T> {
        let mut idx = 0;
        loop {
            match self.get_direction(idx, prefix) {
                Direction::Reached => return self.table[idx].value.take(),
                Direction::Enter { next, .. } => idx = next,
                Direction::Missing => return None,
            }
        }
    }

    /// Remove all entries that are contained within `prefix`. This will change the tree
    /// structure. This operation is `O(n)`, as the entries must be freed up one-by-one.
    pub fn remove_children(&mut self, prefix: &P) {
        if prefix.prefix_len() == 0 {
            return self.clear();
        }
        let mut parent_right = false;
        let mut parent = 0;
        let mut idx = 0;
        loop {
            match self.get_direction_for_insert(idx, prefix) {
                DirectionForInsert::Reached => {
                    return self._do_remove_children(parent, parent_right)
                }
                DirectionForInsert::Enter { next, right } => {
                    parent_right = right;
                    parent = idx;
                    idx = next
                }
                DirectionForInsert::NewLeaf { .. } | DirectionForInsert::NewBranch { .. } => return,
                DirectionForInsert::NewChild { right, .. } => {
                    return self._do_remove_children(idx, right)
                }
            }
        }
    }

    /// remove all elements from that point onwards.
    fn _do_remove_children(&mut self, idx: usize, right: bool) {
        let mut to_free = vec![self.get_child(idx, right).unwrap()];
        self.clear_child(idx, right);
        while let Some(idx) = to_free.pop() {
            let node = &mut self.table[idx];
            let _ = node.value.take();
            if let Some(left) = node.left.take() {
                to_free.push(left)
            }
            if let Some(right) = node.right.take() {
                to_free.push(right)
            }
            self.free.push(idx);
        }
    }

    /// Clear the map, removing all stored key-value pairs and deallocate all memory.
    pub fn clear(&mut self) {
        self.table.clear();
        self.free.clear();
        self.table.push(Node {
            prefix: P::zero(),
            value: None,
            left: None,
            right: None,
        });
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the
    /// map. In contrast to [`Self::remove_keep_tree`], this operation will modify the tree
    /// structure. As a result, this operation takes longer than `remove_keep_tree`, as does
    /// inserting the same element again. However, future reads may be faster as less nodes need to
    /// be traversed. Further, it minimally reduces the memory footprint.
    pub fn remove(&mut self, prefix: &P) -> Option<T> {
        if prefix.prefix_len() == 0 {
            self.remove_keep_tree(prefix)
        } else {
            let mut idx = 0;
            let mut grandparent = 0;
            let mut grandparent_right = false;
            let mut parent = 0;
            let mut parent_right = false;
            // first, search for the element
            loop {
                match self.get_direction(idx, prefix) {
                    Direction::Reached => break,
                    Direction::Enter { next, right } => {
                        grandparent_right = parent_right;
                        parent_right = right;
                        grandparent = parent;
                        parent = idx;
                        idx = next;
                    }
                    Direction::Missing => return None,
                }
            }
            // if we reach this point, then `idx` is the element to remove, `parent` is its parent,
            // and `parent_right` stores the direction of `idx` at `parent`.
            let node = &mut self.table[idx];
            let value = node.value.take();
            let has_left = node.left.is_some();
            let has_right = node.right.is_some();

            if has_left && has_right {
                // if the node has both left and right set, then it must remain in the tree.
                value
            } else if !(has_left || has_right) {
                // if the node is a leaf, simply remove it.
                self.clear_child(parent, parent_right);
                self.free.push(idx);
                // now, if the parent has no value, also remove the parent and replace it with the
                // current node.
                if parent != 0 && self.table[parent].value.is_none() {
                    if let Some(sibling) = self.get_child(parent, !parent_right) {
                        self.set_child(grandparent, sibling, grandparent_right);
                    } else {
                        self.clear_child(grandparent, grandparent_right);
                    }
                }
                value
            } else {
                // one child remains. simply connect that child directly to the parent
                let child_right = has_right;
                let child = self.clear_child(idx, child_right).unwrap();
                self.set_child(parent, child, parent_right);
                self.free.push(idx);
                value
            }
        }
    }

    /// Get the child of a node, either to the left or the right
    #[inline(always)]
    fn get_child(&self, idx: usize, right: bool) -> Option<usize> {
        if right {
            self.table[idx].right
        } else {
            self.table[idx].left
        }
    }

    /// set the child of a node (either to the left or the right), and return the index of the old child.
    #[inline(always)]
    fn set_child(&mut self, idx: usize, child: usize, right: bool) -> Option<usize> {
        if right {
            self.table[idx].right.replace(child)
        } else {
            self.table[idx].left.replace(child)
        }
    }

    /// remove a child from a node (just the reference).
    #[inline(always)]
    fn clear_child(&mut self, idx: usize, right: bool) -> Option<usize> {
        if right {
            self.table[idx].right.take()
        } else {
            self.table[idx].left.take()
        }
    }

    /// insert a new node into the table and return its index.
    #[inline(always)]
    fn new_node(&mut self, prefix: P, value: Option<T>) -> usize {
        if let Some(idx) = self.free.pop() {
            let node = &mut self.table[idx];
            node.prefix = prefix;
            node.value = value;
            node.left = None;
            node.right = None;
            idx
        } else {
            let idx = self.table.len();
            self.table.push(Node {
                prefix,
                value,
                left: None,
                right: None,
            });
            idx
        }
    }

    /// Get the directions from some node `idx` to get to `prefix`.
    #[inline(always)]
    fn get_direction(&self, cur: usize, prefix: &P) -> Direction {
        let cur_p = &self.table[cur].prefix;
        if cur_p.eq(prefix) {
            Direction::Reached
        } else {
            let right = to_right(cur_p, prefix);
            match self.get_child(cur, right) {
                Some(child) if self.table[child].prefix.contains(prefix) => {
                    Direction::Enter { next: child, right }
                }
                _ => Direction::Missing,
            }
        }
    }

    /// Get the directions from some node `idx` to get to `prefix`.
    #[inline(always)]
    fn get_direction_for_insert(&self, cur: usize, prefix: &P) -> DirectionForInsert<P> {
        let cur_p = &self.table[cur].prefix;
        if cur_p.eq(prefix) {
            DirectionForInsert::Reached
        } else {
            let right = to_right(cur_p, prefix);
            if let Some(child) = self.get_child(cur, right) {
                let child_p = &self.table[child].prefix;
                if child_p.contains(prefix) {
                    DirectionForInsert::Enter { next: child, right }
                } else if prefix.contains(child_p) {
                    DirectionForInsert::NewChild {
                        right,
                        child_right: to_right(prefix, child_p),
                    }
                } else {
                    let branch_prefix = prefix.longest_common_prefix(child_p);
                    let prefix_right = to_right(&branch_prefix, prefix);
                    DirectionForInsert::NewBranch {
                        branch_prefix,
                        right,
                        prefix_right,
                    }
                }
            } else {
                DirectionForInsert::NewLeaf { right }
            }
        }
    }
}

/// Node kind that can either be a leaf, a node, or a forward node that summarizes multiple branches.
#[derive(Clone)]
struct Node<P, T> {
    prefix: P,
    value: Option<T>,
    left: Option<usize>,
    right: Option<usize>,
}

impl<P, T> Node<P, T> {
    /// get the tuple of prefix and value.
    fn prefix_value(&self) -> Option<(&P, &T)> {
        self.value.as_ref().map(|v| (&self.prefix, v))
    }
}

#[inline(always)]
pub fn to_right<P: Prefix>(branch_p: &P, child_p: &P) -> bool {
    child_p.is_bit_set(branch_p.prefix_len())
}

enum Direction {
    /// The prefix is already reached.
    Reached,
    /// Enter the next index and search again.
    Enter { next: usize, right: bool },
    /// The node was not found,
    Missing,
}

enum DirectionForInsert<P> {
    /// The prefix is already reached.
    Reached,
    /// Enter the next index and search again.
    Enter { next: usize, right: bool },
    /// Insert a new child at the given position as a leaf.
    NewLeaf { right: bool },
    /// Insert a new child at the given position, moving all old children to be a child of the new
    /// prefix. `parent_right` tells where to insert the new node, while `child_right` tells where
    /// to insert the old child (on the right or the left of the new node).
    NewChild { right: bool, child_right: bool },
    /// Insert a new branch at the parent with the given prefix. `parent_right` tells where to
    /// insert the branch, while `prefix_right` tells where to insert the new node at the
    /// branch. The old child of the parent should be inserted at `!prefix_right` of the branch.
    NewBranch {
        branch_prefix: P,
        right: bool,
        prefix_right: bool,
    },
}
