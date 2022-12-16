//! implementation of getting items.

use super::*;

impl<P, T> Node<P, T>
where
    P: Prefix,
{
    /// Get the entry for a given prefix.
    pub(crate) fn get(&self, prefix: &P) -> Option<&Node<P, T>> {
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
    pub(crate) fn get_mut(&mut self, prefix: &P) -> Option<&mut Node<P, T>> {
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
    pub(crate) fn get_lpm<'a>(
        &'a self,
        prefix: &P,
        cur: Option<(&'a P, &'a T)>,
    ) -> Option<(&'a P, &'a T)> {
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
    pub(super) fn single_child_contains(&self, p: &P) -> bool {
        match self {
            Node::Single { child, .. } => child.prefix().contains(p),
            _ => false,
        }
    }

    /// Helper function to make the borrow checker happy.
    #[inline(always)]
    pub(super) fn branch_right(&self, p: &P) -> Option<bool> {
        match self {
            Node::Branch { prefix, .. } => Some(p.is_bit_set(prefix.prefix_len())),
            _ => None,
        }
    }
}
