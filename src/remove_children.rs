//! Code to remove all children from a node.

use super::*;

impl<P, T> Node<P, T>
where
    P: Prefix,
{
    /// Get the entry for a given prefix.
    pub(super) fn remove_children(&mut self, prefix: &P) {
        if prefix.contains(self.prefix()) {
            unreachable!()
        } else {
            debug_assert!(self.prefix().contains(prefix));
            let self_prefix_len = self.prefix().prefix_len();
            match self {
                Node::Leaf { .. } => {}
                Node::Single { child, .. } if prefix.contains(child.prefix()) => {
                    self._remove_all_child()
                }
                Node::Single { child, .. } if child.prefix().contains(prefix) => {
                    child.remove_children(prefix)
                }
                Node::Single { .. } => {}
                Node::Branch { right, .. } if prefix.is_bit_set(self_prefix_len) => {
                    if prefix.contains(right.prefix()) {
                        self._remove_all_right()
                    } else {
                        right.remove_children(prefix)
                    }
                }
                Node::Branch { left, .. } => {
                    if prefix.contains(left.prefix()) {
                        self._remove_all_left()
                    } else {
                        left.remove_children(prefix)
                    }
                }
            }
        }
    }

    fn _remove_all_child(&mut self) {
        take_mut::take(self, |node| {
            if let Node::Single { prefix, value, .. } = node {
                Node::Leaf { prefix, value }
            } else {
                unreachable!()
            }
        });
    }

    fn _remove_all_left(&mut self) {
        take_mut::take(self, |node| {
            if let Node::Branch {
                prefix,
                value,
                right,
                ..
            } = node
            {
                Node::Single {
                    prefix,
                    value,
                    child: right,
                }
            } else {
                unreachable!()
            }
        });
    }

    fn _remove_all_right(&mut self) {
        take_mut::take(self, |node| {
            if let Node::Branch {
                prefix,
                value,
                left,
                ..
            } = node
            {
                Node::Single {
                    prefix,
                    value,
                    child: left,
                }
            } else {
                unreachable!()
            }
        });
    }
}
