//! Code to remove entries from the map.

use super::*;

impl<P, T> Node<P, T>
where
    P: Prefix,
{
    /// recursively search and remove an item from the tree.
    pub(super) fn remove(&mut self, prefix: &P, from_branch: Option<bool>) -> RemoveAction<T> {
        if self.prefix().eq(prefix) {
            return RemoveAction::Child(self.value_mut().take());
        } else {
            debug_assert!(self.prefix().contains(prefix));
            let self_prefix_len = self.prefix().prefix_len();
            let action = match self {
                Node::Leaf { .. } => return RemoveAction::Return(None),
                Node::Single { child, .. } if child.prefix().contains(prefix) => {
                    child.remove(prefix, None)
                }
                Node::Single { .. } => return RemoveAction::Return(None),
                Node::Branch { right, .. } if prefix.is_bit_set(self_prefix_len) => {
                    right.remove(prefix, Some(true)).right()
                }
                Node::Branch { left, .. } => left.remove(prefix, Some(false)).left(),
            };
            match action {
                RemoveAction::Child(x) => {
                    // remove the child of `self` from the parent of `self` if the parent is a
                    // branch, and `self` has no value.
                    if let (Some(right), true) = (from_branch, self.value().is_none()) {
                        RemoveAction::GrandChild(right, x)
                    } else {
                        self.remove_child(false, from_branch.is_some());
                        RemoveAction::Return(x)
                    }
                }
                RemoveAction::GrandChild(right, x) => {
                    self.remove_grandchild_single(right, from_branch.is_some());
                    RemoveAction::Return(x)
                }
                RemoveAction::Left(x) => {
                    self.remove_child(false, from_branch.is_some());
                    RemoveAction::Return(x)
                }
                RemoveAction::Right(x) => {
                    self.remove_child(true, from_branch.is_some());
                    RemoveAction::Return(x)
                }
                RemoveAction::Return(x) => RemoveAction::Return(x),
            }
        }
    }

    fn remove_child(&mut self, right: bool, from_branch: bool) {
        take_mut::take(self, |node| match (node, right) {
            (
                Node::Single {
                    prefix,
                    value,
                    child,
                },
                _,
            ) => {
                // Either create a new single that forwards for longer, or create a leaf.
                if let (Some(child), _) = remove_self_new_child(child) {
                    Node::Single {
                        prefix,
                        value,
                        child,
                    }
                } else {
                    Node::Leaf { prefix, value }
                }
            }
            (
                Node::Branch {
                    prefix,
                    value,
                    left,
                    right,
                },
                false,
            ) => {
                // Either create a new single that forwards for longer, or create a branch.
                match remove_self_new_child(left) {
                    (Some(new_child), Some(old_prefix)) => Node::Branch {
                        prefix,
                        value,
                        left: Box::new(Node::Single {
                            prefix: old_prefix,
                            value: None,
                            child: new_child,
                        }),
                        right,
                    },
                    (Some(new_child), None) => Node::Branch {
                        prefix,
                        value,
                        left: new_child,
                        right,
                    },
                    (None, _) => {
                        // if we are not from a branch and value is none, then directly return the
                        // simplified right. Otherwise, turn node into a single, pointing to the
                        // simplified right.
                        if !from_branch && value.is_none() {
                            *simplify_single_node(right)
                        } else {
                            Node::Single {
                                prefix,
                                value,
                                child: simplify_single_node(right),
                            }
                        }
                    }
                }
            }
            (
                Node::Branch {
                    prefix,
                    value,
                    left,
                    right,
                },
                true,
            ) => {
                // Either create a new single that forwards for longer, or create a branch.
                match remove_self_new_child(right) {
                    (Some(new_child), Some(old_prefix)) => Node::Branch {
                        prefix,
                        value,
                        left,
                        right: Box::new(Node::Single {
                            prefix: old_prefix,
                            value: None,
                            child: new_child,
                        }),
                    },
                    (Some(new_child), None) => Node::Branch {
                        prefix,
                        value,
                        left,
                        right: new_child,
                    },
                    (None, _) => {
                        // if we are not from a branch and value is none, then directly return the
                        // simplified left. Otherwise, turn node into a single, pointing to the
                        // simplified left.
                        if !from_branch && value.is_none() {
                            *simplify_single_node(left)
                        } else {
                            Node::Single {
                                prefix,
                                value,
                                child: simplify_single_node(left),
                            }
                        }
                    }
                }
            }
            _ => unreachable!(),
        });
    }

    /// Remove the grandchild of a branch, where the left or the right is a single and has no value.
    fn remove_grandchild_single(&mut self, right: bool, from_branch: bool) {
        take_mut::take(self, |node| match (node, right) {
            (
                Node::Branch {
                    prefix,
                    value,
                    left,
                    right,
                },
                false,
            ) => {
                if let Node::Single {
                    prefix: child_p,
                    value: None,
                    child: grandchild,
                } = *left
                {
                    // Either create a new single that forwards for longer, or create a branch.
                    match remove_self_new_child(grandchild).0 {
                        // The grandchild will be replaced by another node.
                        Some(new_grandchild) => Node::Branch {
                            prefix,
                            value,
                            left: Box::new(Node::Single {
                                prefix: child_p,
                                value: None,
                                child: new_grandchild,
                            }),
                            right,
                        },
                        // the grandchild is removed, which will also remove the left child.
                        None => {
                            if value.is_none() && !from_branch {
                                // if we are not coming from a branch, and self is empty, we can simply
                                // replace self with right (the unmodified one).
                                *simplify_single_node(right)
                            } else {
                                // if however we need to keep self, then simply turn self into a
                                // single.
                                Node::Single {
                                    prefix,
                                    value,
                                    child: simplify_single_node(right),
                                }
                            }
                        }
                    }
                } else {
                    unreachable!()
                }
            }
            (
                Node::Branch {
                    prefix,
                    value,
                    left,
                    right,
                },
                true,
            ) => {
                if let Node::Single {
                    prefix: child_p,
                    value: None,
                    child: grandchild,
                } = *right
                {
                    // Either create a new single that forwards for longer, or create a branch.
                    match remove_self_new_child(grandchild).0 {
                        // The grandchild will be replaced by another node.
                        Some(new_grandchild) => Node::Branch {
                            prefix,
                            value,
                            left,
                            right: Box::new(Node::Single {
                                prefix: child_p,
                                value: None,
                                child: new_grandchild,
                            }),
                        },
                        // the grandchild is removed, which will also remove the left child.
                        None => {
                            if value.is_none() && !from_branch {
                                // if we are not coming from a branch, and self is empty, we can simply
                                // replace self with left (the unmodified one).
                                *simplify_single_node(left)
                            } else {
                                // if however we need to keep self, then simply turn self into a
                                // single of left.
                                Node::Single {
                                    prefix,
                                    value,
                                    child: simplify_single_node(left),
                                }
                            }
                        }
                    }
                } else {
                    unreachable!()
                }
            }
            _ => unreachable!(),
        })
    }
}

fn simplify_single_node<P, T>(node: Box<Node<P, T>>) -> Box<Node<P, T>> {
    if let Node::Single {
        value: None, child, ..
    } = *node
    {
        child
    } else {
        node
    }
}

/// function to transform the old child into a new child. Leafs are destroyed, Single nodes
/// return their child (child of child, i.e., grandchi,d), and branches are unmodified.
///
/// This function returns the prefix from the old child if a grandchild was returned.
fn remove_self_new_child<P, T>(old_child: Box<Node<P, T>>) -> (Option<Box<Node<P, T>>>, Option<P>) {
    if matches!(old_child.as_ref(), Node::Branch { value: None, .. }) {
        // unmodify the old child
        (Some(old_child), None)
    } else {
        match *old_child {
            Node::Leaf { .. } => (None, None),
            Node::Single {
                prefix,
                child: grandchild,
                ..
            } => (Some(grandchild), Some(prefix)),
            _ => unreachable!(),
        }
    }
}

pub(super) enum RemoveAction<T> {
    Child(Option<T>),
    Left(Option<T>),
    Right(Option<T>),
    GrandChild(bool, Option<T>),
    Return(Option<T>),
}

impl<T> RemoveAction<T> {
    pub(super) fn unwrap(self) -> Option<T> {
        match self {
            Self::Return(x) => x,
            _ => unreachable!(),
        }
    }
    fn left(self) -> Self {
        if let RemoveAction::Child(x) = self {
            RemoveAction::Left(x)
        } else {
            self
        }
    }

    fn right(self) -> Self {
        if let RemoveAction::Child(x) = self {
            RemoveAction::Right(x)
        } else {
            self
        }
    }
}
