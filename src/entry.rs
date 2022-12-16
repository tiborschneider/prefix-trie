//! Code for inserting elements and the entry pattern.

use super::*;

/// A mutable view into a single entry in a map, which may either be vacant or occupied.
pub enum Entry<'a, P, T> {
    Missing(MissingEntry<'a, P, T>),
    Present(PresentEntry<'a, P, T>),
}

/// A mutable view into a missing entry.
pub struct MissingEntry<'a, P, T> {
    prefix: P,
    node: &'a mut Node<P, T>,
    kind: MissingEntryKind<P>,
}

/// A mutable view into an occupied entry.
pub struct PresentEntry<'a, P, T> {
    node: &'a mut Node<P, T>,
}

impl<P, T> Node<P, T>
where
    P: Prefix,
{
    /// Get the entry for a given prefix.
    pub(super) fn entry(&mut self, prefix: P) -> Entry<'_, P, T> {
        if self.prefix().eq(&prefix) {
            Entry::Present(PresentEntry { node: self })
        } else {
            debug_assert!(self.prefix().contains(&prefix));
            if self.single_child_contains(&prefix) {
                if let Node::Single { child, .. } = self {
                    child.entry(prefix)
                } else {
                    unreachable!()
                }
            } else if let Some(dir) = self.branch_right(&prefix) {
                if let Node::Branch { left, right, .. } = self {
                    if dir {
                        right.entry(prefix)
                    } else {
                        left.entry(prefix)
                    }
                } else {
                    unreachable!()
                }
            } else {
                let kind = match self {
                    Node::Leaf { .. } => MissingEntryKind::ExtendLeaf,
                    Node::Single { child, .. } if prefix.contains(child.prefix()) => {
                        MissingEntryKind::SplitSingle
                    }
                    Node::Single { child, .. } => {
                        MissingEntryKind::BranchOff(child.prefix().longest_common_prefix(&prefix))
                    }
                    _ => unreachable!(),
                };

                Entry::Missing(MissingEntry {
                    prefix,
                    node: self,
                    kind,
                })
            }
        }
    }

    fn insert_extend_leaf(&mut self, p: P, v: T) -> &mut Node<P, T> {
        take_mut::take(self, |node| {
            if let Node::Leaf { prefix, value } = node {
                Node::Single {
                    prefix,
                    value,
                    child: Box::new(Node::Leaf {
                        prefix: p,
                        value: Some(v),
                    }),
                }
            } else {
                unreachable!()
            }
        });
        if let Node::Single { child, .. } = self {
            child.as_mut()
        } else {
            unreachable!()
        }
    }

    fn insert_split_single(&mut self, p: P, v: T) -> &mut Node<P, T> {
        take_mut::take(self, |node| {
            if let Node::Single {
                prefix,
                value,
                child,
            } = node
            {
                Node::Single {
                    prefix,
                    value,
                    child: Box::new(Node::Single {
                        prefix: p,
                        value: Some(v),
                        child,
                    }),
                }
            } else {
                unreachable!()
            }
        });
        if let Node::Single { child, .. } = self {
            child.as_mut()
        } else {
            unreachable!()
        }
    }

    fn insert_branch_off(&mut self, branch_p: P, p: P, v: T) -> &mut Node<P, T> {
        let mut new_goes_right = false;
        take_mut::take(self, |node| {
            if let Node::Single {
                prefix,
                value,
                child,
            } = node
            {
                let branch_len = branch_p.prefix_len();
                let create_child = |n: Box<Node<P, T>>| {
                    if n.prefix().prefix_len() == branch_len + 1 {
                        // child can be created directly
                        n
                    } else {
                        // child must be created as a child of a Node::Single.
                        let mask = mask_from_prefix_len(branch_len + 1);
                        let new_prefix = P::from_repr_len(n.prefix().repr() & mask, branch_len + 1);
                        Box::new(Node::Single {
                            prefix: new_prefix,
                            value: None,
                            child: n,
                        })
                    }
                };

                new_goes_right = p.is_bit_set(branch_len);
                debug_assert!(new_goes_right != child.prefix().is_bit_set(branch_len));
                let old = create_child(child);
                let new = create_child(Box::new(Node::Leaf {
                    prefix: p,
                    value: Some(v),
                }));
                let (left, right) = if new_goes_right {
                    (old, new)
                } else {
                    (new, old)
                };
                if prefix.eq(&branch_p) {
                    Node::Branch {
                        prefix,
                        value,
                        left,
                        right,
                    }
                } else {
                    Node::Single {
                        prefix,
                        value,
                        child: Box::new(Node::Branch {
                            prefix: branch_p,
                            value: None,
                            left,
                            right,
                        }),
                    }
                }
            } else {
                unreachable!()
            }
        });
        if let Node::Branch { left, right, .. } = self {
            return if new_goes_right {
                right.as_mut()
            } else {
                left.as_mut()
            };
        } else if let Node::Single { child, .. } = self {
            if let Node::Branch { left, right, .. } = child.as_mut() {
                return if new_goes_right {
                    right.as_mut()
                } else {
                    left.as_mut()
                };
            }
        }
        unreachable!()
    }
}

/// Different kinds of missing entries (or the action that we need to perform in order to insert a
/// new element at this position)
enum MissingEntryKind<P> {
    /// The current node is a `NodeKind::Leaf`, and it must be extended such that it becomes a
    /// `NodeKind::Single`, and the new node is a `NodeKind::Leaf`.
    ExtendLeaf,
    /// The current node is `NodeKind::Single`. The new node must be inserted between the current
    /// node and its child, and the new node should be `NodeKind::Single`.
    SplitSingle,
    /// Current node is `NodeKind::Single`. At the given branch_point, we need to insert a branch
    /// node of kind `NodeKind::Branch`. There, we need to put the child, as well as the new node on
    /// left or right.
    BranchOff(P),
}

impl<'a, P, T> Entry<'a, P, T> {
    /// Get the value if it exists
    pub fn get(&self) -> Option<&T> {
        match self {
            Entry::Missing(_) => None,
            Entry::Present(e) => e.node.value(),
        }
    }

    /// Get the value if it exists
    pub fn get_mut(&mut self) -> Option<&mut T> {
        match self {
            Entry::Missing(_) => None,
            Entry::Present(e) => e.node.value_mut().as_mut(),
        }
    }

    /// get the key of the current entry
    pub fn key(&self) -> &P {
        match self {
            Entry::Missing(e) => &e.prefix,
            Entry::Present(e) => e.node.prefix(),
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
            Entry::Missing(e) => {
                e.insert(v);
                None
            }
            Entry::Present(e) => e.node.value_mut().replace(v),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and returns a mutable
    /// reference to the value in the entry.
    #[inline(always)]
    pub fn or_insert(self, default: T) -> &'a mut T {
        match self {
            Entry::Missing(e) => e.insert(default).value_mut().as_mut().unwrap(),
            Entry::Present(e) => e.node.value_mut().get_or_insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    #[inline(always)]
    pub fn or_insert_with<F: FnOnce() -> T>(self, default: F) -> &'a mut T {
        match self {
            Entry::Missing(e) => e.insert(default()).value_mut().as_mut().unwrap(),
            Entry::Present(e) => e.node.value_mut().get_or_insert_with(default),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts into the
    /// map.
    #[inline(always)]
    pub fn and_modify<F: FnOnce(&mut T)>(self, f: F) -> Self {
        match self {
            Entry::Missing(e) => Entry::Missing(e),
            Entry::Present(e) => {
                e.node.value_mut().as_mut().map(f);
                Entry::Present(e)
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

impl<'a, P, T> MissingEntry<'a, P, T>
where
    P: Prefix,
{
    fn insert(self, v: T) -> &'a mut Node<P, T> {
        match self.kind {
            MissingEntryKind::ExtendLeaf => self.node.insert_extend_leaf(self.prefix, v),
            MissingEntryKind::SplitSingle => self.node.insert_split_single(self.prefix, v),
            MissingEntryKind::BranchOff(branch_p) => {
                self.node.insert_branch_off(branch_p, self.prefix, v)
            }
        }
    }
}
