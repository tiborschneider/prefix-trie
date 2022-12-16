//! Formatting implementation for the PrefixMap

use std::fmt::{Debug, Formatter, Result};

use super::*;

impl<P: Debug, T: Debug> Debug for PrefixMap<P, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.root.fmt(f)
    }
}

impl<P: Debug, T: Debug> Debug for Node<P, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Leaf {
                prefix,
                value: Some(value),
            } => f.debug_map().entry(prefix, value).finish(),
            Self::Leaf {
                prefix,
                value: None,
            } => f.debug_set().entry(prefix).finish(),
            Self::Single {
                prefix,
                value: Some(value),
                child,
            } => f
                .debug_map()
                .entry(prefix, &(value, child.as_ref()))
                .finish(),
            Self::Single {
                prefix,
                value: None,
                child,
            } => f.debug_map().entry(prefix, child.as_ref()).finish(),
            Self::Branch {
                prefix,
                value: Some(value),
                left,
                right,
            } => f
                .debug_map()
                .entry(prefix, &(value, left.as_ref(), right.as_ref()))
                .finish(),
            Self::Branch {
                prefix,
                value: None,
                left,
                right,
            } => f
                .debug_map()
                .entry(prefix, &(left.as_ref(), right.as_ref()))
                .finish(),
        }
    }
}
