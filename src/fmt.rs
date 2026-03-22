//! Debug formatting for PrefixMap.
//!
//! The output hides the internal TreeBitMap structure and shows the logical prefix trie,
//! matching the style of PrefixMap's debug output.

use std::fmt::{Debug, Formatter, Result};

use crate::{Prefix, PrefixMap};

impl<P: Prefix + Debug, T: Debug> Debug for PrefixMap<P, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let entries: Vec<(P, &T)> = self.iter().collect();
        DebugSubtree { entries: &entries }.fmt(f)
    }
}

struct DebugSubtree<'a, P, T> {
    entries: &'a [(P, &'a T)],
}

struct DebugExtendedNode<'a, P, T> {
    value: &'a T,
    children: DebugSubtree<'a, P, T>,
}

impl<P: Prefix + Debug, T: Debug> Debug for DebugExtendedNode<'_, P, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut d = f.debug_struct("");
        d.field("value", self.value);
        if !self.children.entries.is_empty() {
            d.field("children", &self.children);
        }
        d.finish()
    }
}

impl<P: Prefix + Debug, T: Debug> Debug for DebugSubtree<'_, P, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut dm = f.debug_map();
        let mut entries = self.entries;

        while let Some(((prefix, value), rest)) = entries.split_first() {
            let child_count = rest.iter().take_while(|(p, _)| prefix.contains(p)).count();
            let (children, remaining) = rest.split_at(child_count);
            entries = remaining;

            dm.entry(
                prefix,
                &DebugExtendedNode {
                    value: *value,
                    children: DebugSubtree { entries: children },
                },
            );
        }

        dm.finish()
    }
}
