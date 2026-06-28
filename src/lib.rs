#![cfg_attr(docsrs, feature(doc_notable_trait, doc_cfg))]

//! This crate provides prefix-map and prefix-set collections for IP prefixes and other fixed-width
//! prefix types. [`PrefixMap`] is backed by a compact TreeBitMap-style trie and supports exact,
//! longest-prefix, and shortest-prefix matches. The crate supports both IPv4 and IPv6 (from either
//! [ipnet](https://docs.rs/ipnet/2.10.0), [ipnetwork](https://crates.io/crates/ipnetwork), or
//! [cidr](https://crates.io/crates/cidr)). It also supports any tuple `(R, u8)`, where `R` is any
//! unsigned primitive integer (`u8`, `u16`, `u32`, `u64`, `u128`, or `usize`).
//!
//! Prefixes are not stored verbatim. They are reconstructed from their trie position when returned
//! from map and set operations, so host bits outside the prefix length are not preserved.
//!
//! This crate also provides a [`joint::JointPrefixMap`] and [`joint::JointPrefixSet`] that contains
//! two tables, one for IPv4 and one for IPv6.
//!
//! # Description of the Tree
//!
//! [`PrefixMap`] stores the logical binary prefix trie in multi-bit nodes. Each internal node covers
//! five consecutive binary-trie levels. A node at depth `d` can hold values for prefixes with
//! lengths `d..=d+4`, and it has up to 32 child slots for subtries rooted at depth `d+5`.
//!
//! Each node stores two bitmaps: one for the value slots that are present in the node, and one for
//! the child slots that are present below it. The allocators store multi-bit nodes and value cells
//! in compact, linearized arrays, which improves cache locality and keeps lookup and traversal
//! decisions local to a node. Physical slots are derived from the bitmaps with a popcount, avoiding
//! one pointer per possible branch.
//!
//! A stored entry is identified by its path through the trie and by a value bit inside the final
//! multi-bit node. The prefix object passed to `insert` is not stored alongside the value. Returned
//! prefixes are therefore reconstructed and canonicalized to the prefix length.
//!
//! # Traversals
//!
//! Iterators traverse the logical prefix trie in lexicographic order and yield reconstructed owned
//! prefixes together with references or owned values. Complete iteration is linear in the number of
//! stored entries and trie nodes visited.
//!
//! Set operations use the same view infrastructure. `union`, `intersection`, `difference`,
//! `covering_union`, and `covering_difference` traverse the involved trie views together and yield
//! results in lexicographic order. Covering variants also report longest-prefix matches from the
//! opposite side where appropriate.
//!
//! # Trie Views
//!
//! [`TrieView`] is a trait for immutable, mutable, and composed cursors into a trie. Concrete leaf
//! views are [`TrieRef`], created from `&PrefixMap` or `&PrefixSet`, and [`TrieRefMut`], created
//! from mutable references. Both are obtained through the [`AsView`] trait: call `map.view()` for a
//! full-trie view or `map.view_at(&prefix)` for a non-empty subtrie.
//!
//! Views can be rooted at a prefix even when no value is stored exactly at that prefix. If the
//! prefix falls inside an existing multi-bit node, the view masks that node's value and child
//! bitmaps so that iteration and search stay inside the requested subtrie. Composed views such as
//! [`trieview::UnionView`], [`trieview::IntersectionView`], and [`trieview::DifferenceView`] also
//! implement [`TrieView`], so view operations can be chained before iterating.
//!
//! # Operations on the Tree
//!
//! Most point operations are bounded by prefix width, not by the number of stored entries. Let `w`
//! be the number of bits in the prefix representation, and let `h = ceil((w + 1) / 5)` be the
//! maximum number of multi-bit nodes on a search path. For IPv4, `h <= 7`; for IPv6, `h <= 26`.
//! Let `n` be the number of stored entries, and let `v` be the number of trie nodes visited by a
//! traversal.
//!
//! | Operation                                      | Complexity |
//! |------------------------------------------------|------------|
//! | `len`, `is_empty`, `mem_size`                  | `O(1)`     |
//! | `get`, `get_mut`, `contains_key`               | `O(h)`     |
//! | `get_lpm`, `get_spm`, `cover`                  | `O(h)`     |
//! | `entry`, `insert`                              | `O(h)`     |
//! | `remove`, `remove_keep_tree`                   | `O(h)`     |
//! | `children`, `view_at`                          | `O(h)` to create, then linear in the subtrie |
//! | `iter`, `keys`, `values`                       | `O(n + v)` for a complete traversal |
//! | `retain`, `clear`                              | `O(n + v)` |
//! | `remove_children`                              | `O(h + m)` where `m` is the removed subtrie size |
//! | `union`, `intersection`, `difference`, ...     | linear in the trie portions visited |
//! | Operations on an occupied `map::Entry`         | `O(1)` after the entry lookup |
//! | Inserting through a vacant `map::Entry`        | `O(h)` worst case |
//!
//! There are three removal styles:
//!
//! - [`PrefixMap::remove`] will remove an entry from the tree and modify the tree structure as if
//!   the value was never inserted before. It may remove now-empty multi-bit nodes and compact their
//!   allocator blocks.
//! - [`PrefixMap::remove_children`] will remove all entries that are contained within the given
//!   prefix, including entries stored in the same multi-bit node and in child nodes below it.
//! - [`PrefixMap::remove_keep_tree`] removes only the value and may leave empty trie nodes in
//!   place.

#![allow(clippy::collapsible_else_if)]
#![deny(missing_docs)]

mod aggregate;
mod allocator;
mod fmt;
#[cfg(test)]
mod fuzzing;
mod node;
mod prefix;
#[cfg(feature = "serde")]
mod serde;
mod table;
#[cfg(feature = "ipnet")]
#[cfg(test)]
mod test;

pub mod joint;
pub mod map;
pub mod set;
pub mod trieview;

pub use map::PrefixMap;
pub use prefix::Prefix;
pub use set::PrefixSet;
pub use trieview::{AsView, TrieRef, TrieRefMut, TrieView};
