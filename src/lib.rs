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
//! # Comparison with related projects
//!
//! Throughput is reported relative to `HashMap` (1.00x = HashMap speed), with absolute throughput in
//! parentheses. **Bold** marks the fastest implementation per row. See `benches/benchmark.rs` for
//! details.
//!
//! All benchmarks use IPv4 prefixes from a RIPE RIS peer snapshot (1,042,024 prefixes). See
//! `benches/benchmark.rs` and `benches/memory.rs` for details.
//!
//! | Benchmark           | `HashMap`                | `PrefixMap`              | `TreeBitMap`         | `BTreeMap`          |
//! |---------------------|--------------------------|--------------------------|----------------------|---------------------|
//! | **Lookup**          |                          |                          |                      |                     |
//! | Random access       | 1.00x (14.8 Melem/s)     | **1.24x** (18.4 Melem/s) | 0.64x (9.5 Melem/s)  | 0.29x (4.3 Melem/s) |
//! | BGP updates         | 1.00x (28.9 Melem/s)     | **1.03x** (29.7 Melem/s) | 0.50x (14.6 Melem/s) | 0.31x (8.9 Melem/s) |
//! | **Insert & Remove** |                          |                          |                      |                     |
//! | Random access       | **1.00x** (11.3 Melem/s) | 0.82x (9.2 Melem/s)      | 0.71x (7.9 Melem/s)  | 0.34x (3.8 Melem/s) |
//! | BGP updates         | **1.00x** (22.6 Melem/s) | 0.71x (16.0 Melem/s)     | 0.59x (13.4 Melem/s) | 0.38x (8.6 Melem/s) |
//! | **Create**          |                          |                          |                      |                     |
//! | Random order        | **1.00x** (14.0 Melem/s) | 0.67x (9.4 Melem/s)      | 0.59x (8.3 Melem/s)  | 0.31x (4.4 Melem/s) |
//! | Sorted order        | 1.00x (13.9 Melem/s)     | **1.11x** (15.4 Melem/s) | 0.86x (12.0 Melem/s) | 0.65x (9.0 Melem/s) |
//! | **Memory**          |                          |                          |                      |                     |
//! | Full table          | 26.0 mB                  | 12.0 mB (set: 4.0 mB)    | **11.0 mB**          | 16.4 mB             |
//!
//! In addition, `prefix-trie` includes a [`PrefixSet`] analogous to `std::collections::HashSet`.
//! Set operations are exposed through composable trie views, so operations such as union,
//! intersection, difference, covering union, and covering difference can be combined without
//! building temporary maps. `prefix-trie` has an interface similar to `std::collections`, and its
//! longest-prefix matching is not limited to individual host addresses.
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
