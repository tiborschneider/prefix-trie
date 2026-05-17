#![cfg_attr(docsrs, feature(doc_notable_trait, doc_auto_cfg))]

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
//! The library [`ip_network_table-deps-treebitmap`](https://crates.io/crates/ip_network_table-deps-treebitmap)
//! provides a datastructure (in the following called `TreeBitMap`) that essentially solves a
//! similar algorithm. The following table compares the performance and memory of the two libraries,
//! and relates them to the `HashMap` and `BTreeMap` of the standard library. Throughput is reported
//! relative to `HashMap` (1.00x = HashMap speed), with absolute throughput in parentheses. **Bold**
//! marks the fastest implementation per row. See `benches/benchmark.rs` for details.
//!
//! All benchmarks use IPv4 prefixes from a RIPE RIS peer snapshot (1,042,024 IPv4 prefixes or
//! 246,174 IPv6 prefixes). See `benches/benchmark.rs` and `benches/memory.rs` for details. The
//! benchmark results below were obtained on an AMD EPYC server.
//!
//! | Benchmark          | `HashMap`             | `PrefixMap`           | `TreeBitMap`        | `BTreeMap`         |
//! |--------------------|-----------------------|-----------------------|---------------------|--------------------|
//! | *Lookup*           |                       |                       |                     |                    |
//! | -> Random access   |                       |                       |                     |                    |
//! | ---> IPv4          |   1.00x (7.4 Mops)    | **1.92x (14.2 Mops)** |   1.15x (8.5 Mops)  |   0.46x (3.4 Mops) |
//! | ---> IPv6          | **1.00x (11.0 Mops)** |   0.97x (10.7 Mops)   |   0.58x (6.4 Mops)  |   0.45x (4.9 Mops) |
//! | -> RIS updates     |                       |                       |                     |                    |
//! | ---> IPv4          |   1.00x (17.5 Mops)   | **1.69x (29.5 Mops)** |   0.78x (13.7 Mops) |   0.47x (8.2 Mops) |
//! | ---> IPv6          | **1.00x (24.8 Mops)** |   0.63x (15.7 Mops)   |   0.33x (8.2 Mops)  |   0.32x (7.9 Mops) |
//! | *Insert & Remove*  |                       |                       |                     |                    |
//! | -> Random access   |                       |                       |                     |                    |
//! | ---> IPv4          |   1.00x (7.4 Mops)    | **1.04x (7.7 Mops)**  |   0.89x (6.6 Mops)  |   0.43x (3.2 Mops) |
//! | ---> IPv6          | **1.00x (10.8 Mops)** |   0.48x (5.2 Mops)    |   0.44x (4.7 Mops)  |   0.39x (4.3 Mops) |
//! | -> RIS updates     |                       |                       |                     |                    |
//! | ---> IPv4          | **1.00x (17.1 Mops)** |   0.88x (15.0 Mops)   |   0.71x (12.2 Mops) |   0.47x (8.0 Mops) |
//! | ---> IPv6          | **1.00x (25.0 Mops)** |   0.33x (8.3 Mops)    |   0.29x (7.3 Mops)  |   0.31x (7.7 Mops) |
//! | *Create*           |                       |                       |                     |                    |
//! | -> Random order    |                       |                       |                     |                    |
//! | ---> IPv4          |   1.00x (7.8 Mops)    | **1.13x (8.8 Mops)**  |   0.95x (7.4 Mops)  |   0.55x (4.3 Mops) |
//! | ---> IPv6          | **1.00x (11.4 Mops)** |   0.52x (5.9 Mops)    |   0.43x (4.9 Mops)  |   0.42x (4.8 Mops) |
//! | -> Sorted order    |                       |                       |                     |                    |
//! | ---> IPv4          |   1.00x (10.3 Mops)   | **1.45x (14.9 Mops)** |   1.04x (10.7 Mops) |   0.85x (8.8 Mops) |
//! | ---> IPv6          | **1.00x (11.7 Mops)** |   0.70x (8.2 Mops)    |   0.55x (6.5 Mops)  |   0.51x (6.0 Mops) |
//! | -> Scattered order |                       |                       |                     |                    |
//! | ---> IPv4          |   1.00x (10.3 Mops)   | **1.02x (10.5 Mops)** |   0.76x (7.8 Mops)  |   0.34x (3.4 Mops) |
//! | ---> IPv6          | **1.00x (11.6 Mops)** |   0.59x (6.9 Mops)    |   0.47x (5.5 Mops)  |   0.46x (5.4 Mops) |
//! | **Memory**         |                       |                       |                     |                    |
//! | -> IPv4            | 26.0 mB               | 12.0 mB (set: 4.0 mB) | **11.0 mB**         | 16.4 mB            |
//! | -> IPv6            | 12.5 mB               |  6.0 mB (set: 4.0 mB) |  **4.3 mB**         |  8.1 mB            |
//!
//! Besides better performance than the [`TreeBitMap`](https://crates.io/crates/ip_network_table-deps-treebitmap),
//! `prefix-trie` includes a `PrefixSet` analogous to `std::collections::HashSet`. Set operations
//! are exposed through composable trie views, so operations such as union, intersection, difference,
//! covering union, and covering difference can be combined without building temporary maps.
//! `prefix-trie` has an interface similar to `std::collections`, and its longest-prefix matching
//! is not limited to individual host addresses.
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
