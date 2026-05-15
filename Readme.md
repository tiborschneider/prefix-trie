[![CI test](https://img.shields.io/github/actions/workflow/status/tiborschneider/prefix-trie/test.yml)](https://github.com/tiborschneider/prefix-trie/actions)
[![codecov](https://codecov.io/gh/tiborschneider/prefix-trie/branch/main/graph/badge.svg?token=EEJXNNURMW)](https://codecov.io/gh/tiborschneider/prefix-trie)
[![version](https://img.shields.io/crates/v/prefix-trie)](https://crates.io/crates/prefix-trie)
[![downloads](https://img.shields.io/crates/d/prefix-trie)](https://crates.io/crates/prefix-trie)
[![docs.rs](https://img.shields.io/docsrs/prefix-trie/latest)](https://docs.rs/prefix-trie/latest/prefix_trie/)
[![license](https://img.shields.io/crates/l/prefix-trie/0.2.2)](https://crates.io/crates/prefix-trie)
[![Crates.io MSRV](https://img.shields.io/crates/msrv/prefix-trie)](https://crates.io/crates/prefix-trie)

# Prefix-Trie

This crate provides prefix-map and prefix-set collections for IP prefixes and other fixed-width
prefix types. `PrefixMap` is backed by a compact TreeBitMap-style trie and supports exact,
longest-prefix, and shortest-prefix matches. The crate supports both IPv4 and IPv6 (from either
[ipnet](https://docs.rs/ipnet/2.10.0), [ipnetwork](https://crates.io/crates/ipnetwork), or
[cidr](https://crates.io/crates/cidr)). It also supports any tuple `(R, u8)`, where `R` is any
unsigned primitive integer (`u8`, `u16`, `u32`, `u64`, `u128`, or `usize`).

Prefixes are not stored verbatim. They are reconstructed from their trie position when returned
from map and set operations, so host bits outside the prefix length are not preserved.

This crate also provides a `JointPrefixMap` and `JointPrefixSet` that contains two tables, one for
IPv4 and one for IPv6.

## Migrate to version 0.9

Releases up to 0.8.4 used a binary tree representation.
With version 0.9, this crate migrated to a TreeBitMap, described by [W. Eatherton, Z. Dittia, G. Varghes](https://dl.acm.org/doi/10.1145/997150.997160).
This yields significant performance improvements (~8x faster inserts & lookups for all IPv4 addresses in internet routing tables) and memory reduction (~4x less).

However, this also comes with significant changes in the interface:
- Prefixes are reconstructed from the tree location and no longer stored.
  Consequently, information in the host part of an address is no longer maintained.
  Additionally, the function yields prefixes by value instead of by reference.
  If you wish to store the host-bits as well, consider constructing a type `PrefixMap<P, (P, T)>`.
- Mutable views of the tree can no longer modify the tree structure (to maintain memory safety).
  This is because one can construct two mutable views pointing to branches within the same multi-bit node.
- Thanks to bitmaps, set operations can now be chained (as we can define a common interface for them to return their bitmaps).

## Comparison with related projects

Throughput is reported relative to `HashMap` (1.00x = HashMap speed), with absolute throughput in
parentheses. **Bold** marks the fastest implementation per row. See `benches/benchmark.rs` for
details.

All benchmarks use IPv4 prefixes from a RIPE RIS peer snapshot (1,042,024 prefixes). See
`benches/benchmark.rs` for details.

| Benchmark           | `HashMap`                | `PrefixMap`              | `TreeBitMap`         | `BTreeMap`          |
|---------------------|--------------------------|--------------------------|----------------------|---------------------|
| **Lookup**          |                          |                          |                      |                     |
| Random access       | 1.00x (14.5 Melem/s)     | **1.25x** (18.1 Melem/s) | 0.64x (9.3 Melem/s)  | 0.29x (4.2 Melem/s) |
| BGP updates         | 1.00x (28.4 Melem/s)     | **1.04x** (29.6 Melem/s) | 0.51x (14.5 Melem/s) | 0.30x (8.6 Melem/s) |
| **Insert & Remove** |                          |                          |                      |                     |
| Random access       | **1.00x** (11.5 Melem/s) | 0.79x (9.1 Melem/s)      | 0.68x (7.8 Melem/s)  | 0.34x (3.9 Melem/s) |
| BGP updates         | **1.00x** (23.1 Melem/s) | 0.69x (16.0 Melem/s)     | 0.58x (13.5 Melem/s) | 0.37x (8.5 Melem/s) |
| **Create**          |                          |                          |                      |                     |
| Random order        | **1.00x** (13.9 Melem/s) | 0.66x (9.1 Melem/s)      | 0.58x (8.1 Melem/s)  | 0.30x (4.2 Melem/s) |
| Sorted order        | 1.00x (14.1 Melem/s)     | **1.07x** (15.1 Melem/s) | 0.85x (12.0 Melem/s) | 0.63x (8.9 Melem/s) |

The memory benchmark (`cargo test --bench memory --release -- --nocapture`) stores all 1,042,024
RIS IPv4 prefixes with 32-bit values. Both `PrefixMap` and `TreeBitMap` report 12.0 mB for that
map.

In addition, `prefix-trie` includes a `PrefixSet` analogous to `std::collections::HashSet`.
Set operations are exposed through composable trie views, so operations such as union,
intersection, difference, covering union, and covering difference can be combined without building
temporary maps. `prefix-trie` has an interface similar to `std::collections`, and its longest-prefix
matching is not limited to individual host addresses.

## Description of the Tree

`PrefixMap` stores the logical binary prefix trie in multi-bit nodes. Each internal node covers
five consecutive binary-trie levels. A node at depth `d` can hold values for prefixes with lengths
`d..=d+4`, and it has up to 32 child slots for subtries rooted at depth `d+5`.

Each node stores two bitmaps: one for the value slots that are present in the node, and one for the
child slots that are present below it. The allocators store multi-bit nodes and value cells in
compact, linearized arrays, which improves cache locality and keeps lookup and traversal decisions
local to a node. Physical slots are derived from the bitmaps with a popcount, avoiding one pointer
per possible branch.

A stored entry is identified by its path through the trie and by a value bit inside the final
multi-bit node. The prefix object passed to `insert` is not stored alongside the value. Returned
prefixes are therefore reconstructed and canonicalized to the prefix length.

## Traversals

Iterators traverse the logical prefix trie in lexicographic order and yield reconstructed owned
prefixes together with references or owned values. Complete iteration is linear in the number of
stored entries and trie nodes visited.

Set operations use the same view infrastructure. `union`, `intersection`, `difference`,
`covering_union`, and `covering_difference` traverse the involved trie views together and yield
results in lexicographic order. Covering variants also report longest-prefix matches from the
opposite side where appropriate.

## Trie Views

`TrieView` is a trait for immutable, mutable, and composed cursors into a trie. Concrete leaf views
are `TrieRef`, created from `&PrefixMap` or `&PrefixSet`, and `TrieRefMut`, created from mutable
references. Both are obtained through the `AsView` trait: call `map.view()` for a full-trie view or
`map.view_at(&prefix)` for a non-empty subtrie.

Views can be rooted at a prefix even when no value is stored exactly at that prefix. If the prefix
falls inside an existing multi-bit node, the view masks that node's value and child bitmaps so that
iteration and search stay inside the requested subtrie. Composed views such as `UnionView`,
`IntersectionView`, and `DifferenceView` also implement `TrieView`, so view operations can be
chained before iterating.

## Operations on the Tree

Most point operations are bounded by prefix width, not by the number of stored entries. Let `w` be
the number of bits in the prefix representation, and let `h = ceil((w + 1) / 5)` be the maximum
number of multi-bit nodes on a search path. For IPv4, `h <= 7`; for IPv6, `h <= 26`. Let `n` be the
number of stored entries, and let `v` be the number of trie nodes visited by a traversal.

| Operation                                      | Complexity |
|------------------------------------------------|------------|
| `len`, `is_empty`, `mem_size`                  | `O(1)`     |
| `get`, `get_mut`, `contains_key`               | `O(h)`     |
| `get_lpm`, `get_spm`, `cover`                  | `O(h)`     |
| `entry`, `insert`                              | `O(h)`     |
| `remove`, `remove_keep_tree`                   | `O(h)`     |
| `children`, `view_at`                          | `O(h)` to create, then linear in the subtrie |
| `iter`, `keys`, `values`                       | `O(n + v)` for a complete traversal |
| `retain`, `clear`                              | `O(n + v)` |
| `remove_children`                              | `O(h + m)` where `m` is the removed subtrie size |
| `union`, `intersection`, `difference`, ...     | linear in the trie portions visited |
| Operations on an occupied `map::Entry`         | `O(1)` after the entry lookup |
| Inserting through a vacant `map::Entry`        | `O(h)` worst case |

There are three removal styles:

- `PrefixMap::remove` will remove an entry from the tree and modify the tree structure as if
  the value was never inserted before. It may remove now-empty multi-bit nodes and compact their
  allocator blocks.
- `PrefixMap::remove_children` will remove all entries that are contained within the given
  prefix, including entries stored in the same multi-bit node and in child nodes below it.
- `PrefixMap::remove_keep_tree` removes only the value and leaves the existing node structure in
  place, which can make reinserting the same prefix cheaper but may leave empty internal nodes for
  future traversals to pass through.
