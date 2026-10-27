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

## Description of the Tree

`PrefixMap` stores the logical binary prefix trie in multi-bit nodes, as described by 
[W. Eatherton, Z. Dittia, and G. Varghes](https://dl.acm.org/doi/10.1145/997150.997160). Each 
internal node covers five consecutive binary-trie levels. A node at depth `d` can hold values 
for prefixes with lengths `d..=d+4`, and it has up to 32 child slots for subtries rooted at depth 
`d+5`.

Each node stores two bitmaps: one for the value slots that are present in the node, and one for the
child slots that are present below it. The allocators store multi-bit nodes and value cells in
compact, linearized arrays, which improves cache locality and keeps lookup and traversal decisions
local to a node. Physical slots are derived from the bitmaps with a popcount, avoiding one pointer
per possible branch.

A stored entry is identified by its path through the trie and by a value bit inside the final
multi-bit node. The prefix object passed to `insert` is not stored alongside the value. Returned
prefixes are therefore reconstructed and canonicalized to the prefix length.

## Trie Views and Set Operations

`TrieView` is a trait for immutable, mutable, and composed cursors into a trie. Concrete leaf views
are `TrieRef` (created from `&PrefixMap` or `&PrefixSet`) and `TrieRefMut` (created from mutable
references). Both are obtained through the `AsView` trait: call `map.view()` for a full-trie view or
`map.view_at(&prefix)` for a non-empty subtrie.

Views and iterators traverse the logical prefix trie in lexicographic order and yield reconstructed 
owned prefixes together with references or owned values. 

Set operations use the same view infrastructure. `union`, `intersection`, `difference`,
`covering_union`, and `covering_difference` simultaneously traverse the involved trie views and 
yield results in lexicographic order. Covering variants also report longest-prefix matches from 
the opposite side where appropriate. The result of such a set operation is not the finished 
traversal, but a struct that implements `TrieView` and describes the traversal. Thus, you can chain
multiple set operations and compute them in a single traversal of the original tries.

## Aggregation

Both `PrefixMap` and `PrefixSet` can be aggregated, that is, finding a compact representation of
the Trie to yield the same result for longest-prefix matches. For both the map and the set, this
library has two versions of the aggregation: `aggregate_consistent` and `aggregate`. The 
consistent variant only drops nodes that are covered by an ancestor. Thus, `get_lpm` always returns
the same value for any prefix. The non-consistent variant is also allowed to merge siblings with
the same value. Thus, `get_lpm` is only guaranteed to return the same value for addresses (i.e., 
/32 prefixes for IPv4). 

The `PrefixMap::aggregate`, `PrefixMap::aggregate_fill`, and `PrefixMap::aggregate_fill_default`
implement the Reduced Routing Table Construction algorithm, described by 
[R. P. Draves, C. King, S. Venkatachary, and B. D. Zill](https://doi.org/10.1109/INFCOM.1999.749256). 
The result is a minimal routing table. The `fill` variants will also add the root prefix (i.e., 
0.0.0.0/0), and fill holes with the default value.

## Other operations on the Tree

Most operations are bounded by prefix width, not by the number of stored entries. Let `w` be
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

## Zero-Copy Archives with `rkyv`

With the `rkyv` feature enabled, every map and set in this crate can be serialized into a byte
buffer and read back without a deserialization step. Each owned collection has an archived
counterpart: `ArchivedPrefixMap`, `ArchivedPrefixSet`, `ArchivedJointPrefixMap`, and
`ArchivedJointPrefixSet`. These types are validated once and then queried directly out of the
bytes. The archived types expose (or reimplement) all immutable access methods of their owned
counterparts, such as `get`, `get_lpm`, `get_spm`, `contains_key`, and the various iterators.

Archives integrate with the rest of the crate through the same `TrieView` infrastructure used by
the owned collections. `&ArchivedPrefixMap` and `&ArchivedPrefixSet` implement `AsView`, so any
function written against a `TrieView` accepts an archive just as it accepts a borrowed `PrefixMap`
or `PrefixSet`, and archives participate in the same set operations (`union`, `intersection`,
`difference`, and the covering variants) as owned tries. See the `rkyv` module docs for details
and examples.

## Comparison with related projects

[`ip_network_table-deps-treebitmap`](https://crates.io/crates/ip_network_table-deps-treebitmap) 
provides the same data structure (in the following called `TreeBitMap`) and uses a similar 
algorithm. Besides better performance than the `TreeBitMap`, `prefix-trie` includes a `PrefixSet` 
analogous to `std::collections::HashSet`. Set operations are exposed through composable trie views, 
so operations such as union, intersection, difference, covering union, and covering difference can 
be combined without building temporary maps. `prefix-trie` has an interface similar to 
`std::collections`, and its longest-prefix matching is not limited to individual host addresses.

The following table compares the performance and memory of the two libraries, and 
relates them to the `HashMap` and `BTreeMap` of the standard library. Throughput is reported 
relative to `HashMap` (1.00x = HashMap speed), with absolute throughput in parentheses. **Bold** 
marks the fastest implementation per row. See `benches/benchmark.rs` for details.

All benchmarks use IPv4 prefixes from a RIPE RIS peer snapshot (1,042,024 IPv4 prefixes or 
246,174 IPv6 prefixes). See `benches/benchmark.rs` and `benches/memory.rs` for details. The 
benchmark results below were obtained on an AMD EPYC server.

### Lookup

Exact lookup of a prefix, i.e. retrieving the value stored for a whole
prefix. Throughput is reported relative to `HashMap` (1.00x = HashMap
speed), with absolute throughput in parentheses. Benchmarked with two
workloads: prefixes drawn at random from the RIS initial state, and
prefixes observed in RIS routing-table updates.

| Benchmark       | `HashMap`               | `PrefixMap`             | `TreeBitMap`          | `BTreeMap`           |
|-----------------|-------------------------|-------------------------|-----------------------|----------------------|
| *Random access* |                         |                         |                       |                      |
| --> IPv4        |   1.00x (6.5 Mops/s)    | **1.86x (12.1 Mops/s)** |   1.22x (7.9 Mops/s)  |   0.48x (3.1 Mops/s) |
| --> IPv6        |   1.00x (9.4 Mops/s)    | **1.06x (10.0 Mops/s)** |   0.67x (6.4 Mops/s)  |   0.51x (4.8 Mops/s) |
| *RIS updates*   |                         |                         |                       |                      |
| --> IPv4        |   1.00x (15.1 Mops/s)   | **1.82x (27.6 Mops/s)** |   0.88x (13.3 Mops/s) |   0.52x (7.9 Mops/s) |
| --> IPv6        | **1.00x (22.0 Mops/s)** |   0.70x (15.5 Mops/s)   |   0.37x (8.1 Mops/s)  |   0.42x (9.3 Mops/s) |

### Insert & Remove

Applying a stream of insertions and removals to a pre-filled table.
Throughput is reported relative to `HashMap` (1.00x = HashMap speed),
with absolute throughput in parentheses. Benchmarked with two
workloads: random insert/remove pairs on prefixes drawn from the RIS
initial state, and the mutation stream observed from a RIS peer.

| Benchmark       | `HashMap`               | `PrefixMap`            | `TreeBitMap`          | `BTreeMap`           |
|-----------------|-------------------------|------------------------|-----------------------|----------------------|
| *Random access* |                         |                        |                       |                      |
| --> IPv4        |   1.00x (6.3 Mops/s)    | **1.07x (6.8 Mops/s)** |   1.04x (6.6 Mops/s)  |   0.44x (2.8 Mops/s) |
| --> IPv6        | **1.00x (9.5 Mops/s)**  |   0.51x (4.8 Mops/s)   |   0.51x (4.8 Mops/s)  |   0.46x (4.4 Mops/s) |
| *RIS updates*   |                         |                        |                       |                      |
| --> IPv4        | **1.00x (14.8 Mops/s)** |   0.91x (13.4 Mops/s)  |   0.85x (12.5 Mops/s) |   0.51x (7.5 Mops/s) |
| --> IPv6        | **1.00x (22.4 Mops/s)** |   0.37x (8.2 Mops/s)   |   0.33x (7.5 Mops/s)  |   0.40x (9.0 Mops/s) |

### Create

Building a table from scratch from the prefixes of the RIS initial
state. Throughput is reported relative to `HashMap` (1.00x = HashMap
speed), with absolute throughput in parentheses. Benchmarked with three
insertion orders: random, sorted (lexicographic), and scattered
(reversed-bit).

| Benchmark         | `HashMap`               | `PrefixMap`             | `TreeBitMap`          | `BTreeMap`           |
|-------------------|-------------------------|-------------------------|-----------------------|----------------------|
| *Random order*    |                         |                         |                       |                      |
| --> IPv4          | **1.00x (9.3 Mops/s)**  |   0.85x (7.9 Mops/s)    |   0.79x (7.3 Mops/s)  |   0.42x (3.9 Mops/s) |
| --> IPv6          | **1.00x (10.8 Mops/s)** |   0.53x (5.7 Mops/s)    |   0.46x (5.0 Mops/s)  |   0.44x (4.8 Mops/s) |
| *Sorted order*    |                         |                         |                       |                      |
| --> IPv4          |   1.00x (9.2 Mops/s)    | **1.45x (13.4 Mops/s)** |   1.22x (11.2 Mops/s) |   0.91x (8.4 Mops/s) |
| --> IPv6          | **1.00x (10.8 Mops/s)** |   0.72x (7.8 Mops/s)    |   0.61x (6.6 Mops/s)  |   0.68x (7.4 Mops/s) |
| *Scattered order* |                         |                         |                       |                      |
| --> IPv4          |   1.00x (9.2 Mops/s)    | **1.04x (9.6 Mops/s)**  |   0.81x (7.5 Mops/s)  |   0.33x (3.0 Mops/s) |
| --> IPv6          | **1.00x (10.9 Mops/s)** |   0.61x (6.6 Mops/s)    |   0.52x (5.7 Mops/s)  |   0.51x (5.6 Mops/s) |

### Longest-prefix match

Lookup of the longest matching prefix for random host addresses, each
drawn inside one of the prefixes of the RIS initial state, so that every
lookup has a match at some depth. `HashMap` and `BTreeMap` are omitted,
since they do not support longest-prefix match; throughput is reported
relative to `TreeBitMap` (1.00x = TreeBitMap speed), with absolute
throughput in parentheses.

| Benchmark | `PrefixMap`              | `TreeBitMap`          |
|-----------|--------------------------|-----------------------|
| IPv4      | **1.36x (22.9 Mops/s)**  |   1.00x (16.8 Mops/s) |
| IPv6      | **1.14x (104.7 Mops/s)** |   1.00x (91.9 Mops/s) |

### Clone

Copying an entire routing table built from the RIS initial state.
TrivialClone uses `u32` values; NonTrivialClone uses a wrapper whose
clone passes the value through `black_box`. `PrefixMap` uses its bulk
clone specialization for `u32` only with the `nightly` feature.
Throughput is measured in elements per second relative to `HashMap`
(1.00x = HashMap speed), with absolute throughput in parentheses.
elem/s is the number of elements in the table divided by the time to
copy it, not the number of whole-table copies per second.

| Benchmark         | `HashMap`                 | `PrefixMap`               | `TreeBitMap`            | `BTreeMap`             |
|-------------------|---------------------------|---------------------------|-------------------------|------------------------|
| *TrivialClone*    |                           |                           |                         |                        |
| --> IPv4          |   1.00x (361.9 Melem/s)   | **2.64x (953.9 Melem/s)** |   0.02x (6.1 Melem/s) † |   0.09x (32.9 Melem/s) |
| --> IPv6          |   1.00x (122.7 Melem/s)   | **12.76x (1.6 Gelem/s)**  |   0.03x (3.3 Melem/s) † |   0.35x (43.4 Melem/s) |
| *NonTrivialClone* |                           |                           |                         |                        |
| --> IPv4          | **1.00x (182.8 Melem/s)** |   0.67x (122.8 Melem/s)   |   0.03x (6.1 Melem/s) † |   0.16x (29.1 Melem/s) |
| --> IPv6          | **1.00x (102.7 Melem/s)** |   0.92x (94.0 Melem/s)    |   0.03x (3.3 Melem/s) † |   0.44x (44.8 Melem/s) |

† `TreeBitMap` does not implement `Clone`; it is copied by iterating the source table and rebuilding the copy.

### Iteration

Traversing and consuming all elements of a table built from the RIS
initial state, without sorting the output of the unordered maps.
Throughput is measured in elements per second and reported relative to
`HashMap` (1.00x = HashMap speed), with absolute throughput in parentheses.

| Benchmark | `HashMap`                 | `PrefixMap`              | `TreeBitMap`           | `BTreeMap`                |
|-----------|---------------------------|--------------------------|------------------------|---------------------------|
| IPv4      | **1.00x (430.0 Melem/s)** |   0.16x (68.1 Melem/s) † |   0.04x (15.4 Melem/s) |   0.12x (53.7 Melem/s) ‡  |
| IPv6      | **1.00x (418.7 Melem/s)** |   0.08x (32.1 Melem/s) † |   0.02x (7.5 Melem/s)  |   0.44x (182.6 Melem/s) ‡ |

† `PrefixMap` yields entries in lexicographic prefix order.
‡ `BTreeMap` yields entries in key order (the prefix type's `Ord` ordering).

### Aggregation

Aggregating the whole table built from the RIS initial state with
optimal routing table construction: `set` is the bitmap-only
`PrefixSet::aggregate` (drop + merge), `map` the value-aware
`PrefixMap::aggregate`, and `ortc` `PrefixMap::aggregate_fill_default`.
Each prefix is assigned a next hop from 1..=32 (emulating 32
interfaces), so the ORTC actually merges. Reported as absolute time per
full-table aggregation; the three variants perform different operations
and are not directly comparable.

| Benchmark | `set`   | `map`    | `ortc`   |
|-----------|---------|----------|----------|
| IPv4      |   26 ms |   464 ms |   498 ms |
| IPv6      |   14 ms |   215 ms |   241 ms |


## Migrate to version 0.9

Releases up to 0.8.4 used a binary tree representation.
With version 0.9, this crate migrated to a TreeBitMap, described by 
[W. Eatherton, Z. Dittia, and G. Varghes](https://dl.acm.org/doi/10.1145/997150.997160). This 
yields significant performance improvements (~8x faster inserts & lookups for all IPv4 addresses 
in internet routing tables) and memory reduction (~4x less).

However, this also comes with significant changes in the interface:
- Prefixes are reconstructed from the tree location and no longer stored.
  Consequently, information in the host part of an address is no longer maintained.
  Additionally, the function yields prefixes by value instead of by reference.
  If you wish to store the host-bits as well, consider constructing a type `PrefixMap<P, (P, T)>`.
- Mutable views of the tree can no longer modify the tree structure (to maintain memory safety).
  This is because one can construct two mutable views pointing to branches within the same 
  multi-bit node.
- Thanks to bitmaps, set operations can now be chained (as we can define a common interface for 
  them to return their bitmaps).
