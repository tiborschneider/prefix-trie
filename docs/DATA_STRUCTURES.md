# Data Structures Report: `prefix-trie`

## Overview

`prefix-trie` is a Rust crate implementing a binary prefix tree (trie) for IP prefixes. It provides `PrefixMap<P, T>` (key-value) and `PrefixSet<P>` (set-only) types supporting longest-prefix matching, along with set-algebraic operations (union, intersection, difference) via `TrieView`/`TrieViewMut`. The data structure is generic over any prefix type satisfying the `Prefix` trait.

All types use Rust's default (`repr(Rust)`) layout. There are no `#[repr(C)]`, `#[repr(packed)]`, or `#[repr(align)]` annotations anywhere in the codebase.

---

## 1. `Node<P, T>` — The Core Trie Node

**Definition** (`src/inner.rs:11`):

```rust
struct Node<P, T> {
    prefix: P,
    value:  Option<T>,
    left:   Option<NonZeroUsize>,   // index of left child (bit=0)
    right:  Option<NonZeroUsize>,   // index of right child (bit=1)
}
```

Each node stores a prefix, an optional value, and two optional child indices. Children are referenced by `NonZeroUsize` index into a backing `Vec`, not by pointer — this keeps all nodes in a single contiguous allocation. Since index 0 is always the root sentinel node and never a child, `NonZeroUsize` is a valid representation for all child indices, and `Option<NonZeroUsize>` exploits niche optimization to be the same size as `usize` (8 bytes instead of the 16 bytes that `Option<usize>` would require).

**Memory layout** (measured on aarch64, 64-bit):

| Instantiation | Size | Align | Notes |
|---|---|---|---|
| `Node<Ipv4Net, u32>` | 32 B | 8 | Ipv4Net is 5 B; both children fit in 16 B total |
| `Node<Ipv4Net, ()>` | 24 B | 8 | PrefixSet nodes — no value overhead beyond discriminant |
| `Node<Ipv6Net, u32>` | 48 B | 8 | Ipv6Net is 17 B |
| `Node<Ipv6Net, ()>` | 40 B | 8 | |
| `Node<(u32,u8), u32>` | 32 B | 8 | Same as Ipv4Net variant |
| `Node<(u32,u8), ()>` | 32 B | 8 | |
| `Node<(u128,u8), u64>` | 64 B | 16 | u128 forces 16-byte alignment |

**Alignment analysis**: `Option<NonZeroUsize>` is 8 bytes thanks to niche optimization — the compiler uses the bit pattern `0` (which `NonZeroUsize` can never be) to represent `None`, eliminating the need for a separate discriminant. The two child fields together consume only 16 bytes. The remaining space for `prefix` + `value` depends on their types, with padding inserted as needed to reach 8-byte boundaries.

The `()` value type in `PrefixSet` still requires a 1-byte `Option<()>` discriminant for presence tracking, but the compiler reorders and packs fields to minimize waste.

---

## 2. `Table<P, T>` — Interior-Mutable Node Storage

**Definition** (`src/inner.rs:37`):

```rust
struct Table<P, T>(UnsafeCell<Vec<Node<P, T>>>);
```

A zero-overhead wrapper around `UnsafeCell<Vec<Node<P, T>>>`. All instantiations are **24 bytes** (the size of `Vec<_>`: pointer + length + capacity), at 8-byte alignment. `UnsafeCell` is a transparent wrapper and introduces no size/alignment overhead.

`Table` provides interior mutability for the tree's node storage. This enables `TrieViewMut` to hand out `&mut Node` references from an `&Table` reference, which is required for allowing multiple non-overlapping mutable sub-tree views to coexist.

**Unsafe code** (`src/inner.rs:137-152`): The `get_mut` method manually computes pointer offsets (`ptr.add(idx)`) rather than using `&mut vec[idx]`. This was a deliberate choice to avoid Miri stacked-borrows violations — indexing through `&mut Vec` would create a mutable reference to the entire slice, conflicting with other references. The manual pointer arithmetic creates only a narrow `&mut Node` at the target index.

`Send`/`Sync` are manually implemented with documented safety invariants: the view system guarantees non-overlapping mutable access across threads.

---

## 3. `PrefixMap<P, T>` — The Public Map Type

**Definition** (`src/map/mod.rs:20`):

```rust
struct PrefixMap<P, T> {
    table: Table<P, T>,   // 24 B — the node storage
    free:  Vec<usize>,     // 24 B — free-list of reusable node indices
    count: usize,          //  8 B — number of entries with values
}
```

Always **56 bytes** at 8-byte alignment, regardless of `P` and `T`, since all three fields are indirections (two `Vec`s on the heap + a counter). The `free` list enables O(1) index recycling on `remove` without compacting the `Vec`.

On construction (`Default`), the table is initialized with a single root node at index 0 with `P::zero()` (the 0.0.0.0/0 or ::/0 equivalent) and no value. This sentinel root is never removed.

---

## 4. `PrefixSet<P>` — The Public Set Type

**Definition** (`src/set.rs:11`):

```rust
struct PrefixSet<P>(PrefixMap<P, ()>);
```

A newtype around `PrefixMap<P, ()>`. Always **56 bytes** at 8-byte alignment. The `()` value type means each node carries only the 1-byte `Option<()>` discriminant overhead for presence tracking.

---

## 5. `TrieView<'a, P, T>` and `TrieViewMut<'a, P, T>` — Sub-Trie References

**Definitions** (`src/trieview/mod.rs:108, 695`):

```rust
struct TrieView<'a, P, T> {
    table: &'a Table<P, T>,   // 8 B — shared reference
    loc:   ViewLoc<P>,         // size depends on P
}

struct TrieViewMut<'a, P, T> {
    table: &'a Table<P, T>,   // 8 B — shared ref (interior mutability)
    loc:   ViewLoc<P>,
}

enum ViewLoc<P> {
    Node(usize),           // view points to an actual tree node
    Virtual(P, usize),     // view points to a virtual (implicit) node
}
```

Both view types store an immutable reference to the `Table` — `TrieViewMut` gets mutable access via `Table::get_mut` (interior mutability). The `ViewLoc` enum differentiates between a view rooted at a real node in the tree vs. a "virtual" node (a prefix not materially present in the tree but logically between existing nodes).

| Instantiation | Size | Align | Notes |
|---|---|---|---|
| `TrieView<Ipv4Net, _>` | 24 B | 8 | `ViewLoc<Ipv4Net>`: 16 B (5 B prefix + discriminant + usize, padded) |
| `TrieView<Ipv6Net, _>` | 40 B | 8 | `ViewLoc<Ipv6Net>`: 32 B (17 B prefix + padding + usize) |
| `TrieViewMut<Ipv4Net, _>` | 24 B | 8 | Same layout as `TrieView` |
| `TrieViewMut<Ipv6Net, _>` | 40 B | 8 | |

`TrieView` is `Copy` when `P: Copy`. `TrieViewMut` is intentionally not `Copy` to enforce unique-reference semantics.

---

## 6. `Direction` and `DirectionForInsert<P>` — Navigation Enums

**Definitions** (`src/inner.rs:99, 108`):

```rust
enum Direction {
    Reached,
    Enter { next: usize, right: bool },
    Missing,
}

enum DirectionForInsert<P> {
    Reached,
    Enter { next: usize, right: bool },
    NewLeaf { right: bool },
    NewChild { right: bool, child_right: bool },
    NewBranch { branch_prefix: P, right: bool, prefix_right: bool },
}
```

`Direction` is always **16 bytes** (the `Enter` variant needs `usize` + `bool`, padded to 8-byte alignment plus discriminant).

`DirectionForInsert` is also **16 bytes** for both `Ipv4Net` and `(u32, u8)` instantiations. The `NewBranch` variant is the largest, carrying a prefix value and two bools, but Rust's enum layout optimization keeps it compact because `Ipv4Net` and `(u32, u8)` are small enough (5 and 8 bytes respectively) to fit in the same space as `usize + bool`.

---

## 7. `Entry<'a, P, T>`, `VacantEntry`, `OccupiedEntry`

**Definitions** (`src/map/entry.rs:6, 15, 24`):

```rust
enum Entry<'a, P, T> {
    Vacant(VacantEntry<'a, P, T>),
    Occupied(OccupiedEntry<'a, P, T>),
}

struct VacantEntry<'a, P, T> {
    map:       &'a mut PrefixMap<P, T>,   // 8 B
    prefix:    P,
    idx:       usize,                      // 8 B
    direction: DirectionForInsert<P>,      // 16 B (for Ipv4Net)
}

struct OccupiedEntry<'a, P, T> {
    node:   &'a mut Node<P, T>,   // 8 B
    prefix: P,
}
```

`VacantEntry` captures the *path* taken during lookup so that subsequent insertion is O(1). For `Ipv4Net`:
- `VacantEntry<Ipv4Net, u32>`: 40 B (pointer + 5 B prefix padded + usize + 16 B direction)
- `OccupiedEntry<Ipv4Net, u32>`: 16 B (pointer + 5 B prefix padded)
- `Entry<Ipv4Net, u32>`: 40 B (sized to the larger variant)

---

## 8. `JointPrefixMap<P, T>` and `JointPrefixSet<P>`

**Definitions** (`src/joint/map/mod.rs:21`, `src/joint/set.rs`):

```rust
struct JointPrefixMap<P: JointPrefix, T> {
    pub t1: PrefixMap<P::P1, T>,   // 56 B
    pub t2: PrefixMap<P::P2, T>,   // 56 B
}

struct JointPrefixSet<P: JointPrefix> {
    pub t1: PrefixSet<P::P1>,      // 56 B
    pub t2: PrefixSet<P::P2>,      // 56 B
}
```

These are simple compositions — two independent prefix tries, typically one for IPv4 and one for IPv6. **112 bytes** each, at 8-byte alignment. No shared state between the two sub-trees.

---

## 9. Iterator Types

| Type | Size | Composition |
|---|---|---|
| `Iter<'a, P, T>` | 32 B | `Option<&Table>` (8 B via niche) + `Vec<usize>` (24 B) stack |
| `IterMut<'a, P, T>` | 32 B | Same layout as `Iter` |
| `IntoIter<P, T>` | 48 B | `Vec<Node<P, T>>` (24 B) + `Vec<usize>` (24 B) |
| `Keys`, `Values`, `ValuesMut` | 32 B | Newtypes around `Iter`/`IterMut` |
| `Cover<'a, 'p, P, T>` | 24 B | `&Table` + `Option<usize>` + `&P` |

All iterators use a `Vec<usize>` as a DFS traversal stack, pushing right-then-left child indices to achieve lexicographic (left-before-right) ordering.

---

## 10. The `Prefix` Trait and Its Representations

**Definition** (`src/prefix.rs:12`):

```rust
trait Prefix: Sized + Debug {
    type R: Unsigned + PrimInt + Zero + CheckedShr;
    fn repr(&self) -> Self::R;
    fn prefix_len(&self) -> u8;
    fn from_repr_len(repr: Self::R, len: u8) -> Self;
    // ... provided methods: mask, zero, longest_common_prefix, contains, is_bit_set, eq
}
```

The trait abstracts over any type that can be decomposed into a fixed-width unsigned integer representation (`R`) and a prefix length (`u8`). Implementations:

| Type | `R` | Size | Align | Source |
|---|---|---|---|---|
| `Ipv4Net` | `u32` | 5 B | 1 | ipnet crate |
| `Ipv6Net` | `u128` | 17 B | 1 | ipnet crate |
| `Ipv4Network` | `u32` | — | — | ipnetwork crate |
| `Ipv6Network` | `u128` | — | — | ipnetwork crate |
| `Ipv4Cidr` / `Ipv4Inet` | `u32` | — | — | cidr crate |
| `Ipv6Cidr` / `Ipv6Inet` | `u128` | — | — | cidr crate |
| `(R, u8)` for any `R` | `R` | varies | `align_of::<R>()` | built-in |

Notable: `Ipv4Net` and `Ipv6Net` from the `ipnet` crate are packed at 1-byte alignment (5 and 17 bytes respectively), which means no internal padding. However, when embedded in `Node`, the surrounding `Option<usize>` fields force 8-byte alignment, introducing padding around the prefix field. The tuple `(u32, u8)` has 4-byte alignment and is 8 bytes (with 3 bytes internal padding), yet `Node<(u32,u8), u32>` ends up the same 48 bytes as `Node<Ipv4Net, u32>` — Rust's layout optimizer absorbs the size difference into the same padded structure.

---

## 11. Summary of Memory Characteristics

**Storage model**: Arena-style allocation. All nodes live in a single `Vec<Node<P, T>>`. Deleted node slots are tracked in a free-list (`Vec<usize>`) and reused on subsequent insertions. This avoids heap fragmentation and provides excellent spatial locality for tree traversals.

**Niche optimization on children**: Child indices use `Option<NonZeroUsize>` instead of `Option<usize>`. Since index 0 is reserved for the root sentinel and is never a child, `NonZeroUsize` is valid for all child indices. The compiler exploits the niche (the bit pattern `0`) to store `None` without a separate discriminant, making `Option<NonZeroUsize>` just 8 bytes — the same as a plain `usize`. This saves 16 bytes per node compared to `Option<usize>`.

**No `#[repr]` annotations**: All types use Rust's default layout, meaning the compiler is free to reorder fields for better packing. This is observable — e.g., `Node<Ipv4Net, ()>` is 24 bytes, showing the compiler packs the small prefix and discriminant efficiently.

**Per-node overhead**: For the common `PrefixMap<Ipv4Net, u32>` case, each node is 32 bytes. Of that, 5 bytes are the prefix, 4 bytes the value, and 16 bytes are the two `Option<NonZeroUsize>` child indices — the remaining 7 bytes are alignment padding and the `Option<T>` discriminant.

**Constant-size top-level types**: `PrefixMap`, `PrefixSet`, and all view/iterator types have sizes independent of `P` and `T` (except views, which carry a `ViewLoc<P>`). The generic type parameters only affect heap-allocated node sizes.
