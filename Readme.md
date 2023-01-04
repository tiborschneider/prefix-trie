![CI test](https://github.com/tiborschneider/prefix-trie/actions/workflows/test.yml/badge.svg)
[![codecov](https://codecov.io/gh/tiborschneider/prefix-trie/branch/main/graph/badge.svg?token=EEJXNNURMW)](https://codecov.io/gh/tiborschneider/prefix-trie)
![version](https://img.shields.io/crates/v/prefix-trie)
![downloads](https://img.shields.io/crates/d/prefix-trie)
![docs.rs](https://img.shields.io/docsrs/prefix-trie/latest)
![license](https://img.shields.io/crates/l/prefix-trie/0.2.2)

# Prefix-Trie

This crate provides a simple prefix tree for IP prefixes. The structure allows exact matches, as
well as longest-prefix matches. It contains several (simultaneous) tree traversals.
## Description of the Tree

The tree is structured as follows: Each node consists of a prefix, a container for a potential
value (`Option`), and two optional children. Adding a new child, or traversing into the tree is
done as follows: we look at the most significant bit that is **not** part of the prefix
itself. If it is not set, then we take the left branch, and otherwise, we take the right one.

## Traversals

Any iteration over all elements in the tree is implemented as a graph traversal that will yield
elements in lexicographic order (with the exception of mutable iteration of the
[`PrefixMap`]). This also includes the iteration over the union, intersection, or difference of
two [`PrefixSet`]s, which are implemented as simultaneous tree traversals. Further, calling
`retain` will also traverse the tree only once, removing elements during the traversal.

## Operations on the tree

There are several operations one can do on the tree. Regular inserts are handled using the
`Entry` structure. An `Entry` is a pointer to a location in the tree to either insert a value or
modify an existing one. Removals however are different.

The following are the computational complexities of the functions, where `n` is the number of
elements in the tree.

| Operation                                 | Complexity |
|-------------------------------------------|------------|
| `entry`, `insert`                         | `O(log n)` |
| `remove`, `remove_keep_tree`              | `O(log n)` |
| `remove_children` (calling `drop` on `T`) | `O(n)`     |
| `get`, `get_lpm`, `get_mut`               | `O(log n)` |
| `retain`                                  | `O(n)`     |
| `clear` (calling `drop` on `T`)           | `O(n)`     |
| Operations on [`map::Entry`]              | `O(1)`     |

There are three kinds of removals you! can do:

- [`PrefixMap::remove`] will remove an entry from the tree and modify the tree structure as if
  the value was never inserted before. [`PrefixMap::remove`] will always exactly revert the
  operation of [`PrefixMap::insert`]. When only calling this function to remove elements, you
  are guaranteed that the tree structure is indistinguishable to a different tree where you
  only inserted elements.
- [`PrefixMap::remove_children`] will remove all entries that are contained within the given
  prefix. This operation will search for the node with the shortest prefix length that is
  contained within the given prefix and remove it, including all of its children.
- [`PrefixMap::remove_keep_tree`] will not change anything in the tree structure. It will only
  remove a value from a node. As soon as you call `remove_keep_tree` once on a tree structure,
  the tree will no longer be optimal.
