//! # rkyv zero-copy deserialization.
//!
//! The archived version of a `PrefixMap` is extremely similar to the regular table representation
//! (5-level nodes, heaps of size 31), but read-only. Thus, they do not have an allocator. Instead
//! the data is saved in a contiguous array without empty spaces: Each node is allocated exactly by
//! its popcount (no exponential slots), and without a free list. The data layout is stored in a BFS
//! order to simplify validation and to improve cache locality for the hottest nodes (close to the
//! root).

#[cfg(test)]
mod test;

use core::error::Error;
use std::{
    collections::{HashSet, VecDeque},
    marker::PhantomData,
};

use crate::{
    allocator::Loc,
    table::{Table, K},
    Prefix, PrefixMap,
};
use rkyv::{
    bytecheck::{CheckBytes, Verify},
    munge::munge,
    rancor::{Fallible, Source},
    ser::{Allocator, Writer},
    traits::NoUndef,
    vec::{ArchivedVec, VecResolver},
    Archive, Deserialize, Place, Portable, Serialize,
};

#[repr(transparent)]
#[derive(Portable, CheckBytes)]
#[bytecheck(crate = rkyv::bytecheck)]
struct MyPhantomData<T>(PhantomData<T>);

// Safety: PhantomData is zero-sized, so it cannot have an undefined value by definition.
unsafe impl<T> NoUndef for MyPhantomData<T> {}

/// Rkyv representation of a node with compacted indices
#[derive(Archive, Serialize, Default)]
#[rkyv(derive(Debug))]
pub(crate) struct NodeRepr {
    pub(super) data_bitmap: u32,
    pub(super) child_bitmap: u32,
    pub(super) data_idx: u32,
    pub(super) children_idx: u32,
}

/// Archived (immutable) version of a [`PrefixMap`].
///
/// Any (verified) archived prefix map is canonical and has the following properties:
/// - The tree is stored as BFS (ordered per level).
/// - Data is stored contiguously without empty (uninitialized) memory in between.
/// - The root node is always present.
/// - No node (except the root) may be emtpy.
///
/// Due to these properties, assuming that T is also canonical (i.e., has only one possible
/// representation), you can compare two ArchivedPrefixMaps for equality by comparing their byte
/// string.
#[repr(C)]
#[derive(Portable, CheckBytes)]
#[bytecheck(verify, crate = rkyv::bytecheck)]
pub struct ArchivedPrefixMap<P, T: Archive> {
    nodes: ArchivedVec<ArchivedNodeRepr>,
    data: ArchivedVec<T::Archived>,
    _marker: MyPhantomData<P>,
}

pub struct PrefixMapResolver {
    nodes: VecResolver,
    nodes_len: usize,
    data: VecResolver,
    data_len: usize,
}

impl<P: Prefix, T: Archive> Archive for PrefixMap<P, T> {
    type Archived = ArchivedPrefixMap<P, T>;
    type Resolver = PrefixMapResolver;
    fn resolve(&self, resolver: Self::Resolver, out: Place<Self::Archived>) {
        munge!(let ArchivedPrefixMap { nodes, data, _marker } = out);
        ArchivedVec::resolve_from_len(resolver.nodes_len, resolver.nodes, nodes);
        ArchivedVec::resolve_from_len(resolver.data_len, resolver.data, data);
        _marker.write(MyPhantomData(PhantomData));
    }
}

impl<P, T, S> Serialize<S> for PrefixMap<P, T>
where
    P: Prefix,
    T: Serialize<S>,
    S: Fallible + Writer + Allocator + ?Sized,
{
    fn serialize(&self, s: &mut S) -> Result<PrefixMapResolver, S::Error> {
        let table = self.table();

        // pass 1: Identify empty nodes that do not need to be serialized
        let mut ignore = HashSet::new();
        fn find_empty<T>(table: &Table<T>, ignore: &mut HashSet<Loc>, loc: Loc) -> bool {
            let node = table.node(loc);
            let mut children_have_value = false;
            for child in node.child_locs() {
                children_have_value |= find_empty(table, ignore, child);
            }

            if loc.is_root() || children_have_value || node.data_bitmap != 0 {
                true
            } else {
                ignore.insert(loc);
                false
            }
        }
        find_empty(table, &mut ignore, Loc::root());

        // pass 2: the actual serialization
        let mut nodes = Vec::<NodeRepr>::new();
        let mut data = Vec::<&T>::with_capacity(self.count);
        let mut queue = VecDeque::new();
        nodes.push(NodeRepr::default());
        queue.push_back(Loc::root());

        let mut cur_node = 0;

        while let Some(loc) = queue.pop_front() {
            // ignore empty nodes
            if ignore.contains(&loc) {
                continue;
            }

            // update the node info
            let orig = table.node(loc);
            nodes[cur_node].data_bitmap = orig.data_bitmap;
            nodes[cur_node].child_bitmap = orig.child_bitmap;
            nodes[cur_node].data_idx = data.len() as u32;
            nodes[cur_node].children_idx = nodes.len() as u32;

            for child_loc in orig.child_locs() {
                // extend the nodes vector
                nodes.push(NodeRepr::default());
                // extend the queue
                queue.push_back(child_loc);
            }

            for data_loc in orig.data_locs() {
                // Safety: we get only live references from data_locs that are not modified since.
                data.push(unsafe { table.cell(data_loc) })
            }

            cur_node += 1;
        }

        debug_assert_eq!(cur_node, nodes.len());
        debug_assert_eq!(data.len(), self.count);

        let nodes_len = nodes.len();
        let data_len = data.len();
        let nodes = ArchivedVec::serialize_from_slice(&nodes, s)?;
        let data = ArchivedVec::serialize_from_iter::<T, _, _>(data.iter().copied(), s)?;

        Ok(PrefixMapResolver {
            nodes,
            nodes_len,
            data,
            data_len,
        })
    }
}

impl<P, T, D> Deserialize<PrefixMap<P, T>, D> for ArchivedPrefixMap<P, T>
where
    P: Prefix,
    T: Archive,
    T::Archived: Deserialize<T, D>,
    D: Fallible + ?Sized,
    D::Error: Source,
{
    fn deserialize(&self, d: &mut D) -> Result<PrefixMap<P, T>, D::Error> {
        let count = self.data.as_slice().len();
        let nodes = self
            .nodes
            .as_slice()
            .iter()
            .map(|n| (n.data_bitmap.to_native(), n.child_bitmap.to_native()));
        let data = self.data.as_slice().iter().map(|c| c.deserialize(d));

        let table = Table::from_bfs(nodes, data)?;
        Ok(PrefixMap::from_table_count(table, count))
    }
}

unsafe impl<P, T, C> Verify<C> for ArchivedPrefixMap<P, T>
where
    P: Prefix,
    T: Archive,
    C: Fallible + ?Sized,
    C::Error: Source,
{
    fn verify(&self, _context: &mut C) -> Result<(), C::Error> {
        if self.nodes.len() > 1 << 32 {
            Err(C::Error::new(ArchiveError::NodeIndexOverflow))?
        }
        if self.data.len() > 1 << 32 {
            Err(C::Error::new(ArchiveError::DataIndexOverflow))?
        }
        if self.nodes.is_empty() {
            Err(C::Error::new(ArchiveError::MissingRootNode))?
        }

        let mut child_cursor = 1;
        let mut data_cursor = 0;
        let mut cur_depth = 0;
        let mut next_depth = 1u32;

        let max_depth = P::num_bits();

        for i in 0..self.nodes.len() {
            let node = &self.nodes[i];
            // check non-empty (allow empty roots though)
            if i > 0 && node.data_bitmap == 0 && node.child_bitmap == 0 {
                Err(C::Error::new(ArchiveError::ContainsEmptyNode))?
            }

            // check the depth count
            if i as u32 == next_depth {
                cur_depth += K;
                next_depth = node.children_idx.to_native();
                if cur_depth > max_depth {
                    Err(C::Error::new(ArchiveError::DepthExceedsPrefixRepr))?
                }
            }

            // check max depth
            let max_allowed = u32::min(K - 1, max_depth - cur_depth);
            let denied_mask = DENIED_DEPTH_MASK[max_allowed as usize];
            if node.data_bitmap & denied_mask != 0 {
                Err(C::Error::new(ArchiveError::DepthExceedsPrefixRepr))?
            }

            if node.data_idx != data_cursor {
                Err(C::Error::new(ArchiveError::DataListInconsistent))?
            }
            data_cursor += node.data_bitmap.to_native().count_ones();
            if node.children_idx != child_cursor {
                Err(C::Error::new(ArchiveError::NodeListInconsistent))?
            }
            child_cursor += node.child_bitmap.to_native().count_ones();
        }

        match child_cursor.cmp(&(self.nodes.len() as u32)) {
            std::cmp::Ordering::Less => Err(C::Error::new(ArchiveError::NodeListTooShort))?,
            std::cmp::Ordering::Equal => {}
            std::cmp::Ordering::Greater => Err(C::Error::new(ArchiveError::NodeListTooLong))?,
        }
        match data_cursor.cmp(&(self.data.len() as u32)) {
            std::cmp::Ordering::Less => Err(C::Error::new(ArchiveError::DataListTooShort))?,
            std::cmp::Ordering::Equal => {}
            std::cmp::Ordering::Greater => Err(C::Error::new(ArchiveError::DataListTooLong))?,
        }

        Ok(())
    }
}

const DENIED_DEPTH_MASK: [u32; K as usize] = [
    !((1u32 << 1) - 1),  // m = 0: allow bit 0
    !((1u32 << 3) - 1),  // m = 1: allow bits 0..=2
    !((1u32 << 7) - 1),  // m = 2: allow bits 0..=6
    !((1u32 << 15) - 1), // m = 3: allow bits 0..=14
    !((1u32 << 31) - 1), // m = 4: allow bits 0..=30 (bit 31 denied = stray-bit check)
];

#[derive(Debug)]
pub enum ArchiveError {
    NodeListTooShort,
    NodeListTooLong,
    NodeListInconsistent,
    NodeIndexOverflow,
    DataListTooShort,
    DataListTooLong,
    DataListInconsistent,
    DataIndexOverflow,
    ContainsEmptyNode,
    MissingRootNode,
    DepthExceedsPrefixRepr,
}

impl Error for ArchiveError {}
impl std::fmt::Display for ArchiveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::NodeListTooShort => "Node list is too short",
            Self::NodeListTooLong => "Node list is too long",
            Self::NodeListInconsistent => "Inconsistent node list",
            Self::NodeIndexOverflow => "Node list too long for 32-bit index.",
            Self::DataListTooShort => "Data list is too short",
            Self::DataListTooLong => "Data list is too long",
            Self::DataListInconsistent => "Inconsistent data list",
            Self::DataIndexOverflow => "Data list too long for 32-bit index.",
            Self::ContainsEmptyNode => "Trie contains empty nodes.",
            Self::MissingRootNode => "Missing the root node.",
            Self::DepthExceedsPrefixRepr => {
                "Depth of tree exceeds the number of bits in the prefix."
            }
        };
        f.write_str(s)
    }
}
