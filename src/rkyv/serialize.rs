//! Serialization logic for rkyv

use std::{
    collections::{HashSet, VecDeque},
    marker::PhantomData,
};

use crate::{
    allocator::Loc,
    joint::{JointPrefix, JointPrefixMap, JointPrefixSet},
    rkyv::{
        ArchivedJointPrefixMap, ArchivedJointPrefixSet, ArchivedPrefixMap, ArchivedPrefixSet,
        MyPhantomData, NodeRepr, PrefixMapResolver,
    },
    table::Table,
    Prefix, PrefixMap, PrefixSet,
};
use rkyv::{
    munge::munge,
    rancor::Fallible,
    ser::{Allocator, Writer},
    vec::ArchivedVec,
    Archive, Place, Serialize,
};

use super::JointPrefixMapResolver;

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

impl<P: Prefix> Archive for PrefixSet<P> {
    type Archived = ArchivedPrefixSet<P>;
    type Resolver = PrefixMapResolver;
    fn resolve(&self, resolver: Self::Resolver, out: Place<Self::Archived>) {
        munge!(let ArchivedPrefixSet(out) = out);
        self.0.resolve(resolver, out)
    }
}

impl<P: JointPrefix, T: Archive> Archive for JointPrefixMap<P, T> {
    type Archived = ArchivedJointPrefixMap<P, T>;
    type Resolver = JointPrefixMapResolver;
    fn resolve(&self, resolver: Self::Resolver, out: Place<Self::Archived>) {
        munge!(let ArchivedJointPrefixMap {t1, t2} = out);
        self.t1.resolve(resolver.t1, t1);
        self.t2.resolve(resolver.t2, t2);
    }
}

impl<P: JointPrefix> Archive for JointPrefixSet<P> {
    type Archived = ArchivedJointPrefixSet<P>;
    type Resolver = JointPrefixMapResolver;
    fn resolve(&self, resolver: Self::Resolver, out: Place<Self::Archived>) {
        munge!(let ArchivedJointPrefixSet {t1, t2} = out);
        self.t1.resolve(resolver.t1, t1);
        self.t2.resolve(resolver.t2, t2);
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

impl<P, S> Serialize<S> for PrefixSet<P>
where
    P: Prefix,
    S: Fallible + Writer + Allocator + ?Sized,
{
    fn serialize(&self, s: &mut S) -> Result<PrefixMapResolver, S::Error> {
        self.0.serialize(s)
    }
}

impl<P, T, S> Serialize<S> for JointPrefixMap<P, T>
where
    P: JointPrefix,
    T: Archive + Serialize<S>,
    S: Fallible + Writer + Allocator + ?Sized,
{
    fn serialize(&self, s: &mut S) -> Result<JointPrefixMapResolver, S::Error> {
        let t1 = self.t1.serialize(s)?;
        let t2 = self.t2.serialize(s)?;
        Ok(JointPrefixMapResolver { t1, t2 })
    }
}

impl<P, S> Serialize<S> for JointPrefixSet<P>
where
    P: JointPrefix,
    S: Fallible + Writer + Allocator + ?Sized,
{
    fn serialize(&self, s: &mut S) -> Result<JointPrefixMapResolver, S::Error> {
        let t1 = self.t1.serialize(s)?;
        let t2 = self.t2.serialize(s)?;
        Ok(JointPrefixMapResolver { t1, t2 })
    }
}
