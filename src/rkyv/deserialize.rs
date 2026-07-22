//! Deserialization logic for rkyv

use crate::{
    joint::{JointPrefix, JointPrefixMap, JointPrefixSet},
    rkyv::{ArchivedJointPrefixMap, ArchivedJointPrefixSet, ArchivedPrefixMap, ArchivedPrefixSet},
    table::Table,
    Prefix, PrefixMap, PrefixSet,
};
use rkyv::{
    rancor::{Fallible, Source},
    Archive, Deserialize,
};

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

impl<P, D> Deserialize<PrefixSet<P>, D> for ArchivedPrefixSet<P>
where
    P: Prefix,
    D: Fallible + ?Sized,
    D::Error: Source,
{
    fn deserialize(&self, d: &mut D) -> Result<PrefixSet<P>, D::Error> {
        self.0.deserialize(d).map(PrefixSet)
    }
}

impl<P, T, D> Deserialize<JointPrefixMap<P, T>, D> for ArchivedJointPrefixMap<P, T>
where
    P: JointPrefix,
    T: Archive,
    T::Archived: Deserialize<T, D>,
    D: Fallible + ?Sized,
    D::Error: Source,
{
    fn deserialize(&self, d: &mut D) -> Result<JointPrefixMap<P, T>, D::Error> {
        let t1 = self.t1.deserialize(d)?;
        let t2 = self.t2.deserialize(d)?;
        Ok(JointPrefixMap { t1, t2 })
    }
}

impl<P, D> Deserialize<JointPrefixSet<P>, D> for ArchivedJointPrefixSet<P>
where
    P: JointPrefix,
    D: Fallible + ?Sized,
    D::Error: Source,
{
    fn deserialize(&self, d: &mut D) -> Result<JointPrefixSet<P>, D::Error> {
        let t1 = self.t1.deserialize(d)?;
        let t2 = self.t2.deserialize(d)?;
        Ok(JointPrefixSet { t1, t2 })
    }
}
