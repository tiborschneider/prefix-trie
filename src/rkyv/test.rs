use crate::{
    fuzzing::*,
    joint::{JointPrefixMap, JointPrefixSet},
    qc,
    rkyv::{ArchivedJointPrefixMap, ArchivedJointPrefixSet, ArchivedPrefixMap, ArchivedPrefixSet},
    PrefixMap, PrefixSet,
};
use rkyv::{access, from_bytes, rancor::Error, to_bytes};

macro_rules! rkyv_eq_test {
    ($X:ident < $P:ident>, $fn:ident) => {
        paste::paste! {
            qc!($fn, [<_ $fn>]);
            fn [<_ $fn>](ops: Vec<Operation<$P, ()>>) -> bool {
                let pset = prepare!($X<$P>, ops);
                let a = pset.$fn();
                let bytes = to_bytes::<Error>(&pset).unwrap();
                let archived = access::<[<Archived $X>]::<$P>, Error>(bytes.as_slice()).unwrap();
                let b = archived.$fn();
                a == b
            }
        }
    };
    ($X:ident < $P:ident, i32 >, $fn:ident) => {
        paste::paste! {
            qc!($fn, [<_ $fn>]);
            fn [<_ $fn>](ops: Vec<Operation<$P, i32>>) -> bool {
                let pmap = prepare!($X<$P, i32>, ops);
                let a = pmap.$fn();
                let bytes = to_bytes::<Error>(&pmap).unwrap();
                let archived = access::<[<Archived $X>]::<$P, rkyv::rend::i32_le>, Error>(bytes.as_slice()).unwrap();
                let b = archived.$fn();
                a == b
            }
        }
    };
    ($X:ident < $P:ident>, $fn:ident, $arg:ty) => {
        paste::paste! {
            qc!($fn, [<_ $fn>]);
            fn [<_ $fn>]((ops, arg): (Vec<Operation<$P, ()>>, $arg)) -> bool {
                let pset = prepare!($X<$P>, ops);
                let a = pset.$fn(&arg);
                let bytes = to_bytes::<Error>(&pset).unwrap();
                let archived = access::<[<Archived $X>]::<$P>, Error>(bytes.as_slice()).unwrap();
                let b = archived.$fn(&arg);
                a == b
            }
        }
    };
    ($X:ident < $P:ident, i32 >, $fn:ident, $arg:ty) => {
        paste::paste! {
            qc!($fn, [<_ $fn>]);
            fn [<_ $fn>]((ops, arg): (Vec<Operation<$P, i32>>, $arg)) -> bool {
                let pmap = prepare!($X<$P, i32>, ops);
                let a = pmap.$fn(&arg);
                let bytes = to_bytes::<Error>(&pmap).unwrap();
                let archived = access::<[<Archived $X>]::<$P, rkyv::rend::i32_le>, Error>(bytes.as_slice()).unwrap();
                let b = archived.$fn(&arg);
                a == b
            }
        }
    };
    ($X:ident < $P:ident>, $fn:ident, $arg:ty, $map_a:expr, $map_b:expr) => {
        paste::paste! {
            qc!($fn, [<_ $fn>]);
            fn [<_ $fn>]((ops, arg): (Vec<Operation<$P, ()>>, $arg)) -> bool {
                let pset = prepare!($X<$P>, ops);
                let a = pset.$fn(&arg).map($map_a);
                let bytes = to_bytes::<Error>(&pset).unwrap();
                let archived = access::<[<Archived $X>]::<$P>, Error>(bytes.as_slice()).unwrap();
                let b = archived.$fn(&arg).map($map_b);
                a == b
            }
        }
    };
    ($X:ident < $P:ident, i32 >, $fn:ident, $arg:ty, $map_a:expr, $map_b:expr) => {
        paste::paste! {
            qc!($fn, [<_ $fn>]);
            fn [<_ $fn>]((ops, arg): (Vec<Operation<$P, i32>>, $arg)) -> bool {
                let pmap = prepare!($X<$P, i32>, ops);
                let a = pmap.$fn(&arg).map($map_a);
                let bytes = to_bytes::<Error>(&pmap).unwrap();
                let archived = access::<[<Archived $X>]::<$P, rkyv::rend::i32_le>, Error>(bytes.as_slice()).unwrap();
                let b = archived.$fn(&arg).map($map_b);
                a == b
            }
        }
    };
}

macro_rules! prepare {
    ($X:ident < $P:ident>, $ops:expr) => {{
        let mut pset = $X::<$P>::new();
        for op in $ops {
            match op {
                Operation::Add(p, _) => {
                    pset.insert(p);
                }
                Operation::Remove(p) => {
                    pset.remove(&p);
                }
                Operation::RemoveChildren(p) => {
                    pset.remove_children(&p);
                }
            }
        }
        pset
    }};
    ($X:ident < $P:ident, i32>, $ops:expr) => {{
        let mut pmap = $X::<$P, i32>::new();
        for op in $ops {
            match op {
                Operation::Add(p, t) => {
                    pmap.insert(p, t);
                }
                Operation::Remove(p) => {
                    pmap.remove(&p);
                }
                Operation::RemoveChildren(p) => {
                    pmap.remove_children(&p);
                }
            }
        }
        pmap
    }};
}

mod map {

    use super::*;
    type P = TestPrefix;

    qc!(serialize_canonical_bytes, _serialize_canonical_bytes);
    fn _serialize_canonical_bytes(list: Vec<Operation<P, i32>>) -> bool {
        let pmap = prepare!(PrefixMap<P, i32>, list);
        let fresh: PrefixMap<_, _> = pmap.iter().map(|(p, t)| (p, *t)).collect();

        let pmap_bytes = to_bytes::<Error>(&pmap).unwrap();
        let fresh_bytes = to_bytes::<Error>(&fresh).unwrap();

        pmap_bytes.as_slice() == fresh_bytes.as_slice()
    }

    qc!(deserialize_validate, _deserialize_validate);
    fn _deserialize_validate(list: Vec<Operation<P, i32>>) -> bool {
        let pmap = prepare!(PrefixMap<P, i32>, list);
        let pmap_bytes = to_bytes::<Error>(&pmap).unwrap();
        let archived = from_bytes::<PrefixMap<P, i32>, Error>(pmap_bytes.as_slice()).unwrap();

        pmap == archived
    }

    rkyv_eq_test!(PrefixMap<P, i32>, len);
    rkyv_eq_test!(PrefixMap<P, i32>, is_empty);
    rkyv_eq_test!(PrefixMap<P, i32>, address_count);
    rkyv_eq_test!(PrefixMap<P, i32>, get, P, |x| *x, |x| x.to_native());
    rkyv_eq_test!(PrefixMap<P, i32>, get_key_value, P, |(p, t)| (p, *t), |(p, t)| (p, t.to_native()));
    rkyv_eq_test!(PrefixMap<P, i32>, get_lpm, P, |(p, t)| (p, *t), |(p, t)| (p, t.to_native()));
}

mod set {
    use super::*;
    type P = TestPrefix;

    qc!(serialize_canonical_bytes, _serialize_canonical_bytes);
    fn _serialize_canonical_bytes(list: Vec<Operation<P, ()>>) -> bool {
        let pset = prepare!(PrefixSet<P>, list);
        let fresh: PrefixSet<_> = pset.iter().collect();

        let pmap_bytes = to_bytes::<Error>(&pset).unwrap();
        let fresh_bytes = to_bytes::<Error>(&fresh).unwrap();

        pmap_bytes.as_slice() == fresh_bytes.as_slice()
    }

    qc!(deserialize_validate, _deserialize_validate);
    fn _deserialize_validate(list: Vec<Operation<P, ()>>) -> bool {
        let pset = prepare!(PrefixSet<P>, list);
        let pmap_bytes = to_bytes::<Error>(&pset).unwrap();
        let archived = from_bytes::<PrefixSet<P>, Error>(pmap_bytes.as_slice()).unwrap();

        pset == archived
    }

    rkyv_eq_test!(PrefixSet<P>, len);
    rkyv_eq_test!(PrefixSet<P>, is_empty);
    rkyv_eq_test!(PrefixSet<P>, address_count);
    rkyv_eq_test!(PrefixSet<P>, contains, P);
    rkyv_eq_test!(PrefixSet<P>, get, P);
    rkyv_eq_test!(PrefixSet<P>, get_lpm, P);
}

mod joint_map {
    use super::*;
    type P = JointTestPrefix;

    qc!(serialize_canonical_bytes, _serialize_canonical_bytes);
    fn _serialize_canonical_bytes(list: Vec<Operation<P, i32>>) -> bool {
        let pmap = prepare!(JointPrefixMap<P, i32>, list);

        let t1: PrefixMap<_, _> = pmap.t1.iter().map(|(p, t)| (p, *t)).collect();
        let t2: PrefixMap<_, _> = pmap.t2.iter().map(|(p, t)| (p, *t)).collect();
        let fresh = JointPrefixMap::<P, _> { t1, t2 };

        let pmap_bytes = to_bytes::<Error>(&pmap).unwrap();
        let fresh_bytes = to_bytes::<Error>(&fresh).unwrap();

        pmap_bytes.as_slice() == fresh_bytes.as_slice()
    }

    qc!(deserialize_validate, _deserialize_validate);
    fn _deserialize_validate(list: Vec<Operation<P, i32>>) -> bool {
        let pmap = prepare!(JointPrefixMap<P, i32>, list);

        let pmap_bytes = to_bytes::<Error>(&pmap).unwrap();
        let archived = from_bytes::<JointPrefixMap<P, i32>, Error>(pmap_bytes.as_slice()).unwrap();

        pmap == archived
    }

    rkyv_eq_test!(JointPrefixMap<P, i32>, len);
    rkyv_eq_test!(JointPrefixMap<P, i32>, is_empty);
    rkyv_eq_test!(JointPrefixMap<P, i32>, address_count);
    rkyv_eq_test!(JointPrefixMap<P, i32>, get, P, |x| *x, |x| x.to_native());
    rkyv_eq_test!(JointPrefixMap<P, i32>, get_key_value, P, |(p, t)| (p, *t), |(p, t)| (p, t.to_native()));
    rkyv_eq_test!(JointPrefixMap<P, i32>, get_lpm, P, |(p, t)| (p, *t), |(p, t)| (p, t.to_native()));
}

mod joint_set {
    use super::*;
    type P = JointTestPrefix;

    qc!(serialize_canonical_bytes, _serialize_canonical_bytes);
    fn _serialize_canonical_bytes(list: Vec<Operation<P, ()>>) -> bool {
        let pset = prepare!(JointPrefixSet<P>, list);

        let t1: PrefixSet<_> = pset.t1.iter().collect();
        let t2: PrefixSet<_> = pset.t2.iter().collect();
        let fresh = JointPrefixSet::<P> { t1, t2 };

        let pset_bytes = to_bytes::<Error>(&pset).unwrap();
        let fresh_bytes = to_bytes::<Error>(&fresh).unwrap();

        pset_bytes.as_slice() == fresh_bytes.as_slice()
    }

    qc!(deserialize_validate, _deserialize_validate);
    fn _deserialize_validate(list: Vec<Operation<P, ()>>) -> bool {
        let pset = prepare!(JointPrefixSet<P>, list);
        let pset_bytes = to_bytes::<Error>(&pset).unwrap();
        let archived = from_bytes::<JointPrefixSet<P>, Error>(pset_bytes.as_slice()).unwrap();

        pset == archived
    }

    rkyv_eq_test!(JointPrefixSet<P>, len);
    rkyv_eq_test!(JointPrefixSet<P>, is_empty);
    rkyv_eq_test!(JointPrefixSet<P>, address_count);
    rkyv_eq_test!(JointPrefixSet<P>, contains, P);
    rkyv_eq_test!(JointPrefixSet<P>, get, P);
    rkyv_eq_test!(JointPrefixSet<P>, get_lpm, P);
}
