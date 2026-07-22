use crate::{
    fuzzing::*,
    joint::{JointPrefixMap, JointPrefixSet},
    qc, PrefixMap, PrefixSet,
};
use rkyv::{access, from_bytes, rancor::Error, to_bytes};

macro_rules! rkyv_eq {
    ($var:ident . $fn:ident ()) => {{
        let a = $var.$fn();
        let b = rkyv_map(&$var, |x| x.$fn());
        a == b
    }};
    ($var:ident . $fn:ident ($($args:expr),*) $last:expr) => {{
        let a = $var.$fn($($args),*);
        let b = rkyv_map(&$var, |x| x.$fn($($args),*));
        a == b
    }};
}

macro_rules! rkyv_eq_test {
    ($fn:ident) => {
        paste::paste! {
            qc!($fn, [<_ $fn>]);
            fn [<_ $fn>](list: Vec<Operation<TestPrefix, i32>>) -> bool {
                let pmap = prepare(list);
                rkyv_eq!(pmap.$fn())
            }
        }
    };
}

fn rkyv_map<T, F, R>(data: &T, f: F) -> R
where
    T: rkyv::Archive
        + for<'a> rkyv::Serialize<
            rkyv::api::high::HighSerializer<
                rkyv::util::AlignedVec,
                rkyv::ser::allocator::ArenaHandle<'a>,
                Error,
            >,
        >,
    T::Archived: rkyv::Portable
        + for<'a> rkyv::bytecheck::CheckBytes<rkyv::api::high::HighValidator<'a, Error>>,
    F: for<'a> FnOnce(&'a T::Archived) -> R,
{
    let bytes = to_bytes::<Error>(data).unwrap();
    let archived = access::<_, Error>(bytes.as_slice()).unwrap();
    f(archived)
}

mod map {

    use super::*;

    fn prepare(ops: Vec<Operation<TestPrefix, i32>>) -> PrefixMap<TestPrefix, i32> {
        let mut pmap = PrefixMap::new();
        for op in ops {
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
    }

    qc!(serialize_canonical_bytes, _serialize_canonical_bytes);
    fn _serialize_canonical_bytes(list: Vec<Operation<TestPrefix, i32>>) -> bool {
        let pmap = prepare(list);
        let fresh: PrefixMap<_, _> = pmap.iter().map(|(p, t)| (p, *t)).collect();

        let pmap_bytes = to_bytes::<Error>(&pmap).unwrap();
        let fresh_bytes = to_bytes::<Error>(&fresh).unwrap();

        pmap_bytes.as_slice() == fresh_bytes.as_slice()
    }

    qc!(deserialize_validate, _deserialize_validate);
    fn _deserialize_validate(list: Vec<Operation<TestPrefix, i32>>) -> bool {
        let pmap = prepare(list);
        let pmap_bytes = to_bytes::<Error>(&pmap).unwrap();
        let archived =
            from_bytes::<PrefixMap<TestPrefix, i32>, Error>(pmap_bytes.as_slice()).unwrap();

        pmap == archived
    }

    rkyv_eq_test!(len);
    rkyv_eq_test!(is_empty);
    rkyv_eq_test!(address_count);
}

mod set {
    use super::*;

    fn prepare(ops: Vec<Operation<TestPrefix, ()>>) -> PrefixSet<TestPrefix> {
        let mut pset = PrefixSet::new();
        for op in ops {
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
    }

    qc!(serialize_canonical_bytes, _serialize_canonical_bytes);
    fn _serialize_canonical_bytes(list: Vec<Operation<TestPrefix, ()>>) -> bool {
        let pset = prepare(list);
        let fresh: PrefixSet<_> = pset.iter().collect();

        let pmap_bytes = to_bytes::<Error>(&pset).unwrap();
        let fresh_bytes = to_bytes::<Error>(&fresh).unwrap();

        pmap_bytes.as_slice() == fresh_bytes.as_slice()
    }

    qc!(deserialize_validate, _deserialize_validate);
    fn _deserialize_validate(list: Vec<Operation<TestPrefix, ()>>) -> bool {
        let pset = prepare(list);
        let pmap_bytes = to_bytes::<Error>(&pset).unwrap();
        let archived = from_bytes::<PrefixSet<TestPrefix>, Error>(pmap_bytes.as_slice()).unwrap();

        pset == archived
    }
}

mod joint_map {
    use super::*;

    fn prepare(ops: Vec<Operation<JointTestPrefix, i32>>) -> JointPrefixMap<JointTestPrefix, i32> {
        let mut pmap = JointPrefixMap::new();
        for op in ops {
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
    }

    qc!(serialize_canonical_bytes, _serialize_canonical_bytes);
    fn _serialize_canonical_bytes(list: Vec<Operation<JointTestPrefix, i32>>) -> bool {
        let pmap = prepare(list);

        let t1: PrefixMap<_, _> = pmap.t1.iter().map(|(p, t)| (p, *t)).collect();
        let t2: PrefixMap<_, _> = pmap.t2.iter().map(|(p, t)| (p, *t)).collect();
        let fresh = JointPrefixMap::<JointTestPrefix, _> { t1, t2 };

        let pmap_bytes = to_bytes::<Error>(&pmap).unwrap();
        let fresh_bytes = to_bytes::<Error>(&fresh).unwrap();

        pmap_bytes.as_slice() == fresh_bytes.as_slice()
    }

    qc!(deserialize_validate, _deserialize_validate);
    fn _deserialize_validate(list: Vec<Operation<JointTestPrefix, i32>>) -> bool {
        let pmap = prepare(list);

        let pmap_bytes = to_bytes::<Error>(&pmap).unwrap();
        let archived =
            from_bytes::<JointPrefixMap<JointTestPrefix, i32>, Error>(pmap_bytes.as_slice())
                .unwrap();

        pmap == archived
    }
}

mod joint_set {
    use super::*;

    fn prepare(ops: Vec<Operation<JointTestPrefix, ()>>) -> JointPrefixSet<JointTestPrefix> {
        let mut pset = JointPrefixSet::new();
        for op in ops {
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
    }

    qc!(serialize_canonical_bytes, _serialize_canonical_bytes);
    fn _serialize_canonical_bytes(list: Vec<Operation<JointTestPrefix, ()>>) -> bool {
        let pmap = prepare(list);

        let t1: PrefixSet<_> = pmap.t1.iter().collect();
        let t2: PrefixSet<_> = pmap.t2.iter().collect();
        let fresh = JointPrefixSet::<JointTestPrefix> { t1, t2 };

        let pmap_bytes = to_bytes::<Error>(&pmap).unwrap();
        let fresh_bytes = to_bytes::<Error>(&fresh).unwrap();

        pmap_bytes.as_slice() == fresh_bytes.as_slice()
    }

    qc!(deserialize_validate, _deserialize_validate);
    fn _deserialize_validate(list: Vec<Operation<JointTestPrefix, ()>>) -> bool {
        let pmap = prepare(list);
        let pmap_bytes = to_bytes::<Error>(&pmap).unwrap();
        let archived =
            from_bytes::<JointPrefixSet<JointTestPrefix>, Error>(pmap_bytes.as_slice()).unwrap();

        pmap == archived
    }
}
