use crate::{fuzzing::*, qc, PrefixMap};
use rkyv::{from_bytes, rancor::Error, to_bytes};

qc!(serialize_canonical_bytes, _serialize_canonical_bytes);
fn _serialize_canonical_bytes(list: Vec<Operation<TestPrefix, i32>>) -> bool {
    let mut pmap = PrefixMap::new();

    for op in list {
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

    let fresh: PrefixMap<_, _> = pmap.iter().map(|(p, t)| (p, *t)).collect();

    let pmap_bytes = to_bytes::<Error>(&pmap).unwrap();
    let fresh_bytes = to_bytes::<Error>(&fresh).unwrap();

    pmap_bytes.as_slice() == fresh_bytes.as_slice()
}

qc!(deserialize_validate, _deserialize_validate);
fn _deserialize_validate(list: Vec<Operation<TestPrefix, i32>>) -> bool {
    let mut pmap = PrefixMap::new();

    for op in list {
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

    let pmap_bytes = to_bytes::<Error>(&pmap).unwrap();
    let archived = from_bytes::<PrefixMap<TestPrefix, i32>, Error>(pmap_bytes.as_slice()).unwrap();

    pmap == archived
}
