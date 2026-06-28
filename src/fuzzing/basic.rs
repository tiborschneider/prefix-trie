use std::collections::HashMap;

use super::*;
use itertools::Itertools;

fn expected_cover(map: &PrefixMap<TestPrefix, i32>, query: &TestPrefix) -> Vec<(TestPrefix, i32)> {
    let mut want = map
        .iter()
        .filter(|(prefix, _)| prefix.contains(query))
        .map(|(prefix, value)| (prefix, *value))
        .collect::<Vec<_>>();
    want.sort_by_key(|(prefix, _)| prefix.prefix_len());
    want
}

fn expected_cover_from_ref(
    reference: &HashMap<TestPrefix, i32>,
    query: &TestPrefix,
) -> Vec<(TestPrefix, i32)> {
    let mut want = reference
        .iter()
        .filter(|(prefix, _)| prefix.contains(query))
        .map(|(prefix, value)| (*prefix, *value))
        .collect::<Vec<_>>();
    want.sort_by_key(|(prefix, _)| prefix.prefix_len());
    want
}

fn expected_set_cover(set: &PrefixSet<TestPrefix>, query: &TestPrefix) -> Vec<TestPrefix> {
    let mut want = set
        .iter()
        .filter(|prefix| prefix.contains(query))
        .collect::<Vec<_>>();
    want.sort_by_key(Prefix::prefix_len);
    want
}

qc!(new, _new);
fn _new(list: Vec<(TestPrefix, i32)>) -> bool {
    let mut pmap = PrefixMap::new();
    let mut hmap = HashMap::new();

    for (p, t) in list {
        pmap.insert(p, t);
        hmap.insert(p, t);
    }

    pmap.check_memory_alloc() && pmap.into_iter().eq(hmap.into_iter().sorted())
}

qc!(new_mods, _new_mods);
fn _new_mods(list: Vec<Operation<TestPrefix, i32>>) -> bool {
    let mut pmap = PrefixMap::new();
    let mut hmap = HashMap::new();

    for op in list {
        match op {
            Operation::Add(p, t) => {
                pmap.insert(p, t);
                hmap.insert(p, t);
            }
            Operation::Remove(p) => {
                pmap.remove(&p);
                hmap.remove(&p);
            }
            Operation::RemoveChildren(p) => {
                pmap.remove_children(&p);
                hmap.retain(|x, _| !p.contains(x));
            }
        }
    }

    pmap.check_memory_alloc() && pmap.into_iter().eq(hmap.into_iter().sorted())
}

qc!(new_mods_vec, _new_mods_vec);
fn _new_mods_vec(list: Vec<Operation<TestPrefix, i32>>) -> bool {
    let mut pmap = PrefixMap::new();
    let mut hmap = HashMap::new();

    for op in list {
        match op {
            Operation::Add(p, t) => {
                pmap.insert(p, vec![t]);
                hmap.insert(p, vec![t]);
            }
            Operation::Remove(p) => {
                pmap.remove(&p);
                hmap.remove(&p);
            }
            Operation::RemoveChildren(p) => {
                pmap.remove_children(&p);
                hmap.retain(|x, _| !p.contains(x));
            }
        }
    }

    pmap.check_memory_alloc() && pmap.into_iter().eq(hmap.into_iter().sorted())
}

qc!(mods_clone, _mods_clone);
fn _mods_clone(list: Vec<Operation<TestPrefix, i32>>) -> bool {
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

    if !pmap.check_memory_alloc() {
        return false;
    }

    let cloned = pmap.clone();

    if !cloned.check_memory_alloc() {
        return false;
    }

    cloned == pmap
}

qc!(new_mods_entry, _new_mods_entry);
fn _new_mods_entry(list: Vec<Operation<TestPrefix, i32>>) -> bool {
    let mut pmap = PrefixMap::new();
    let mut hmap = HashMap::new();

    for op in list {
        match op {
            Operation::Add(p, t) => {
                let _ = pmap.entry(p).insert(t);
                hmap.insert(p, t);
            }
            Operation::Remove(p) => {
                pmap.remove(&p);
                hmap.remove(&p);
            }
            Operation::RemoveChildren(p) => {
                pmap.remove_children(&p);
                hmap.retain(|x, _| !p.contains(x));
            }
        }
    }

    pmap.check_memory_alloc() && pmap.into_iter().eq(hmap.into_iter().sorted())
}

qc!(equality, _equality);
fn _equality(list: Vec<Operation<TestPrefix, i32>>) -> bool {
    let mut map = PrefixMap::default();

    for op in list {
        match op {
            Operation::Add(p, t) => {
                map.insert(p, t);
            }
            Operation::Remove(p) => {
                map.remove(&p);
            }
            Operation::RemoveChildren(p) => {
                map.remove_children(&p);
            }
        }
    }

    let clone = map.clone().into_iter().collect::<PrefixMap<_, _>>();

    // assert that the iterator of both is the same
    map == clone && map.len() == clone.len() && map.is_empty() == clone.is_empty()
}

qc!(equality_keep_tree, _equality_keep_tree);
fn _equality_keep_tree(list: Vec<Operation<TestPrefix, i32>>) -> bool {
    let mut map = PrefixMap::default();

    for op in list {
        match op {
            Operation::Add(p, t) => {
                map.insert(p, t);
            }
            Operation::Remove(p) => {
                map.remove_keep_tree(&p);
            }
            Operation::RemoveChildren(p) => {
                map.remove_children(&p);
            }
        }
    }

    let clone = map.clone().into_iter().collect::<PrefixMap<_, _>>();

    // assert that the iterator of both is the same
    map == clone && map.len() == clone.len() && map.is_empty() == clone.is_empty()
}

qc!(equality_set, _equality_set);
fn _equality_set(list: Vec<Operation<TestPrefix, ()>>) -> bool {
    let mut set = PrefixSet::default();

    for op in list {
        match op {
            Operation::Add(p, _) => {
                set.insert(p);
            }
            Operation::Remove(p) => {
                set.remove(&p);
            }
            Operation::RemoveChildren(p) => {
                set.remove_children(&p);
            }
        }
    }

    let clone = set.iter().collect::<PrefixSet<_>>();

    // assert that the iterator of both is the same
    set == clone && set.len() == clone.len() && set.is_empty() == clone.is_empty()
}

qc!(inequality, _inequality);
fn _inequality((list, toggle): (Vec<Operation<TestPrefix, i32>>, TestPrefix)) -> bool {
    let mut map = PrefixMap::default();

    for op in list {
        match op {
            Operation::Add(p, t) => {
                map.insert(p, t);
            }
            Operation::Remove(p) => {
                map.remove(&p);
            }
            Operation::RemoveChildren(p) => {
                map.remove_children(&p);
            }
        }
    }

    let clone = map.clone().into_iter().collect::<PrefixMap<_, _>>();
    if map.contains_key(&toggle) {
        map.remove(&toggle);
    } else {
        map.insert(toggle, 0);
    }
    map != clone
}

qc!(inequality_set, _inequality_set);
fn _inequality_set((list, toggle): (Vec<Operation<TestPrefix, ()>>, TestPrefix)) -> bool {
    let mut set = PrefixSet::default();

    for op in list {
        match op {
            Operation::Add(p, _) => {
                set.insert(p);
            }
            Operation::Remove(p) => {
                set.remove(&p);
            }
            Operation::RemoveChildren(p) => {
                set.remove_children(&p);
            }
        }
    }

    let clone = set.iter().collect::<PrefixSet<_>>();
    if set.contains(&toggle) {
        set.remove(&toggle);
    } else {
        set.insert(toggle);
    }
    set != clone
}

// `PrefixSet` is `PrefixMap<P, ()>`, whose ZST cell allocator takes a different code
// path (shared dummy region, no free list). These mutate a set and assert the allocator
// stays consistent via `check_memory_alloc`, comparing against a `HashSet` reference.

qc!(new_mods_set, _new_mods_set);
fn _new_mods_set(list: Vec<Operation<TestPrefix, ()>>) -> bool {
    let mut set = PrefixSet::new();
    let mut href = std::collections::HashSet::new();

    for op in list {
        match op {
            Operation::Add(p, ()) => {
                set.insert(p);
                href.insert(p);
            }
            Operation::Remove(p) => {
                set.remove(&p);
                href.remove(&p);
            }
            Operation::RemoveChildren(p) => {
                set.remove_children(&p);
                href.retain(|x| !p.contains(x));
            }
        }
    }

    set.0.check_memory_alloc() && set.into_iter().eq(href.into_iter().sorted())
}

qc!(mods_clone_set, _mods_clone_set);
fn _mods_clone_set(list: Vec<Operation<TestPrefix, ()>>) -> bool {
    let mut set = PrefixSet::new();

    for op in list {
        match op {
            Operation::Add(p, ()) => {
                set.insert(p);
            }
            Operation::Remove(p) => {
                set.remove(&p);
            }
            Operation::RemoveChildren(p) => {
                set.remove_children(&p);
            }
        }
    }

    if !set.0.check_memory_alloc() {
        return false;
    }

    let cloned = set.clone();

    cloned.0.check_memory_alloc() && cloned == set
}

qc!(retain_set, _retain_set);
fn _retain_set((set, root): (PrefixSet<TestPrefix>, TestPrefix)) -> bool {
    let mut set = set;
    let want = set
        .iter()
        .filter(|p| !(root.contains(p) && p.1 >= root.1 + 2))
        .collect::<Vec<_>>();
    set.retain(|p| !(root.contains(p) && p.1 >= root.1 + 2));
    set.0.check_memory_alloc() && set.into_iter().eq(want)
}

qc!(remove_children, _remove_children);
fn _remove_children((mut map, root): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
    let want = select(&map, |p, _| !root.contains(p));
    map.remove_children(&root);
    map.check_memory_alloc() && map.len() == want.len() && map.into_iter().eq(want)
}

qc!(remove_children_vec, _remove_children_vec);
fn _remove_children_vec((map, root): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
    let mut map = map
        .into_iter()
        .map(|(p, t)| (p, vec![t]))
        .collect::<PrefixMap<_, _>>();
    let want = select(&map, |p, _| !root.contains(p));
    map.remove_children(&root);
    map.check_memory_alloc() && map.len() == want.len() && map.into_iter().eq(want)
}

qc!(retain, _retain);
fn _retain((mut map, root): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
    let want = select(&map, |p, _| !(root.contains(p) && p.1 >= root.1 + 2));
    map.retain(|p, _| !(root.contains(p) && p.1 >= root.1 + 2));
    map.check_memory_alloc() && map.into_iter().eq(want)
}

qc!(cover, _cover);
fn _cover((map, query): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
    let want = expected_cover(&map, &query);
    let got = map
        .cover(&query)
        .map(|(prefix, value)| (prefix, *value))
        .collect::<Vec<_>>();
    got == want
}

qc!(cover_keys, _cover_keys);
fn _cover_keys((map, query): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
    let want = expected_cover(&map, &query)
        .into_iter()
        .map(|(prefix, _)| prefix)
        .collect::<Vec<_>>();
    let got = map.cover_keys(&query).collect::<Vec<_>>();
    got == want
}

qc!(cover_values, _cover_values);
fn _cover_values((map, query): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
    let want = expected_cover(&map, &query)
        .into_iter()
        .map(|(_, value)| value)
        .collect::<Vec<_>>();
    let got = map.cover_values(&query).copied().collect::<Vec<_>>();
    got == want
}

qc!(cover_set, _cover_set);
fn _cover_set((prefixes, query): (Vec<TestPrefix>, TestPrefix)) -> bool {
    let set = prefixes.into_iter().collect::<PrefixSet<_>>();
    let want = expected_set_cover(&set, &query);
    let got = set.cover(&query).collect::<Vec<_>>();
    got == want
}

qc!(cover_after_keep_tree_mods, _cover_after_keep_tree_mods);
fn _cover_after_keep_tree_mods(
    (ops, query): (Vec<Operation<TestPrefix, i32>>, TestPrefix),
) -> bool {
    let mut pmap = PrefixMap::new();
    let mut hmap = HashMap::new();

    for op in ops {
        match op {
            Operation::Add(p, value) => {
                pmap.insert(p, value);
                hmap.insert(p, value);
            }
            Operation::Remove(p) => {
                pmap.remove_keep_tree(&p);
                hmap.remove(&p);
            }
            Operation::RemoveChildren(p) => {
                pmap.remove_children(&p);
                hmap.retain(|x, _| !p.contains(x));
            }
        }
    }

    let want = expected_cover_from_ref(&hmap, &query);
    let got = pmap
        .cover(&query)
        .map(|(prefix, value)| (prefix, *value))
        .collect::<Vec<_>>();
    pmap.check_memory_alloc() && got == want
}

qc!(equality_joint_map, _equality_joint_map);
fn _equality_joint_map(
    (left_entries, right_entries): (Vec<(TestPrefix, i32)>, Vec<(TestPrefix, i32)>),
) -> bool {
    use crate::joint::JointPrefixMap;
    use either::Either;

    type JP = Either<TestPrefix, TestPrefix>;

    let mut map: JointPrefixMap<JP, i32> = JointPrefixMap::new();
    for (p, v) in &left_entries {
        map.insert(Either::Left(*p), *v);
    }
    for (p, v) in &right_entries {
        map.insert(Either::Right(*p), *v);
    }

    let clone: JointPrefixMap<JP, i32> = map.iter().map(|(p, v)| (p, *v)).collect();
    map == clone && map.len() == clone.len() && map.is_empty() == clone.is_empty()
}

qc!(inequality_joint_map, _inequality_joint_map);
fn _inequality_joint_map(
    (left_entries, right_entries, toggle): (
        Vec<(TestPrefix, i32)>,
        Vec<(TestPrefix, i32)>,
        TestPrefix,
    ),
) -> bool {
    use crate::joint::JointPrefixMap;
    use either::Either;

    type JP = Either<TestPrefix, TestPrefix>;

    let mut map: JointPrefixMap<JP, i32> = JointPrefixMap::new();
    for (p, v) in &left_entries {
        map.insert(Either::Left(*p), *v);
    }
    for (p, v) in &right_entries {
        map.insert(Either::Right(*p), *v);
    }

    let clone: JointPrefixMap<JP, i32> = map.iter().map(|(p, v)| (p, *v)).collect();
    let key = Either::Left(toggle);
    if map.contains_key(&key) {
        map.remove(&key);
    } else {
        map.insert(key, 0);
    }
    map != clone
}

qc!(equality_joint_set, _equality_joint_set);
fn _equality_joint_set((left_entries, right_entries): (Vec<TestPrefix>, Vec<TestPrefix>)) -> bool {
    use crate::joint::JointPrefixSet;
    use either::Either;

    type JP = Either<TestPrefix, TestPrefix>;

    let mut set: JointPrefixSet<JP> = JointPrefixSet::new();
    for p in &left_entries {
        set.insert(Either::Left(*p));
    }
    for p in &right_entries {
        set.insert(Either::Right(*p));
    }

    let clone: JointPrefixSet<JP> = set.iter().collect();
    set == clone && set.len() == clone.len() && set.is_empty() == clone.is_empty()
}

qc!(inequality_joint_set, _inequality_joint_set);
fn _inequality_joint_set(
    (left_entries, right_entries, toggle): (Vec<TestPrefix>, Vec<TestPrefix>, TestPrefix),
) -> bool {
    use crate::joint::JointPrefixSet;
    use either::Either;

    type JP = Either<TestPrefix, TestPrefix>;

    let mut set: JointPrefixSet<JP> = JointPrefixSet::new();
    for p in &left_entries {
        set.insert(Either::Left(*p));
    }
    for p in &right_entries {
        set.insert(Either::Right(*p));
    }

    let clone: JointPrefixSet<JP> = set.iter().collect();
    let key = Either::Right(toggle);
    if set.contains(&key) {
        set.remove(&key);
    } else {
        set.insert(key);
    }
    set != clone
}

qc!(drop_check, _drop_check);
fn _drop_check((pmap, root): (PrefixMap<TestPrefix, ()>, TestPrefix)) -> bool {
    struct DropCounter(std::rc::Rc<std::cell::Cell<usize>>, Vec<i32>);

    impl Drop for DropCounter {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    let count = std::rc::Rc::new(std::cell::Cell::new(0));
    let exp = pmap.len();

    {
        let mut map: PrefixMap<TestPrefix, DropCounter> = PrefixMap::new();

        for p in pmap.keys() {
            map.insert(p, DropCounter(count.clone(), vec![0]));
        }

        let mut into_iter = map.into_iter();
        for (p, v) in into_iter.by_ref() {
            if root.contains(&p) {
                break;
            }
            let _ = v.1;
        }

        let _ = into_iter;
    }

    count.get() == exp
}

qc!(
    dense_set_iter_from_inclusive,
    _dense_set_iter_from_inclusive
);
fn _dense_set_iter_from_inclusive(input: (Vec<TestPrefix>, TestPrefix)) -> bool {
    let (list, query) = input;
    let set: PrefixSet<TestPrefix> = list.into_iter().collect();
    let got: Vec<_> = set.iter_from(&query, true).collect();
    let want: Vec<_> = set.iter().skip_while(|p| *p < query).collect();
    got == want
}

qc!(
    dense_set_iter_from_exclusive,
    _dense_set_iter_from_exclusive
);
fn _dense_set_iter_from_exclusive(input: (Vec<TestPrefix>, TestPrefix)) -> bool {
    let (list, query) = input;
    let set: PrefixSet<TestPrefix> = list.into_iter().collect();
    let got: Vec<_> = set.iter_from(&query, false).collect();
    let want: Vec<_> = set.iter().skip_while(|p| *p <= query).collect();
    got == want
}

qc!(dense_iter_from_inclusive, _dense_iter_from_inclusive);
fn _dense_iter_from_inclusive(input: (Vec<(TestPrefix, i32)>, TestPrefix)) -> bool {
    let (list, query) = input;
    let map: PrefixMap<TestPrefix, i32> = list.into_iter().collect();
    let got: Vec<_> = map.iter_from(&query, true).map(|(p, v)| (p, *v)).collect();
    let want: Vec<_> = map
        .iter()
        .skip_while(|(p, _)| *p < query)
        .map(|(p, v)| (p, *v))
        .collect();
    got == want
}

qc!(dense_iter_from_exclusive, _dense_iter_from_exclusive);
fn _dense_iter_from_exclusive(input: (Vec<(TestPrefix, i32)>, TestPrefix)) -> bool {
    let (list, query) = input;
    let map: PrefixMap<TestPrefix, i32> = list.into_iter().collect();
    let got: Vec<_> = map.iter_from(&query, false).map(|(p, v)| (p, *v)).collect();
    let want: Vec<_> = map
        .iter()
        .skip_while(|(p, _)| *p <= query)
        .map(|(p, v)| (p, *v))
        .collect();
    got == want
}
