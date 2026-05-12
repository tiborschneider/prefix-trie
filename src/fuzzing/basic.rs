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

qc!(remove_children, _remove_children);
fn _remove_children((mut map, root): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
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
