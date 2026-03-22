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
        }
    }

    pmap.check_memory_alloc() && pmap.into_iter().eq(hmap.into_iter().sorted())
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
    map.retain(|p, _| !(root.contains(&p) && p.1 >= root.1 + 2));
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
    let mut map = PrefixMap::new();
    let mut reference = HashMap::new();

    for op in ops {
        match op {
            Operation::Add(prefix, value) => {
                map.insert(prefix, value);
                reference.insert(prefix, value);
            }
            Operation::Remove(prefix) => {
                map.remove_keep_tree(&prefix);
                reference.remove(&prefix);
            }
        }
    }

    let want = expected_cover_from_ref(&reference, &query);
    let got = map
        .cover(&query)
        .map(|(prefix, value)| (prefix, *value))
        .collect::<Vec<_>>();
    map.check_memory_alloc() && got == want
}

// ============ PrefixMap Integration Tests ============

qc!(dense_new, _dense_new);
fn _dense_new(list: Vec<(TestPrefix, i32)>) -> bool {
    let mut pmap = PrefixMap::new();
    let mut hmap = HashMap::new();

    for (p, t) in list.clone() {
        pmap.insert(p, t);
        hmap.insert(p, t);
    }

    if !pmap.check_memory_alloc() {
        return false;
    }

    // assert that the iterator of both is the same
    let pmap_data = pmap.into_iter().collect_vec();
    let hmap_data = hmap.into_iter().sorted().collect_vec();
    pmap_data == hmap_data
}

qc!(dense_new_mods, _dense_new_mods);
fn _dense_new_mods(list: Vec<Operation<TestPrefix, i32>>) -> bool {
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
        }
    }

    if !pmap.check_memory_alloc() {
        return false;
    }

    // assert that the iterator of both is the same
    pmap.into_iter().eq(hmap.into_iter().sorted())
}

qc!(dense_mods_clone, _dense_mods_clone);
fn _dense_mods_clone(list: Vec<Operation<TestPrefix, i32>>) -> bool {
    let mut pmap = PrefixMap::new();

    for op in list {
        match op {
            Operation::Add(p, t) => {
                pmap.insert(p, t);
            }
            Operation::Remove(p) => {
                pmap.remove(&p);
            }
        }
    }

    if !pmap.check_memory_alloc() {
        return false;
    }

    let cloned = pmap.clone();

    if !cloned.check_memory_alloc() {
        eprintln!("Cloned datastructure contains memory corruption");
        return false;
    }

    cloned == pmap
}

qc!(dense_new_mods_entry, _dense_new_mods_entry);
fn _dense_new_mods_entry(list: Vec<Operation<TestPrefix, i32>>) -> bool {
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
        }
    }

    if !pmap.check_memory_alloc() {
        return false;
    }

    // assert that the iterator of both is the same
    pmap.into_iter().eq(hmap.into_iter().sorted())
}

qc!(dense_remove_children, _dense_remove_children);
fn _dense_remove_children((mut pmap, root): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
    let want = select(&pmap, |p, _| !root.contains(p));
    pmap.remove_children(&root);
    if !pmap.check_memory_alloc() {
        return false;
    }
    pmap.len() == want.len() && pmap.into_iter().eq(want)
}

qc!(dense_retain, _dense_retain);
fn _dense_retain((mut pmap, root): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
    let want = select(&pmap, |p, _| !(root.contains(p) && p.1 >= root.1 + 2));
    pmap.retain(|p, _| !(root.contains(&p) && p.1 >= root.1 + 2));
    if !pmap.check_memory_alloc() {
        return false;
    }
    pmap.into_iter().eq(want)
}
