use super::*;

qc!(children, _children);
fn _children((map, start): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
    let want = select_ref(&map, |p, _| start.contains(p));
    map.children(&start).eq(want)
}

qc!(children_trieview, _children_trieview);
fn _children_trieview((map, start): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
    let want = select_ref(&map, |p, _| start.contains(p));
    if let Some(view) = map.view_at(start) {
        view.iter().eq(want)
    } else {
        want.is_empty()
    }
}

qc!(children_trieview_mut, _children_trieview_mut);
fn _children_trieview_mut((mut map, start): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
    let want = select(&map, |p, _| start.contains(p));
    if let Some(view) = map.view_mut_at(start) {
        view.iter().eq(want.iter().map(|(p, t)| (p, t)))
    } else {
        want.is_empty()
    }
}

qc!(children_keys_trieview, _children_keys_trieview);
fn _children_keys_trieview((map, start): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
    let want = select_keys(&map, |p, _| start.contains(p));
    if let Some(view) = map.view_at(start) {
        view.keys().eq(want)
    } else {
        want.is_empty()
    }
}

qc!(children_keys_trieview_mut, _children_keys_trieview_mut);
fn _children_keys_trieview_mut((mut map, start): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
    let want: Vec<_> = select_keys(&map, |p, _| start.contains(p))
        .into_iter()
        .cloned()
        .collect();
    if let Some(view) = map.view_mut_at(start) {
        view.keys().eq(&want)
    } else {
        want.is_empty()
    }
}

qc!(children_values_trieview, _children_values_trieview);
fn _children_values_trieview((map, start): (PrefixMap<TestPrefix, i32>, TestPrefix)) -> bool {
    let want = select_values(&map, |p, _| start.contains(p));
    if let Some(view) = map.view_at(start) {
        view.values().eq(want)
    } else {
        want.is_empty()
    }
}

qc!(children_values_trieview_mut, _children_values_trieview_mut);
fn _children_values_trieview_mut(
    (mut map, start): (PrefixMap<TestPrefix, i32>, TestPrefix),
) -> bool {
    let want: Vec<_> = select_values(&map, |p, _| start.contains(p))
        .into_iter()
        .cloned()
        .collect();
    if let Some(view) = map.view_mut_at(start) {
        view.values().eq(&want)
    } else {
        want.is_empty()
    }
}
