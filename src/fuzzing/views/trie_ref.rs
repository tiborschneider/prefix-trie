use super::*;

qc!(trie_ref_root_iter, _trie_ref_root_iter);
fn _trie_ref_root_iter(entries: Entries) -> bool {
    let (map, reference) = build_map(entries);
    let want = entries_in_view(&reference, None);
    let got = map
        .view()
        .into_iter()
        .map(|(prefix, value)| (prefix, *value))
        .collect::<Vec<_>>();
    got == want
}

qc!(trie_ref_sub_iter, _trie_ref_sub_iter);
fn _trie_ref_sub_iter((entries, root): (Entries, TestPrefix)) -> bool {
    let (map, reference) = build_map(entries);
    let want = entries_in_view(&reference, Some(root));
    let got = map
        .view_at(&root)
        .map(|view| {
            view.into_iter()
                .map(|(prefix, value)| (prefix, *value))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    got == want
}

qc!(trie_ref_root_lpm, _trie_ref_root_lpm);
fn _trie_ref_root_lpm((entries, query): (Entries, TestPrefix)) -> bool {
    let (map, reference) = build_map(entries);
    let entries = entries_in_view(&reference, None);
    let want = lpm_in_view(&entries, &query);
    let got = map
        .view()
        .find_lpm_value(&query)
        .map(|(prefix, value)| (prefix, *value));
    got == want
}

qc!(trie_ref_sub_lpm, _trie_ref_sub_lpm);
fn _trie_ref_sub_lpm((entries, root, query): (Entries, TestPrefix, TestPrefix)) -> bool {
    let (map, reference) = build_map(entries);
    let entries = entries_in_view(&reference, Some(root));
    let want = lpm_in_view(&entries, &query);
    let got = map
        .view_at(&root)
        .and_then(|view| view.find_lpm_value(&query))
        .map(|(prefix, value)| (prefix, *value));
    got == want
}

qc!(trie_ref_mut_root_iter, _trie_ref_mut_root_iter);
fn _trie_ref_mut_root_iter(entries: Entries) -> bool {
    let (mut map, reference) = build_map(entries);
    let want = entries_in_view(&reference, None);
    let got = (&mut map)
        .view()
        .into_iter()
        .map(|(prefix, value)| (prefix, *value))
        .collect::<Vec<_>>();
    got == want
}

qc!(trie_ref_mut_sub_iter, _trie_ref_mut_sub_iter);
fn _trie_ref_mut_sub_iter((entries, root): (Entries, TestPrefix)) -> bool {
    let (mut map, reference) = build_map(entries);
    let want = entries_in_view(&reference, Some(root));
    let got = (&mut map)
        .view_at(&root)
        .map(|view| {
            view.into_iter()
                .map(|(prefix, value)| (prefix, *value))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    got == want
}

qc!(trie_ref_mut_root_lpm, _trie_ref_mut_root_lpm);
fn _trie_ref_mut_root_lpm((entries, query): (Entries, TestPrefix)) -> bool {
    let (mut map, reference) = build_map(entries);
    let entries = entries_in_view(&reference, None);
    let want = lpm_in_view(&entries, &query);
    let got = (&mut map)
        .view()
        .find_lpm_value(&query)
        .map(|(prefix, value)| (prefix, *value));
    got == want
}

qc!(trie_ref_mut_sub_lpm, _trie_ref_mut_sub_lpm);
fn _trie_ref_mut_sub_lpm((entries, root, query): (Entries, TestPrefix, TestPrefix)) -> bool {
    let (mut map, reference) = build_map(entries);
    let entries = entries_in_view(&reference, Some(root));
    let want = lpm_in_view(&entries, &query);
    let got = (&mut map)
        .view_at(&root)
        .and_then(|view| view.find_lpm_value(&query))
        .map(|(prefix, value)| (prefix, *value));
    got == want
}
