use std::collections::HashMap;

use crate::trieview::{CoveringUnionItem, UnionItem};

use super::*;

mod combinations;
mod covering_difference;
mod covering_union;
mod difference;
mod intersection;
mod trie_ref;
mod union;

type Entries = Vec<(TestPrefix, i32)>;
type ReferenceMap = HashMap<TestPrefix, i32>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum CoveringUnionValue {
    Left(i32, Option<(TestPrefix, i32)>),
    Right(Option<(TestPrefix, i32)>, i32),
    Both(i32, i32),
}

trait CopyValue {
    fn copy_value(self) -> i32;
}

impl CopyValue for &i32 {
    fn copy_value(self) -> i32 {
        *self
    }
}

impl CopyValue for &mut i32 {
    fn copy_value(self) -> i32 {
        *self
    }
}

fn build_map(entries: Entries) -> (PrefixMap<TestPrefix, i32>, ReferenceMap) {
    let mut map = PrefixMap::new();
    let mut reference = HashMap::new();
    for (prefix, value) in entries {
        map.insert(prefix, value);
        reference.insert(prefix, value);
    }
    (map, reference)
}

fn sorted<T: Ord>(mut values: Vec<T>) -> Vec<T> {
    values.sort();
    values
}

fn in_scope(root: Option<TestPrefix>, prefix: &TestPrefix) -> bool {
    root.map_or(true, |root| root.contains(prefix))
}

fn entries_in_view(reference: &ReferenceMap, root: Option<TestPrefix>) -> Vec<(TestPrefix, i32)> {
    sorted(
        reference
            .iter()
            .filter(|(prefix, _)| in_scope(root, prefix))
            .map(|(prefix, value)| (*prefix, *value))
            .collect(),
    )
}

fn lpm_in_view<T: Clone>(
    entries: &[(TestPrefix, T)],
    query: &TestPrefix,
) -> Option<(TestPrefix, T)> {
    entries
        .iter()
        .filter(|(prefix, _)| prefix.contains(query))
        .max_by_key(|(prefix, _)| prefix.prefix_len())
        .cloned()
}

fn view_or_empty<'a>(
    map: &'a PrefixMap<TestPrefix, i32>,
    empty: &'a PrefixMap<TestPrefix, i32>,
    root: Option<TestPrefix>,
) -> TrieRef<'a, TestPrefix, i32> {
    match root {
        Some(root) => match map.view_at(&root) {
            Some(view) => view,
            None => empty.view(),
        },
        None => map.view(),
    }
}

fn view_mut_or_empty<'a>(
    map: &'a mut PrefixMap<TestPrefix, i32>,
    empty: &'a mut PrefixMap<TestPrefix, i32>,
    root: Option<TestPrefix>,
) -> TrieRefMut<'a, TestPrefix, i32> {
    match root {
        Some(root) => match (&mut *map).view_at(&root) {
            Some(view) => view,
            None => empty.view(),
        },
        None => map.view(),
    }
}

fn expected_union(
    left: &ReferenceMap,
    right: &ReferenceMap,
    left_root: Option<TestPrefix>,
    right_root: Option<TestPrefix>,
) -> Vec<(TestPrefix, (Option<i32>, Option<i32>))> {
    let mut out: HashMap<TestPrefix, (Option<i32>, Option<i32>)> = HashMap::new();
    for (prefix, value) in left
        .iter()
        .filter(|(prefix, _)| in_scope(left_root, prefix))
    {
        out.entry(*prefix).or_default().0 = Some(*value);
    }
    for (prefix, value) in right
        .iter()
        .filter(|(prefix, _)| in_scope(right_root, prefix))
    {
        out.entry(*prefix).or_default().1 = Some(*value);
    }
    sorted(out.into_iter().collect())
}

fn expected_intersection(
    left: &ReferenceMap,
    right: &ReferenceMap,
    left_root: Option<TestPrefix>,
    right_root: Option<TestPrefix>,
) -> Vec<(TestPrefix, (i32, i32))> {
    sorted(
        left.iter()
            .filter(|(prefix, _)| in_scope(left_root, prefix))
            .filter_map(|(prefix, left_value)| {
                right.get(prefix).and_then(|right_value| {
                    in_scope(right_root, prefix).then_some((*prefix, (*left_value, *right_value)))
                })
            })
            .collect(),
    )
}

fn expected_difference(
    left: &ReferenceMap,
    right: &ReferenceMap,
    left_root: Option<TestPrefix>,
    right_root: Option<TestPrefix>,
) -> Vec<(TestPrefix, i32)> {
    sorted(
        left.iter()
            .filter(|(prefix, _)| in_scope(left_root, prefix))
            .filter(|(prefix, _)| !in_scope(right_root, prefix) || !right.contains_key(prefix))
            .map(|(prefix, value)| (*prefix, *value))
            .collect(),
    )
}

fn expected_covering_difference(
    left: &ReferenceMap,
    right: &ReferenceMap,
    left_root: Option<TestPrefix>,
    right_root: Option<TestPrefix>,
) -> Vec<(TestPrefix, i32)> {
    sorted(
        left.iter()
            .filter(|(prefix, _)| in_scope(left_root, prefix))
            .filter(|(prefix, _)| {
                !right
                    .keys()
                    .filter(|right_prefix| in_scope(right_root, right_prefix))
                    .any(|right_prefix| right_prefix.contains(prefix))
            })
            .map(|(prefix, value)| (*prefix, *value))
            .collect(),
    )
}

fn expected_covering_union(
    left: &ReferenceMap,
    right: &ReferenceMap,
    left_root: Option<TestPrefix>,
    right_root: Option<TestPrefix>,
) -> Vec<(TestPrefix, CoveringUnionValue)> {
    let left_entries = entries_in_view(left, left_root);
    let right_entries = entries_in_view(right, right_root);
    expected_union(left, right, left_root, right_root)
        .into_iter()
        .map(|(prefix, (left, right))| {
            let value = match (left, right) {
                (Some(left), Some(right)) => CoveringUnionValue::Both(left, right),
                (Some(left), None) => {
                    CoveringUnionValue::Left(left, lpm_in_view(&right_entries, &prefix))
                }
                (None, Some(right)) => {
                    CoveringUnionValue::Right(lpm_in_view(&left_entries, &prefix), right)
                }
                (None, None) => unreachable!("union entry without values"),
            };
            (prefix, value)
        })
        .collect()
}

fn norm_union<L: CopyValue, R: CopyValue>(item: UnionItem<L, R>) -> (Option<i32>, Option<i32>) {
    match item {
        UnionItem::Left(left) => (Some(left.copy_value()), None),
        UnionItem::Right(right) => (None, Some(right.copy_value())),
        UnionItem::Both(left, right) => (Some(left.copy_value()), Some(right.copy_value())),
    }
}

fn norm_covering_union<L: CopyValue, R: CopyValue>(
    item: CoveringUnionItem<TestPrefix, L, R>,
) -> CoveringUnionValue {
    match item {
        CoveringUnionItem::Left { left, right_lpm } => CoveringUnionValue::Left(
            left.copy_value(),
            right_lpm.map(|(prefix, value)| (prefix, value.copy_value())),
        ),
        CoveringUnionItem::Right { left_lpm, right } => CoveringUnionValue::Right(
            left_lpm.map(|(prefix, value)| (prefix, value.copy_value())),
            right.copy_value(),
        ),
        CoveringUnionItem::Both { left, right } => {
            CoveringUnionValue::Both(left.copy_value(), right.copy_value())
        }
    }
}
