use std::ops::RangeInclusive;

use super::*;

/// The sibling prefix of `prefix`, obtained by flipping the lowest bit of its network address.
/// Only meaningful for a non-default prefix (a `/0` has no sibling).
fn sibling(prefix: &TestPrefix) -> Option<TestPrefix> {
    if prefix.prefix_len() == 0 {
        return None;
    }
    let differing_bit = 1u32 << (32 - prefix.prefix_len() as u32);
    Some(TestPrefix::from_repr_len(
        prefix.repr() ^ differing_bit,
        prefix.prefix_len(),
    ))
}

/// The inclusive address range covered by `prefix`. The end fits in `u32` (the largest value is
/// `2^32 - 1`); only the block-size shift needs a transient `u64` to avoid overflowing on a `/0`.
fn range(prefix: &TestPrefix) -> RangeInclusive<u32> {
    let start = prefix.repr();
    let end = start + ((1u64 << (32 - prefix.prefix_len() as u32)) - 1) as u32;
    start..=end
}

/// How strongly an aggregated set is expected to be reduced; selects which structural invariants
/// [`covered_space`] enforces while it walks the (sorted) members.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Reduced {
    /// No structural guarantee — used for the original, pre-aggregation set.
    No,
    /// Irredundant: no member is covered by another (the guarantee of `aggregate_consistent`).
    /// Mergeable sibling pairs are still allowed.
    Irredundant,
    /// Minimal: irredundant *and* no two mergeable siblings remain (the guarantee of `aggregate`).
    Minimal,
}

/// The covered address space of `set` as merged disjoint inclusive intervals, computed in a single
/// pass over the (already sorted) members.
///
/// `reduced` selects the structural invariant to enforce: [`Reduced::Irredundant`] requires that
/// consecutive members never overlap (an overlap means one member contains another, so a redundant
/// prefix was left in); [`Reduced::Minimal`] additionally forbids mergeable siblings (the pair
/// should have collapsed into their parent). Returns `None` if the requested invariant is violated.
fn covered_space(
    set: &PrefixSet<TestPrefix>,
    reduced: Reduced,
) -> Option<Vec<RangeInclusive<u32>>> {
    let mut merged: Vec<RangeInclusive<u32>> = Vec::new();
    let mut previous: Option<TestPrefix> = None;
    for prefix in set {
        let cur = range(&prefix);
        if let Some(previous) = previous {
            let prev = range(&previous);
            let overlaps = cur.start() <= prev.end(); // one member contains another
            let mergeable = sibling(&previous) == Some(prefix); // pair should have merged
            let violated = match reduced {
                Reduced::No => false,
                Reduced::Irredundant => overlaps,
                Reduced::Minimal => overlaps || mergeable,
            };
            if violated {
                return None;
            }
        }
        previous = Some(prefix);
        match merged.last_mut() {
            // merge overlapping or touching ranges; saturating_add avoids overflow at the top.
            Some(last) if *cur.start() <= last.end().saturating_add(1) => {
                let end = *cur.end().max(last.end());
                *last = *last.start()..=end;
            }
            _ => merged.push(cur),
        }
    }
    Some(merged)
}

qc!(aggregate_set, _aggregate_set);
fn _aggregate_set(prefixes: Vec<TestPrefix>) -> bool {
    let original = prefixes.iter().copied().collect::<PrefixSet<_>>();
    let mut aggregated = original.clone();
    aggregated.aggregate();
    let mut double_agg = aggregated.clone();
    double_agg.aggregate();

    let original_space = covered_space(&original, Reduced::No).unwrap();
    let Some(aggregated_space) = covered_space(&aggregated, Reduced::Minimal) else {
        return false; // test failed.
    };

    // The covered address space must be preserved exactly, and the cached `len()` must stay in sync
    // with the actual element count (it is maintained manually via the aggregation's count delta).
    original_space == aggregated_space
        && original.address_count() == aggregated.address_count()
        && aggregated.len() == aggregated.iter().count()
        && aggregated.0.check_memory_alloc()
        && aggregated == double_agg
}

/// The longest-prefix-match result of `map` for every address, as merged disjoint address
/// intervals (the map analog of [`covered_space`]).
///
/// Each entry's address range is inserted least-specific first, so a more-specific entry overwrites
/// its sub-range (`rangemap` replaces overlaps with the newer value). The result maps every covered
/// address to its `get_lpm` value; uncovered addresses are absent. Two maps yield identical
/// `get_lpm` for every address iff their `lpm_map`s are equal.
///
/// `reduced` selects the structural invariant to enforce (entries may legitimately nest when a
/// more-specific entry has a *different* value): [`Reduced::Irredundant`] requires that no entry
/// has the same value as its nearest covering ancestor (the guarantee of `aggregate_consistent`);
/// [`Reduced::Minimal`] additionally forbids two equal-value sibling prefixes (the merging
/// `aggregate` would have collapsed them). Returns `None` if the requested invariant is violated.
fn lpm_map(
    map: &PrefixMap<TestPrefix, u8>,
    reduced: Reduced,
) -> Option<rangemap::RangeInclusiveMap<u32, u8>> {
    let entries: Vec<(TestPrefix, u8)> = map.iter().map(|(p, v)| (p, *v)).collect();

    if reduced != Reduced::No {
        for &(p, v) in &entries {
            // Redundant: `p`'s nearest strictly-less-specific covering entry has the same value.
            let redundant = entries
                .iter()
                .filter(|(q, _)| q.prefix_len() < p.prefix_len() && q.contains(&p))
                .max_by_key(|(q, _)| q.prefix_len())
                .is_some_and(|&(_, ancestor_value)| ancestor_value == v);
            // Mergeable: `p`'s sibling is also present with the same value.
            let mergeable = sibling(&p).is_some_and(|sib| map.get(&sib) == Some(&v));
            let violated = match reduced {
                Reduced::No => false,
                Reduced::Irredundant => redundant,
                Reduced::Minimal => redundant || mergeable,
            };
            if violated {
                return None;
            }
        }
    }

    let mut sorted = entries;
    sorted.sort_by_key(|(p, _)| p.prefix_len());
    let mut lpm = rangemap::RangeInclusiveMap::new();
    for (p, v) in sorted {
        lpm.insert(range(&p), v);
    }
    Some(lpm)
}

qc!(aggregate_consistent_map, _aggregate_consistent_map);
fn _aggregate_consistent_map(entries: Vec<(TestPrefix, u8)>) -> bool {
    let original: PrefixMap<TestPrefix, u8> = entries.into_iter().collect();
    let mut aggregated = original.clone();
    aggregated.aggregate_consistent();
    let mut twice = aggregated.clone();
    twice.aggregate_consistent();

    let original_lpm = lpm_map(&original, Reduced::No).unwrap();
    let Some(aggregated_lpm) = lpm_map(&aggregated, Reduced::Irredundant) else {
        return false; // a redundant entry survived
    };

    // Drop-only never invents prefixes: every survivor is an unchanged entry of the original.
    let is_subset = aggregated.iter().all(|(p, v)| original.get(&p) == Some(v));

    // `get_lpm` is identical for every address, and `aggregate_consistent` is idempotent.
    original_lpm == aggregated_lpm
        && original.address_count() == aggregated.address_count()
        && is_subset
        && aggregated.len() == aggregated.iter().count()
        && aggregated.check_memory_alloc()
        && aggregated == twice
}

qc!(aggregate_consistent_set, _aggregate_consistent_set);
fn _aggregate_consistent_set(prefixes: Vec<TestPrefix>) -> bool {
    let original = prefixes.iter().copied().collect::<PrefixSet<_>>();
    let mut aggregated = original.clone();
    aggregated.aggregate_consistent();
    let mut twice = aggregated.clone();
    twice.aggregate_consistent();

    // Drop-only preserves the covered address space and leaves the set irredundant (no member
    // covered by another), but not necessarily minimal (mergeable siblings may remain).
    let original_space = covered_space(&original, Reduced::No).unwrap();
    let Some(aggregated_space) = covered_space(&aggregated, Reduced::Irredundant) else {
        return false; // an unremoved covered member slipped through
    };

    // Drop-only never invents prefixes: every survivor existed in the original.
    let is_subset = aggregated.iter().all(|p| original.contains(&p));

    // `get_lpm` presence is preserved for every prefix in the original.
    let lpm_presence_preserved = prefixes
        .iter()
        .all(|p| original.get_lpm(p).is_some() == aggregated.get_lpm(p).is_some());

    original_space == aggregated_space
        && original.address_count() == aggregated.address_count()
        && is_subset
        && lpm_presence_preserved
        && aggregated.len() == aggregated.iter().count()
        && aggregated.0.check_memory_alloc()
        && aggregated == twice
}

qc!(aggregate_map, _aggregate_map);
fn _aggregate_map(entries: Vec<(TestPrefix, u8)>) -> bool {
    let original: PrefixMap<TestPrefix, u8> = entries.into_iter().collect();
    let mut aggregated = original.clone();
    aggregated.aggregate();
    let mut twice = aggregated.clone();
    twice.aggregate();

    let original_lpm = lpm_map(&original, Reduced::No).unwrap();
    // `Reduced::Minimal` also asserts the result is irredundant and has no equal-value siblings.
    let Some(aggregated_lpm) = lpm_map(&aggregated, Reduced::Minimal) else {
        return false; // a redundant or mergeable entry survived
    };

    // Equal range-maps mean `get_lpm` matches for every address, covered set included: a newly
    // covered hole would appear as an extra range and fail the comparison.
    original_lpm == aggregated_lpm
        && original.address_count() == aggregated.address_count()
        && aggregated.len() == aggregated.iter().count()
        && aggregated.check_memory_alloc()
        && aggregated == twice
}

qc!(aggregate_fill_map, _aggregate_fill_map);
fn _aggregate_fill_map(entries: Vec<(TestPrefix, u8)>) -> bool {
    const DEFAULT: u8 = 0;
    let original: PrefixMap<TestPrefix, u8> = entries.into_iter().collect();
    let mut aggregated = original.clone();
    aggregated.aggregate_fill(|| DEFAULT);
    let mut twice = aggregated.clone();
    twice.aggregate_fill(|| DEFAULT);

    let original_lpm = lpm_map(&original, Reduced::No).unwrap();
    let Some(aggregated_lpm) = lpm_map(&aggregated, Reduced::Minimal) else {
        return false;
    };

    // Expected forwarding: `DEFAULT` across the whole space, with the original forwarding on top
    // (this is `original.get_lpm(a).unwrap_or(DEFAULT)` for every address).
    let mut expected = rangemap::RangeInclusiveMap::new();
    expected.insert(0..=u32::MAX, DEFAULT);
    for (r, v) in original_lpm.iter() {
        expected.insert(r.clone(), *v);
    }

    aggregated_lpm == expected
        && aggregated.len() == aggregated.iter().count()
        && aggregated.check_memory_alloc()
        && aggregated == twice
}
