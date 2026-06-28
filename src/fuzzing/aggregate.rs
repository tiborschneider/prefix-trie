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

/// The covered address space of `set` as merged disjoint inclusive intervals, computed in a single
/// pass over the (already sorted) members.
///
/// When `assert_minimal` is set, the set is also checked to be an irreducible cover: consecutive
/// members must never overlap (an overlap means one member contains another, so a redundant prefix
/// was left in) and must never be mergeable siblings (the pair should have collapsed into their
/// parent). Returns `None` if that check fails.
fn covered_space(
    set: &PrefixSet<TestPrefix>,
    assert_minimal: bool,
) -> Option<Vec<RangeInclusive<u32>>> {
    let mut merged: Vec<RangeInclusive<u32>> = Vec::new();
    let mut previous: Option<TestPrefix> = None;
    for prefix in set {
        let cur = range(&prefix);
        if assert_minimal {
            if let Some(previous) = previous {
                let prev = range(&previous);
                let overlaps = cur.start() <= prev.end();
                let mergeable = sibling(&previous) == Some(prefix);
                if overlaps || mergeable {
                    return None;
                }
            }
            previous = Some(prefix);
        }
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

    let original_space = covered_space(&original, false).unwrap();
    let Some(aggregated_space) = covered_space(&aggregated, true) else {
        return false; // test failed.
    };

    // The covered address space must be preserved exactly, and `len()` must stay in sync.
    original_space == aggregated_space
        && aggregated.len() == aggregated.iter().count()
        && aggregated == double_agg
}
