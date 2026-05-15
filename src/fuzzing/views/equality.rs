use super::*;

fn expected_eq_keys(
    left: &ReferenceMap,
    right: &ReferenceMap,
    left_root: Option<TestPrefix>,
    right_root: Option<TestPrefix>,
) -> bool {
    let left_keys: std::collections::HashSet<_> =
        left.keys().filter(|p| in_scope(left_root, p)).collect();
    let right_keys: std::collections::HashSet<_> =
        right.keys().filter(|p| in_scope(right_root, p)).collect();
    left_keys == right_keys
}

fn check_eq_keys(
    left: Entries,
    right: Entries,
    left_root: Option<TestPrefix>,
    right_root: Option<TestPrefix>,
) -> bool {
    let (left_map, left_reference) = build_map(left);
    let (right_map, right_reference) = build_map(right);
    let empty_left = PrefixMap::new();
    let empty_right = PrefixMap::new();
    let want = expected_eq_keys(&left_reference, &right_reference, left_root, right_root);
    let got = view_or_empty(&left_map, &empty_left, left_root).eq_keys(view_or_empty(
        &right_map,
        &empty_right,
        right_root,
    ));
    got == want
}

fn check_eq_by(
    left: Entries,
    right: Entries,
    left_root: Option<TestPrefix>,
    right_root: Option<TestPrefix>,
) -> bool {
    let (left_map, left_reference) = build_map(left);
    let (right_map, right_reference) = build_map(right);
    let empty_left = PrefixMap::new();
    let empty_right = PrefixMap::new();

    // compute expected: same keys AND same values
    let left_entries = entries_in_view(&left_reference, left_root);
    let right_entries = entries_in_view(&right_reference, right_root);
    let want = left_entries == right_entries;

    let got = view_or_empty(&left_map, &empty_left, left_root).eq_by(
        view_or_empty(&right_map, &empty_right, right_root),
        |a, b| a == b,
    );
    got == want
}

// eq_keys against a difference view: (a \ b).eq_keys(c) should match the
// reference difference key set against c's key set.
fn check_eq_keys_difference(
    a: Entries,
    b: Entries,
    c: Entries,
    a_root: Option<TestPrefix>,
    b_root: Option<TestPrefix>,
    c_root: Option<TestPrefix>,
) -> bool {
    let (a_map, a_ref) = build_map(a);
    let (b_map, b_ref) = build_map(b);
    let (c_map, c_ref) = build_map(c);
    let empty_a = PrefixMap::new();
    let empty_b = PrefixMap::new();
    let empty_c = PrefixMap::new();

    let diff_keys: std::collections::HashSet<_> =
        expected_difference(&a_ref, &b_ref, a_root, b_root)
            .into_iter()
            .map(|(p, _)| p)
            .collect();
    let c_keys: std::collections::HashSet<_> =
        c_ref.keys().filter(|p| in_scope(c_root, p)).collect();
    let want = diff_keys == c_keys.into_iter().copied().collect();

    let got = view_or_empty(&a_map, &empty_a, a_root)
        .difference(view_or_empty(&b_map, &empty_b, b_root))
        .eq_keys(view_or_empty(&c_map, &empty_c, c_root));
    got == want
}

macro_rules! root_root {
    ($name:ident, $fn:ident, $check:ident) => {
        qc!($name, $fn);
        fn $fn((left, right): (Entries, Entries)) -> bool {
            $check(left, right, None, None)
        }
    };
}

macro_rules! root_sub {
    ($name:ident, $fn:ident, $check:ident) => {
        qc!($name, $fn);
        fn $fn((left, right, right_root): (Entries, Entries, TestPrefix)) -> bool {
            $check(left, right, None, Some(right_root))
        }
    };
}

macro_rules! sub_root {
    ($name:ident, $fn:ident, $check:ident) => {
        qc!($name, $fn);
        fn $fn((left, right, left_root): (Entries, Entries, TestPrefix)) -> bool {
            $check(left, right, Some(left_root), None)
        }
    };
}

macro_rules! sub_sub {
    ($name:ident, $fn:ident, $check:ident) => {
        qc!($name, $fn);
        fn $fn(
            (left, right, left_root, right_root): (Entries, Entries, TestPrefix, TestPrefix),
        ) -> bool {
            $check(left, right, Some(left_root), Some(right_root))
        }
    };
}

root_root!(eq_keys_root_root, _eq_keys_root_root, check_eq_keys);
root_sub!(eq_keys_root_sub, _eq_keys_root_sub, check_eq_keys);
sub_root!(eq_keys_sub_root, _eq_keys_sub_root, check_eq_keys);
sub_sub!(eq_keys_sub_sub, _eq_keys_sub_sub, check_eq_keys);

root_root!(eq_by_root_root, _eq_by_root_root, check_eq_by);
root_sub!(eq_by_root_sub, _eq_by_root_sub, check_eq_by);
sub_root!(eq_by_sub_root, _eq_by_sub_root, check_eq_by);
sub_sub!(eq_by_sub_sub, _eq_by_sub_sub, check_eq_by);

qc!(eq_keys_difference_root, _eq_keys_difference_root);
fn _eq_keys_difference_root((a, b, c): (Entries, Entries, Entries)) -> bool {
    check_eq_keys_difference(a, b, c, None, None, None)
}

qc!(eq_keys_difference_sub, _eq_keys_difference_sub);
fn _eq_keys_difference_sub(
    (a, b, c, a_root, b_root, c_root): (
        Entries,
        Entries,
        Entries,
        TestPrefix,
        TestPrefix,
        TestPrefix,
    ),
) -> bool {
    check_eq_keys_difference(a, b, c, Some(a_root), Some(b_root), Some(c_root))
}
