use super::*;

fn check_iter(
    left: Entries,
    right: Entries,
    left_root: Option<TestPrefix>,
    right_root: Option<TestPrefix>,
) -> bool {
    let (left_map, left_reference) = build_map(left);
    let (right_map, right_reference) = build_map(right);
    let empty_left = PrefixMap::new();
    let empty_right = PrefixMap::new();
    let want = expected_intersection(&left_reference, &right_reference, left_root, right_root);
    let got = view_or_empty(&left_map, &empty_left, left_root)
        .intersection(view_or_empty(&right_map, &empty_right, right_root))
        .map(|view| {
            view.into_iter()
                .map(|(prefix, (left, right))| (prefix, (*left, *right)))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    got == want
}

fn check_lpm(
    left: Entries,
    right: Entries,
    left_root: Option<TestPrefix>,
    right_root: Option<TestPrefix>,
    query: TestPrefix,
) -> bool {
    let (left_map, left_reference) = build_map(left);
    let (right_map, right_reference) = build_map(right);
    let empty_left = PrefixMap::new();
    let empty_right = PrefixMap::new();
    let entries = expected_intersection(&left_reference, &right_reference, left_root, right_root);
    let want = lpm_in_view(&entries, &query);
    let got = view_or_empty(&left_map, &empty_left, left_root)
        .intersection(view_or_empty(&right_map, &empty_right, right_root))
        .and_then(|view| view.find_lpm_value(&query))
        .map(|(prefix, (left, right))| (prefix, (*left, *right)));
    got == want
}

fn check_iter_mut(
    left: Entries,
    right: Entries,
    left_root: Option<TestPrefix>,
    right_root: Option<TestPrefix>,
) -> bool {
    let (mut left_map, left_reference) = build_map(left);
    let (mut right_map, right_reference) = build_map(right);
    let mut empty_left = PrefixMap::new();
    let mut empty_right = PrefixMap::new();
    let want = expected_intersection(&left_reference, &right_reference, left_root, right_root);
    let got = view_mut_or_empty(&mut left_map, &mut empty_left, left_root)
        .intersection(view_mut_or_empty(
            &mut right_map,
            &mut empty_right,
            right_root,
        ))
        .map(|view| {
            view.into_iter()
                .map(|(prefix, (left, right))| (prefix, (*left, *right)))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    got == want
}

fn check_lpm_mut(
    left: Entries,
    right: Entries,
    left_root: Option<TestPrefix>,
    right_root: Option<TestPrefix>,
    query: TestPrefix,
) -> bool {
    let (mut left_map, left_reference) = build_map(left);
    let (mut right_map, right_reference) = build_map(right);
    let mut empty_left = PrefixMap::new();
    let mut empty_right = PrefixMap::new();
    let entries = expected_intersection(&left_reference, &right_reference, left_root, right_root);
    let want = lpm_in_view(&entries, &query);
    let got = view_mut_or_empty(&mut left_map, &mut empty_left, left_root)
        .intersection(view_mut_or_empty(
            &mut right_map,
            &mut empty_right,
            right_root,
        ))
        .and_then(|view| view.find_lpm_value(&query))
        .map(|(prefix, (left, right))| (prefix, (*left, *right)));
    got == want
}

macro_rules! root_root {
    ($iter:ident, $iter_fn:ident, $lpm:ident, $lpm_fn:ident, $check_iter:ident, $check_lpm:ident) => {
        qc!($iter, $iter_fn);
        fn $iter_fn((left, right): (Entries, Entries)) -> bool {
            $check_iter(left, right, None, None)
        }

        qc!($lpm, $lpm_fn);
        fn $lpm_fn((left, right, query): (Entries, Entries, TestPrefix)) -> bool {
            $check_lpm(left, right, None, None, query)
        }
    };
}

macro_rules! root_sub {
    ($iter:ident, $iter_fn:ident, $lpm:ident, $lpm_fn:ident, $check_iter:ident, $check_lpm:ident) => {
        qc!($iter, $iter_fn);
        fn $iter_fn((left, right, right_root): (Entries, Entries, TestPrefix)) -> bool {
            $check_iter(left, right, None, Some(right_root))
        }

        qc!($lpm, $lpm_fn);
        fn $lpm_fn(
            (left, right, right_root, query): (Entries, Entries, TestPrefix, TestPrefix),
        ) -> bool {
            $check_lpm(left, right, None, Some(right_root), query)
        }
    };
}

macro_rules! sub_root {
    ($iter:ident, $iter_fn:ident, $lpm:ident, $lpm_fn:ident, $check_iter:ident, $check_lpm:ident) => {
        qc!($iter, $iter_fn);
        fn $iter_fn((left, right, left_root): (Entries, Entries, TestPrefix)) -> bool {
            $check_iter(left, right, Some(left_root), None)
        }

        qc!($lpm, $lpm_fn);
        fn $lpm_fn(
            (left, right, left_root, query): (Entries, Entries, TestPrefix, TestPrefix),
        ) -> bool {
            $check_lpm(left, right, Some(left_root), None, query)
        }
    };
}

macro_rules! sub_sub {
    ($iter:ident, $iter_fn:ident, $lpm:ident, $lpm_fn:ident, $check_iter:ident, $check_lpm:ident) => {
        qc!($iter, $iter_fn);
        fn $iter_fn(
            (left, right, left_root, right_root): (Entries, Entries, TestPrefix, TestPrefix),
        ) -> bool {
            $check_iter(left, right, Some(left_root), Some(right_root))
        }

        qc!($lpm, $lpm_fn);
        fn $lpm_fn(
            (left, right, left_root, right_root, query): (
                Entries,
                Entries,
                TestPrefix,
                TestPrefix,
                TestPrefix,
            ),
        ) -> bool {
            $check_lpm(left, right, Some(left_root), Some(right_root), query)
        }
    };
}

root_root!(
    intersection_root_root_iter,
    _intersection_root_root_iter,
    intersection_root_root_lpm,
    _intersection_root_root_lpm,
    check_iter,
    check_lpm
);
root_sub!(
    intersection_root_sub_iter,
    _intersection_root_sub_iter,
    intersection_root_sub_lpm,
    _intersection_root_sub_lpm,
    check_iter,
    check_lpm
);
sub_root!(
    intersection_sub_root_iter,
    _intersection_sub_root_iter,
    intersection_sub_root_lpm,
    _intersection_sub_root_lpm,
    check_iter,
    check_lpm
);
sub_sub!(
    intersection_sub_sub_iter,
    _intersection_sub_sub_iter,
    intersection_sub_sub_lpm,
    _intersection_sub_sub_lpm,
    check_iter,
    check_lpm
);

root_root!(
    intersection_mut_root_root_iter,
    _intersection_mut_root_root_iter,
    intersection_mut_root_root_lpm,
    _intersection_mut_root_root_lpm,
    check_iter_mut,
    check_lpm_mut
);
root_sub!(
    intersection_mut_root_sub_iter,
    _intersection_mut_root_sub_iter,
    intersection_mut_root_sub_lpm,
    _intersection_mut_root_sub_lpm,
    check_iter_mut,
    check_lpm_mut
);
sub_root!(
    intersection_mut_sub_root_iter,
    _intersection_mut_sub_root_iter,
    intersection_mut_sub_root_lpm,
    _intersection_mut_sub_root_lpm,
    check_iter_mut,
    check_lpm_mut
);
sub_sub!(
    intersection_mut_sub_sub_iter,
    _intersection_mut_sub_sub_iter,
    intersection_mut_sub_sub_lpm,
    _intersection_mut_sub_sub_lpm,
    check_iter_mut,
    check_lpm_mut
);
