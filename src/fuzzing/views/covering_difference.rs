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
    let want =
        expected_covering_difference(&left_reference, &right_reference, left_root, right_root);
    let got = view_or_empty(&left_map, &empty_left, left_root)
        .covering_difference(view_or_empty(&right_map, &empty_right, right_root))
        .into_iter()
        .map(|(prefix, value)| (prefix, *value))
        .collect::<Vec<_>>();
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
    let entries =
        expected_covering_difference(&left_reference, &right_reference, left_root, right_root);
    let want = lpm_in_view(&entries, &query);
    let got = view_or_empty(&left_map, &empty_left, left_root)
        .covering_difference(view_or_empty(&right_map, &empty_right, right_root))
        .find_lpm_value(&query)
        .map(|(prefix, value)| (prefix, *value));
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
    let want =
        expected_covering_difference(&left_reference, &right_reference, left_root, right_root);
    let got = view_mut_or_empty(&mut left_map, &mut empty_left, left_root)
        .covering_difference(view_mut_or_empty(
            &mut right_map,
            &mut empty_right,
            right_root,
        ))
        .into_iter()
        .map(|(prefix, value)| (prefix, *value))
        .collect::<Vec<_>>();
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
    let entries =
        expected_covering_difference(&left_reference, &right_reference, left_root, right_root);
    let want = lpm_in_view(&entries, &query);
    let got = view_mut_or_empty(&mut left_map, &mut empty_left, left_root)
        .covering_difference(view_mut_or_empty(
            &mut right_map,
            &mut empty_right,
            right_root,
        ))
        .find_lpm_value(&query)
        .map(|(prefix, value)| (prefix, *value));
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
    covering_difference_root_root_iter,
    _covering_difference_root_root_iter,
    covering_difference_root_root_lpm,
    _covering_difference_root_root_lpm,
    check_iter,
    check_lpm
);
root_sub!(
    covering_difference_root_sub_iter,
    _covering_difference_root_sub_iter,
    covering_difference_root_sub_lpm,
    _covering_difference_root_sub_lpm,
    check_iter,
    check_lpm
);
sub_root!(
    covering_difference_sub_root_iter,
    _covering_difference_sub_root_iter,
    covering_difference_sub_root_lpm,
    _covering_difference_sub_root_lpm,
    check_iter,
    check_lpm
);
sub_sub!(
    covering_difference_sub_sub_iter,
    _covering_difference_sub_sub_iter,
    covering_difference_sub_sub_lpm,
    _covering_difference_sub_sub_lpm,
    check_iter,
    check_lpm
);

root_root!(
    covering_difference_mut_root_root_iter,
    _covering_difference_mut_root_root_iter,
    covering_difference_mut_root_root_lpm,
    _covering_difference_mut_root_root_lpm,
    check_iter_mut,
    check_lpm_mut
);
root_sub!(
    covering_difference_mut_root_sub_iter,
    _covering_difference_mut_root_sub_iter,
    covering_difference_mut_root_sub_lpm,
    _covering_difference_mut_root_sub_lpm,
    check_iter_mut,
    check_lpm_mut
);
sub_root!(
    covering_difference_mut_sub_root_iter,
    _covering_difference_mut_sub_root_iter,
    covering_difference_mut_sub_root_lpm,
    _covering_difference_mut_sub_root_lpm,
    check_iter_mut,
    check_lpm_mut
);
sub_sub!(
    covering_difference_mut_sub_sub_iter,
    _covering_difference_mut_sub_sub_iter,
    covering_difference_mut_sub_sub_lpm,
    _covering_difference_mut_sub_sub_lpm,
    check_iter_mut,
    check_lpm_mut
);
