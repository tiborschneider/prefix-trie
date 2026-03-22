use super::*;

fn expected_union_difference(
    left: &ReferenceMap,
    middle: &ReferenceMap,
    right: &ReferenceMap,
    root: Option<TestPrefix>,
) -> Vec<(TestPrefix, (Option<i32>, Option<i32>))> {
    sorted(
        expected_union(left, middle, root, root)
            .into_iter()
            .filter(|(prefix, _)| !right.contains_key(prefix) || !in_scope(root, prefix))
            .collect(),
    )
}

fn expected_difference_intersection(
    left: &ReferenceMap,
    middle: &ReferenceMap,
    right: &ReferenceMap,
    root: Option<TestPrefix>,
) -> Vec<(TestPrefix, (i32, i32))> {
    sorted(
        left.iter()
            .filter(|(prefix, _)| in_scope(root, prefix))
            .filter(|(prefix, _)| !middle.contains_key(prefix) || !in_scope(root, prefix))
            .filter_map(|(prefix, left_value)| {
                right.get(prefix).and_then(|right_value| {
                    in_scope(root, prefix).then_some((*prefix, (*left_value, *right_value)))
                })
            })
            .collect(),
    )
}

fn check_union_difference_iter(
    left: Entries,
    middle: Entries,
    right: Entries,
    root: Option<TestPrefix>,
) -> bool {
    let (left_map, left_reference) = build_map(left);
    let (middle_map, middle_reference) = build_map(middle);
    let (right_map, right_reference) = build_map(right);
    let empty_left = PrefixMap::new();
    let empty_middle = PrefixMap::new();
    let empty_right = PrefixMap::new();

    let want =
        expected_union_difference(&left_reference, &middle_reference, &right_reference, root);
    let got = view_or_empty(&left_map, &empty_left, root)
        .union(view_or_empty(&middle_map, &empty_middle, root))
        .difference(view_or_empty(&right_map, &empty_right, root))
        .into_iter()
        .map(|(prefix, item)| (prefix, norm_union(item)))
        .collect::<Vec<_>>();
    got == want
}

fn check_union_difference_lpm(
    left: Entries,
    middle: Entries,
    right: Entries,
    root: Option<TestPrefix>,
    query: TestPrefix,
) -> bool {
    let (left_map, left_reference) = build_map(left);
    let (middle_map, middle_reference) = build_map(middle);
    let (right_map, right_reference) = build_map(right);
    let empty_left = PrefixMap::new();
    let empty_middle = PrefixMap::new();
    let empty_right = PrefixMap::new();

    let entries =
        expected_union_difference(&left_reference, &middle_reference, &right_reference, root);
    let want = lpm_in_view(&entries, &query);
    let got = view_or_empty(&left_map, &empty_left, root)
        .union(view_or_empty(&middle_map, &empty_middle, root))
        .difference(view_or_empty(&right_map, &empty_right, root))
        .find_lpm_value(&query)
        .map(|(prefix, item)| (prefix, norm_union(item)));
    got == want
}

fn check_union_difference_iter_mut(
    left: Entries,
    middle: Entries,
    right: Entries,
    root: Option<TestPrefix>,
) -> bool {
    let (mut left_map, left_reference) = build_map(left);
    let (mut middle_map, middle_reference) = build_map(middle);
    let (mut right_map, right_reference) = build_map(right);
    let mut empty_left = PrefixMap::new();
    let mut empty_middle = PrefixMap::new();
    let mut empty_right = PrefixMap::new();

    let want =
        expected_union_difference(&left_reference, &middle_reference, &right_reference, root);
    let got = view_mut_or_empty(&mut left_map, &mut empty_left, root)
        .union(view_mut_or_empty(&mut middle_map, &mut empty_middle, root))
        .difference(view_mut_or_empty(&mut right_map, &mut empty_right, root))
        .into_iter()
        .map(|(prefix, item)| (prefix, norm_union(item)))
        .collect::<Vec<_>>();
    got == want
}

fn check_union_difference_lpm_mut(
    left: Entries,
    middle: Entries,
    right: Entries,
    root: Option<TestPrefix>,
    query: TestPrefix,
) -> bool {
    let (mut left_map, left_reference) = build_map(left);
    let (mut middle_map, middle_reference) = build_map(middle);
    let (mut right_map, right_reference) = build_map(right);
    let mut empty_left = PrefixMap::new();
    let mut empty_middle = PrefixMap::new();
    let mut empty_right = PrefixMap::new();

    let entries =
        expected_union_difference(&left_reference, &middle_reference, &right_reference, root);
    let want = lpm_in_view(&entries, &query);
    let got = view_mut_or_empty(&mut left_map, &mut empty_left, root)
        .union(view_mut_or_empty(&mut middle_map, &mut empty_middle, root))
        .difference(view_mut_or_empty(&mut right_map, &mut empty_right, root))
        .find_lpm_value(&query)
        .map(|(prefix, item)| (prefix, norm_union(item)));
    got == want
}

fn check_difference_intersection_iter(
    left: Entries,
    middle: Entries,
    right: Entries,
    root: Option<TestPrefix>,
) -> bool {
    let (left_map, left_reference) = build_map(left);
    let (middle_map, middle_reference) = build_map(middle);
    let (right_map, right_reference) = build_map(right);
    let empty_left = PrefixMap::new();
    let empty_middle = PrefixMap::new();
    let empty_right = PrefixMap::new();

    let want = expected_difference_intersection(
        &left_reference,
        &middle_reference,
        &right_reference,
        root,
    );
    let got = view_or_empty(&left_map, &empty_left, root)
        .difference(view_or_empty(&middle_map, &empty_middle, root))
        .intersection(view_or_empty(&right_map, &empty_right, root))
        .map(|view| {
            view.into_iter()
                .map(|(prefix, (left, right))| (prefix, (*left, *right)))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    got == want
}

fn check_difference_intersection_lpm(
    left: Entries,
    middle: Entries,
    right: Entries,
    root: Option<TestPrefix>,
    query: TestPrefix,
) -> bool {
    let (left_map, left_reference) = build_map(left);
    let (middle_map, middle_reference) = build_map(middle);
    let (right_map, right_reference) = build_map(right);
    let empty_left = PrefixMap::new();
    let empty_middle = PrefixMap::new();
    let empty_right = PrefixMap::new();

    let entries = expected_difference_intersection(
        &left_reference,
        &middle_reference,
        &right_reference,
        root,
    );
    let want = lpm_in_view(&entries, &query);
    let got = view_or_empty(&left_map, &empty_left, root)
        .difference(view_or_empty(&middle_map, &empty_middle, root))
        .intersection(view_or_empty(&right_map, &empty_right, root))
        .and_then(|view| view.find_lpm_value(&query))
        .map(|(prefix, (left, right))| (prefix, (*left, *right)));
    got == want
}

fn check_difference_intersection_iter_mut(
    left: Entries,
    middle: Entries,
    right: Entries,
    root: Option<TestPrefix>,
) -> bool {
    let (mut left_map, left_reference) = build_map(left);
    let (mut middle_map, middle_reference) = build_map(middle);
    let (mut right_map, right_reference) = build_map(right);
    let mut empty_left = PrefixMap::new();
    let mut empty_middle = PrefixMap::new();
    let mut empty_right = PrefixMap::new();

    let want = expected_difference_intersection(
        &left_reference,
        &middle_reference,
        &right_reference,
        root,
    );
    let got = view_mut_or_empty(&mut left_map, &mut empty_left, root)
        .difference(view_mut_or_empty(&mut middle_map, &mut empty_middle, root))
        .intersection(view_mut_or_empty(&mut right_map, &mut empty_right, root))
        .map(|view| {
            view.into_iter()
                .map(|(prefix, (left, right))| (prefix, (*left, *right)))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    got == want
}

fn check_difference_intersection_lpm_mut(
    left: Entries,
    middle: Entries,
    right: Entries,
    root: Option<TestPrefix>,
    query: TestPrefix,
) -> bool {
    let (mut left_map, left_reference) = build_map(left);
    let (mut middle_map, middle_reference) = build_map(middle);
    let (mut right_map, right_reference) = build_map(right);
    let mut empty_left = PrefixMap::new();
    let mut empty_middle = PrefixMap::new();
    let mut empty_right = PrefixMap::new();

    let entries = expected_difference_intersection(
        &left_reference,
        &middle_reference,
        &right_reference,
        root,
    );
    let want = lpm_in_view(&entries, &query);
    let got = view_mut_or_empty(&mut left_map, &mut empty_left, root)
        .difference(view_mut_or_empty(&mut middle_map, &mut empty_middle, root))
        .intersection(view_mut_or_empty(&mut right_map, &mut empty_right, root))
        .and_then(|view| view.find_lpm_value(&query))
        .map(|(prefix, (left, right))| (prefix, (*left, *right)));
    got == want
}

macro_rules! root_case {
    ($iter:ident, $iter_fn:ident, $lpm:ident, $lpm_fn:ident, $check_iter:ident, $check_lpm:ident) => {
        qc!($iter, $iter_fn);
        fn $iter_fn((left, middle, right): (Entries, Entries, Entries)) -> bool {
            $check_iter(left, middle, right, None)
        }

        qc!($lpm, $lpm_fn);
        fn $lpm_fn((left, middle, right, query): (Entries, Entries, Entries, TestPrefix)) -> bool {
            $check_lpm(left, middle, right, None, query)
        }
    };
}

macro_rules! sub_case {
    ($iter:ident, $iter_fn:ident, $lpm:ident, $lpm_fn:ident, $check_iter:ident, $check_lpm:ident) => {
        qc!($iter, $iter_fn);
        fn $iter_fn(
            (left, middle, right, sub_root): (Entries, Entries, Entries, TestPrefix),
        ) -> bool {
            $check_iter(left, middle, right, Some(sub_root))
        }

        qc!($lpm, $lpm_fn);
        fn $lpm_fn(
            (left, middle, right, sub_root, query): (
                Entries,
                Entries,
                Entries,
                TestPrefix,
                TestPrefix,
            ),
        ) -> bool {
            $check_lpm(left, middle, right, Some(sub_root), query)
        }
    };
}

root_case!(
    combination_union_difference_root_iter,
    _combination_union_difference_root_iter,
    combination_union_difference_root_lpm,
    _combination_union_difference_root_lpm,
    check_union_difference_iter,
    check_union_difference_lpm
);
sub_case!(
    combination_union_difference_sub_iter,
    _combination_union_difference_sub_iter,
    combination_union_difference_sub_lpm,
    _combination_union_difference_sub_lpm,
    check_union_difference_iter,
    check_union_difference_lpm
);
root_case!(
    combination_union_difference_mut_root_iter,
    _combination_union_difference_mut_root_iter,
    combination_union_difference_mut_root_lpm,
    _combination_union_difference_mut_root_lpm,
    check_union_difference_iter_mut,
    check_union_difference_lpm_mut
);
sub_case!(
    combination_union_difference_mut_sub_iter,
    _combination_union_difference_mut_sub_iter,
    combination_union_difference_mut_sub_lpm,
    _combination_union_difference_mut_sub_lpm,
    check_union_difference_iter_mut,
    check_union_difference_lpm_mut
);

root_case!(
    combination_difference_intersection_root_iter,
    _combination_difference_intersection_root_iter,
    combination_difference_intersection_root_lpm,
    _combination_difference_intersection_root_lpm,
    check_difference_intersection_iter,
    check_difference_intersection_lpm
);
sub_case!(
    combination_difference_intersection_sub_iter,
    _combination_difference_intersection_sub_iter,
    combination_difference_intersection_sub_lpm,
    _combination_difference_intersection_sub_lpm,
    check_difference_intersection_iter,
    check_difference_intersection_lpm
);
root_case!(
    combination_difference_intersection_mut_root_iter,
    _combination_difference_intersection_mut_root_iter,
    combination_difference_intersection_mut_root_lpm,
    _combination_difference_intersection_mut_root_lpm,
    check_difference_intersection_iter_mut,
    check_difference_intersection_lpm_mut
);
sub_case!(
    combination_difference_intersection_mut_sub_iter,
    _combination_difference_intersection_mut_sub_iter,
    combination_difference_intersection_mut_sub_lpm,
    _combination_difference_intersection_mut_sub_lpm,
    check_difference_intersection_iter_mut,
    check_difference_intersection_lpm_mut
);
