use std::collections::HashMap;

use super::*;
use itertools::Itertools;
use trieview::UnionItem;

qc!(union, _union);
fn _union((a, b): (PrefixMap<TestPrefix, i32>, PrefixMap<TestPrefix, i32>)) -> bool {
    let mut union_set: HashMap<TestPrefix, (Option<i32>, Option<i32>)> = HashMap::new();
    for (p, a) in a.iter() {
        let _ = union_set.entry(*p).or_default().0.insert(*a);
    }
    for (p, b) in b.iter() {
        let _ = union_set.entry(*p).or_default().1.insert(*b);
    }

    let want = union_set.into_iter().sorted().collect::<Vec<_>>();
    let got = a
        .view()
        .union(&b)
        .map(|x| match x {
            UnionItem::Left { prefix, left, .. } => (*prefix, (Some(*left), None)),
            UnionItem::Right { prefix, right, .. } => (*prefix, (None, Some(*right))),
            UnionItem::Both {
                prefix,
                left,
                right,
            } => (*prefix, (Some(*left), Some(*right))),
        })
        .collect::<Vec<_>>();

    want == got
}

qc!(union_mut, _union_mut);
fn _union_mut((mut a, mut b): (PrefixMap<TestPrefix, i32>, PrefixMap<TestPrefix, i32>)) -> bool {
    let mut union_set: HashMap<TestPrefix, (Option<i32>, Option<i32>)> = HashMap::new();
    for (p, a) in a.iter() {
        let _ = union_set.entry(*p).or_default().0.insert(*a);
    }
    for (p, b) in b.iter() {
        let _ = union_set.entry(*p).or_default().1.insert(*b);
    }

    let want = union_set.into_iter().sorted().collect::<Vec<_>>();
    let got = a
        .view_mut()
        .union_mut(&mut b)
        .map(|(p, a, b)| (*p, (a.copied(), b.copied())))
        .collect::<Vec<_>>();

    want == got
}

qc!(union_lpm, _union_lpm);
fn _union_lpm((a, b): (PrefixMap<TestPrefix, i32>, PrefixMap<TestPrefix, i32>)) -> bool {
    let mut union_set: HashMap<TestPrefix, (Option<(TestPrefix, i32)>, Option<(TestPrefix, i32)>)> =
        HashMap::new();
    for (p, a) in a.iter() {
        union_set
            .entry(*p)
            .or_insert_with(|| (Some((*p, *a)), b.get_lpm(p).copied()));
    }
    for (p, b) in b.iter() {
        union_set
            .entry(*p)
            .or_insert_with(|| (a.get_lpm(p).copied(), Some((*p, *b))));
    }

    let want = union_set.into_iter().sorted().collect::<Vec<_>>();
    let got = a
        .view()
        .union(&b)
        .map(|x| (*x.prefix(), (x.left().copied(), x.right().copied())))
        .collect::<Vec<_>>();

    want == got
}

qc!(intersection, _intersection);
fn _intersection((a, b): (PrefixMap<TestPrefix, i32>, PrefixMap<TestPrefix, i32>)) -> bool {
    let mut intersection_set: HashMap<TestPrefix, (i32, i32)> = HashMap::new();
    for (p, a) in a.iter() {
        if let Some(b) = b.get(p) {
            intersection_set.insert(*p, (*a, *b));
        }
    }

    let want = intersection_set.into_iter().sorted().collect::<Vec<_>>();
    let got = a
        .view()
        .intersection(&b)
        .map(|(p, a, b)| (*p, (*a, *b)))
        .collect::<Vec<_>>();

    want == got
}

qc!(intersection_mut, _intersection_mut);
fn _intersection_mut(
    (mut a, mut b): (PrefixMap<TestPrefix, i32>, PrefixMap<TestPrefix, i32>),
) -> bool {
    let mut intersection_set: HashMap<TestPrefix, (i32, i32)> = HashMap::new();
    for (p, a) in a.iter() {
        if let Some(b) = b.get(p) {
            intersection_set.insert(*p, (*a, *b));
        }
    }

    let want = intersection_set.into_iter().sorted().collect::<Vec<_>>();
    let got = a
        .view_mut()
        .intersection_mut(&mut b)
        .map(|(p, a, b)| (*p, (*a, *b)))
        .collect::<Vec<_>>();

    want == got
}

qc!(difference, _difference);
fn _difference((a, b): (PrefixMap<TestPrefix, i32>, PrefixMap<TestPrefix, i32>)) -> bool {
    let mut difference_set: HashMap<TestPrefix, (i32, Option<(TestPrefix, i32)>)> = HashMap::new();
    for (p, a) in a.iter() {
        let b = b.get_lpm(p).copied();
        if b.map(|(lpm, _)| &lpm == p).unwrap_or(false) {
            // same prefix! ignore
        } else {
            difference_set.insert(*p, (*a, b));
        }
    }

    let want = difference_set.into_iter().sorted().collect::<Vec<_>>();
    let got = a
        .view()
        .difference(&b)
        .map(|i| (*i.prefix, (*i.value, i.right.copied())))
        .collect::<Vec<_>>();

    want == got
}

qc!(difference_mut, _difference_mut);
fn _difference_mut((mut a, b): (PrefixMap<TestPrefix, i32>, PrefixMap<TestPrefix, i32>)) -> bool {
    let mut difference_set: HashMap<TestPrefix, (i32, Option<(TestPrefix, i32)>)> = HashMap::new();
    for (p, a) in a.iter() {
        let b = b.get_lpm(p).copied();
        if b.map(|(lpm, _)| &lpm == p).unwrap_or(false) {
            // same prefix! ignore
        } else {
            difference_set.insert(*p, (*a, b));
        }
    }

    let want = difference_set.into_iter().sorted().collect::<Vec<_>>();
    let got = a
        .view_mut()
        .difference_mut(&b)
        .map(|i| (*i.prefix, (*i.value, i.right.copied())))
        .collect::<Vec<_>>();

    want == got
}

qc!(covering_difference, _covering_difference);
fn _covering_difference((a, b): (PrefixMap<TestPrefix, i32>, PrefixMap<TestPrefix, i32>)) -> bool {
    let mut difference_set: HashMap<TestPrefix, i32> = HashMap::new();
    for (p, a) in a.iter() {
        if b.get_lpm(p).is_none() {
            difference_set.insert(*p, *a);
        }
    }

    let want = difference_set.into_iter().sorted().collect::<Vec<_>>();
    let got = a
        .view()
        .covering_difference(&b)
        .map(|(p, t)| (*p, *t))
        .collect::<Vec<_>>();

    want == got
}

qc!(covering_difference_mut, _covering_difference_mut);
fn _covering_difference_mut(
    (mut a, b): (PrefixMap<TestPrefix, i32>, PrefixMap<TestPrefix, i32>),
) -> bool {
    let mut difference_set: HashMap<TestPrefix, i32> = HashMap::new();
    for (p, a) in a.iter() {
        if b.get_lpm(p).is_none() {
            difference_set.insert(*p, *a);
        }
    }

    let want = difference_set.into_iter().sorted().collect::<Vec<_>>();
    let got = a
        .view_mut()
        .covering_difference_mut(&b)
        .map(|(p, t)| (*p, *t))
        .collect::<Vec<_>>();

    want == got
}

trait MyCopy {
    type Out;

    fn copied(&self) -> Self::Out;
}

impl<P: Copy, T: Copy> MyCopy for Option<(&P, &T)> {
    type Out = Option<(P, T)>;

    fn copied(&self) -> Self::Out {
        self.map(|(p, t)| (*p, *t))
    }
}
