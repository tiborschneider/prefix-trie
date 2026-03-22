//! Intersection set-operation view.
//!
//! [`IntersectionView`] yields every prefix present in **both** the left and right views.
//! Both `data_bitmap()` and `child_bitmap()` are the AND of the two sides' bitmaps, so
//! only prefixes/children present in both views are visited.
//!
//! `IntersectionView::new` returns `None` for structurally disjoint sub-tries, so every
//! live `IntersectionView` has aligned, overlapping views.

use std::marker::PhantomData;

use crate::{prefix::mask_from_prefix_len, AsView, Prefix};

use super::{TrieView, ViewIter};

/// An immutable view over the intersection of two [`TrieView`]s.
///
/// Returned as `Option<IntersectionView<'_, L, R>>` by [`TrieView::intersection`].
/// `None` means the two sub-tries are disjoint (no common prefixes possible).
///
/// A live `IntersectionView` can be iterated directly (implements [`IntoIterator`])
/// or composed with further set operations before iterating.
#[derive(Clone)]
pub struct IntersectionView<'a, L, R> {
    left: L,
    right: R,
    _phantom: PhantomData<&'a ()>,
}

impl<'a, L, R> IntersectionView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    /// Construct an `IntersectionView`, aligning the two views to the same depth.
    ///
    /// Returns `None` when:
    /// - The key prefixes diverge at the shallower prefix_len (disjoint sub-tries), or
    /// - The deeper side has no matching sub-trie at the shallower side's key.
    pub(crate) fn new(left: L, right: R) -> Option<Self> {
        let (left, right) = align(left, right)?;
        Some(Self {
            left,
            right,
            _phantom: PhantomData,
        })
    }
}

/// Align two views to the same depth by navigating the shallower one toward the deeper one.
///
/// Returns `None` if the key prefixes diverge (disjoint sub-tries).
fn align<'a, L, R>(left: L, right: R) -> Option<(L, R)>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    // Check key agreement at the shallower prefix_len.
    let min_prefix_len = left.prefix_len().min(right.prefix_len());
    let mask = mask_from_prefix_len(min_prefix_len as u8);
    if left.key() & mask != right.key() & mask {
        return None; // diverging keys -> disjoint sub-tries
    }

    // Navigate the shallower side toward the deeper one.
    if left.depth() < right.depth() {
        let left = left.navigate_to(right.key(), right.prefix_len())?;
        Some((left, right))
    } else if right.depth() < left.depth() {
        let right = right.navigate_to(left.key(), left.prefix_len())?;
        Some((left, right))
    } else if left.prefix_len() < right.prefix_len() {
        let left = left.navigate_to(right.key(), right.prefix_len())?;
        Some((left, right))
    } else if right.prefix_len() < left.prefix_len() {
        let right = right.navigate_to(left.key(), left.prefix_len())?;
        Some((left, right))
    } else {
        Some((left, right))
    }
}

impl<'a, L, R> TrieView<'a> for IntersectionView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    type P = L::P;
    type T = (L::T, R::T);

    #[inline]
    fn depth(&self) -> u32 {
        self.left.depth()
    }

    #[inline]
    fn key(&self) -> <L::P as Prefix>::R {
        self.left.key()
    }

    #[inline]
    fn prefix_len(&self) -> u32 {
        self.left.prefix_len()
    }

    /// Only bits present in **both** data bitmaps.
    #[inline]
    fn data_bitmap(&self) -> u32 {
        self.left.data_bitmap() & self.right.data_bitmap()
    }

    /// Only children present in **both** child bitmaps.
    #[inline]
    fn child_bitmap(&self) -> u32 {
        self.left.child_bitmap() & self.right.child_bitmap()
    }

    #[inline]
    unsafe fn get_data(&mut self, data_bit: u32) -> (L::T, R::T) {
        // SAFETY: caller guarantees data_bit is set in data_bitmap() and called at most once.
        unsafe { (self.left.get_data(data_bit), self.right.get_data(data_bit)) }
    }

    #[inline]
    unsafe fn get_child(&mut self, child_bit: u32) -> Self {
        // SAFETY: caller guarantees child_bit is set in child_bitmap() and called at most once.
        unsafe {
            Self {
                left: self.left.get_child(child_bit),
                right: self.right.get_child(child_bit),
                _phantom: PhantomData,
            }
        }
    }

    #[inline]
    unsafe fn reposition(&mut self, key: <L::P as Prefix>::R, prefix_len: u32) {
        // SAFETY: caller ensures non-overlapping use with existing cursors.
        unsafe {
            self.left.reposition(key, prefix_len);
            self.right.reposition(key, prefix_len);
        }
    }
}

impl<'a, L, R> IntoIterator for IntersectionView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    type Item = (L::P, (L::T, R::T));
    type IntoIter = ViewIter<'a, IntersectionView<'a, L, R>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, L, R> AsView<'a> for IntersectionView<'a, L, R>
where
    L: TrieView<'a>,
    R: TrieView<'a, P = L::P>,
{
    type P = L::P;
    type View = Self;

    fn view(self) -> Self {
        self
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        Prefix,
        {
            trieview::{AsView, TrieView},
            PrefixMap,
        },
    };

    type P = (u32, u8);

    fn p(repr: u32, len: u8) -> P {
        P::from_repr_len(repr, len)
    }

    fn map_from(entries: &[(u32, u8, i32)]) -> PrefixMap<P, i32> {
        let mut m = PrefixMap::new();
        for &(repr, len, val) in entries {
            m.insert(p(repr, len), val);
        }
        m
    }

    #[test]
    fn intersection_basic() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0b000000, 8, 9)]);
        let b = map_from(&[
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 20),
            (0x0c000000, 8, 99),
        ]);
        let got: Vec<_> = a
            .view()
            .intersection(b.view())
            .unwrap()
            .into_iter()
            .map(|(p, (l, r))| (p, (*l, *r)))
            .collect();
        assert_eq!(
            got,
            vec![(p(0x0a000000, 8), (1, 10)), (p(0x0a010000, 16), (2, 20))]
        );
    }

    #[test]
    fn intersection_no_common_entries() {
        // 10.0.0.0/8 and 11.0.0.0/8 share no prefixes. Both root views cover the entire
        // trie, so the intersection is Some; is_non_empty() may be true (shared child
        // subtrees exist at the bitmap level), but iterating yields nothing.
        let a = map_from(&[(0x0a000000, 8, 1)]);
        let b = map_from(&[(0x0b000000, 8, 2)]);
        let isect = a.view().intersection(b.view()).unwrap();
        assert!(isect.into_iter().next().is_none());
    }

    #[test]
    fn intersection_disjoint_subviews_is_none() {
        // Viewing at sub-prefixes that are structurally disjoint -> None.
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0b000000, 8, 10), (0x0b010000, 16, 20)]);
        let va = a.view_at(&p(0x0a000000, 8)).unwrap();
        let vb = b.view_at(&p(0x0b000000, 8)).unwrap();
        assert!(va.intersection(vb).is_none());
    }

    #[test]
    fn intersection_into_iter_for_loop() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let b = map_from(&[(0x0a000000, 8, 10), (0x0a010000, 16, 20)]);
        let mut count = 0;
        if let Some(isect) = a.view().intersection(b.view()) {
            for (_prefix, (_l, _r)) in isect {
                count += 1;
            }
        }
        assert_eq!(count, 2);
    }

    #[test]
    fn intersection_composed() {
        // (a ∩ b) ∩ c -> tests that IntersectionView itself implements TrieView
        // and can be fed into another intersection.
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0b000000, 8, 3)]);
        let b = map_from(&[
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 20),
            (0x0c000000, 8, 30),
        ]);
        let c = map_from(&[(0x0a000000, 8, 100), (0x0b000000, 8, 200)]);

        // a ∩ b gives {10.0.0.0/8, 10.1.0.0/16}; ∩ c keeps only {10.0.0.0/8}
        let ab = a.view().intersection(b.view()).unwrap();
        let got: Vec<_> = ab
            .intersection(c.view())
            .unwrap()
            .into_iter()
            .map(|(p, ((l, _m), r))| (p, (*l, *r)))
            .collect();
        assert_eq!(got, vec![(p(0x0a000000, 8), (1, 100))]);
    }

    #[test]
    fn intersection_find_then_iter() {
        // Build maps with many entries across two sub-tries; intersect then find a sub-prefix.
        let a = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a010100, 24, 3),
            (0x0a020000, 16, 4),
            (0x0b000000, 8, 5),
        ]);
        let b = map_from(&[
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 20),
            (0x0a010100, 24, 30),
            (0x0a030000, 16, 40),
            (0x0c000000, 8, 50),
        ]);

        // Intersect: common = {10.0.0.0/8, 10.1.0.0/16, 10.1.1.0/24}
        let isect = a.view().intersection(b.view()).unwrap();

        // find(10.1.0.0/16) on the intersection -> should yield 10.1.0.0/16 and 10.1.1.0/24
        let sub: Vec<_> = isect
            .find(&p(0x0a010000, 16))
            .unwrap()
            .into_iter()
            .map(|(p, (l, r))| (p, (*l, *r)))
            .collect();
        assert_eq!(
            sub,
            vec![(p(0x0a010000, 16), (2, 20)), (p(0x0a010100, 24), (3, 30))]
        );
    }

    #[test]
    fn intersection_find_exact_and_value() {
        let a = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 3)]);
        let b = map_from(&[
            (0x0a000000, 8, 10),
            (0x0a010000, 16, 20),
            (0x0a020000, 16, 40), // not in a
        ]);

        let isect = a.view().intersection(b.view()).unwrap();

        // find_exact on a prefix present in both
        let v = isect.clone().find_exact(&p(0x0a010000, 16)).unwrap();
        let (l, r) = v.value().unwrap();
        assert_eq!((*l, *r), (2, 20));

        // find_exact on a prefix present only in a (not in b) -> None
        assert!(isect.find_exact(&p(0x0a010100, 24)).is_none());
    }

    #[test]
    fn intersection_mut_find_lpm_value_does_not_require_clone() {
        let mut a = map_from(&[(0x0a000000, 8, 1), (0x0a010100, 24, 3)]);
        let b = map_from(&[(0x0a000000, 8, 10), (0x0a010100, 24, 30)]);

        let got = (&mut a)
            .view()
            .intersection(b.view())
            .unwrap()
            .find_lpm_value(&p(0x0a010180, 25))
            .map(|(prefix, (left, right))| {
                *left += *right;
                (prefix, *left, *right)
            });

        assert_eq!(got, Some((p(0x0a010100, 24), 33, 30)));
        assert_eq!(a.get(&p(0x0a010100, 24)), Some(&33));
    }
}
