//! Filter view
//!
//! [`FilterView`] restricts a view's data entries to those for which a predicate holds.
//!
//! Because [`TrieView::get_data`] may only be called once per `data_bit`, the predicate
//! cannot be evaluated lazily on first access: doing so would consume the value before we
//! know whether to keep it. Instead, `new` / `get_child` / `reposition` eagerly evaluate the
//! predicate against every data slot of the current node and cache the values that pass in a
//! fixed-size array sized to a node's maximum data-slot count (`NUM_DATA`), avoiding a heap
//! allocation per node.

use std::mem::MaybeUninit;

use crate::{table::NUM_DATA, AsView, Prefix, TrieView};

use super::{reconstruct_prefix, ViewIter};

/// Restricts a view's data entries to those for which the predicate holds.
///
/// Returned by [`TrieView::filter`].
pub struct FilterView<'a, V: TrieView<'a>, F> {
    view: V,
    f: F,
    /// Data bits currently exposed via [`data_bitmap`][TrieView::data_bitmap] for this cursor
    /// position. Shrinks when `reposition` narrows the cursor to a smaller sub-range of the
    /// node. Does **not** shrink when `get_data` is called. Always a subset of `owned`.
    mask: u32,
    /// Data bits whose `cache` slot currently holds an initialized value (it passed the
    /// predicate and has not yet been taken via `get_data`). Only shrinks when `get_data` takes
    /// a value; used by `Drop` to know which slots still need dropping. Unaffected by
    /// `reposition`, since a value hidden by narrowing still needs to be dropped eventually.
    owned: u32,
    cache: [MaybeUninit<V::T>; NUM_DATA],
}

// Cloning duplicates every value still alive in `cache` (tracked by `owned`, not just the
// currently-exposed `mask`) so the clone's own `Drop` sees a fully consistent cache.
//
// Safety argument for why this can never alias a mutable view's `&mut T`:
// - `V::T: Clone` is required. `&'a mut T` does not implement `Clone` (only `&'a T` does;
//   Rust withholds it from mutable references specifically to prevent this kind of aliasing),
//   so this impl does not exist at all when `V::T = &'a mut T`.
// - `V: Clone` is also required, and mutable cursors (`TrieRefMut`, and any composed view
//   wrapping one) intentionally do not implement `Clone`, for the same reason.
// Both bounds would have to hold simultaneously for `.clone()` to be callable, and neither can
// hold for a mutable view, so `Clone` is only ever reachable when `T` is a shared reference (or
// an owned `Clone` type) and duplicating it is unproblematic.
impl<'a, V, F> Clone for FilterView<'a, V, F>
where
    V: TrieView<'a> + Clone,
    V::T: Clone,
    F: Clone,
{
    fn clone(&self) -> Self {
        let mut cache: [MaybeUninit<V::T>; NUM_DATA] =
            std::array::from_fn(|_| MaybeUninit::uninit());

        // Clone every bit that is alive (`owned`), not just the currently-exposed `mask`: a
        // value hidden by a prior `reposition` is still `owned` and must be duplicated too, or
        // the clone's `owned` would claim a slot is initialized when it isn't.
        let mut bits = self.owned;
        while bits != 0 {
            let b = bits.trailing_zeros() as usize;
            bits &= bits - 1;
            cache[b] = MaybeUninit::new(
                // SAFETY: `b` is set in `self.owned`, so `self.cache[b]` is initialized.
                unsafe { self.cache[b].assume_init_ref().clone() },
            );
        }

        Self {
            view: self.view.clone(),
            f: self.f.clone(),
            mask: self.mask,
            owned: self.owned,
            cache,
        }
    }
}

impl<'a, V: TrieView<'a>, F> Drop for FilterView<'a, V, F> {
    fn drop(&mut self) {
        let mut bits = self.owned;
        while bits != 0 {
            let b = bits.trailing_zeros() as usize;
            bits &= bits - 1;
            // SAFETY: `b` is set in `self.owned`, so `self.cache[b]` is initialized and has not
            // been dropped or taken (via `get_data`) yet.
            unsafe { self.cache[b].assume_init_drop() };
        }
    }
}

impl<'a, V, F> FilterView<'a, V, F>
where
    V: TrieView<'a>,
    F: Fn(V::P, &V::T) -> bool,
{
    pub(super) fn new(mut view: V, f: F) -> Self {
        let (mask, cache) = Self::build_cache(&mut view, &f);
        Self {
            view,
            f,
            mask,
            owned: mask,
            cache,
        }
    }

    /// Evaluate `f` against every data slot in `view`'s current node, returning the passing
    /// bitmap and a cache of the corresponding values (indexed by `data_bit`).
    ///
    /// Invariant: the cache is initialized on every bit set in the returned mask.
    fn build_cache(view: &mut V, f: &F) -> (u32, [MaybeUninit<V::T>; NUM_DATA]) {
        let mut cache: [MaybeUninit<V::T>; NUM_DATA] =
            std::array::from_fn(|_| MaybeUninit::uninit());
        let mut mask = 0u32;
        let mut bits = view.data_bitmap();
        while bits != 0 {
            let b = bits.trailing_zeros();
            bits &= bits - 1;
            let prefix = reconstruct_prefix::<V::P>(view.depth(), view.key(), b);
            // SAFETY: `b` is set in `view.data_bitmap()` and is fetched exactly once here.
            let value = unsafe { view.get_data(b) };
            if f(prefix, &value) {
                cache[b as usize] = MaybeUninit::new(value);
                mask |= 1 << b;
            }
        }
        (mask, cache)
    }
}

impl<'a, V, F> TrieView<'a> for FilterView<'a, V, F>
where
    V: TrieView<'a>,
    F: Fn(V::P, &V::T) -> bool + Clone,
{
    type P = V::P;
    type T = V::T;

    #[inline]
    fn depth(&self) -> u32 {
        self.view.depth()
    }

    #[inline]
    fn key(&self) -> <Self::P as Prefix>::R {
        self.view.key()
    }

    #[inline]
    fn prefix_len(&self) -> u32 {
        self.view.prefix_len()
    }

    #[inline]
    fn data_bitmap(&self) -> u32 {
        self.mask
    }

    #[inline]
    fn child_bitmap(&self) -> u32 {
        self.view.child_bitmap()
    }

    unsafe fn get_data(&mut self, data_bit: u32) -> Self::T {
        debug_assert_ne!(self.mask & (1 << data_bit), 0, "data_bit not set in mask");
        // Taking the value out of the cache also removes it from `owned`, so `Drop` won't try
        // to drop it again.
        self.owned &= !(1 << data_bit);
        // SAFETY: `assume_init()` requires `self.cache[data_bit]` to be initialized.
        // - By this method's own contract, the caller only ever passes a `data_bit` that is
        //   set in `self.data_bitmap()`, i.e. in `self.mask`, and `mask` is always a subset of
        //   `owned`, so `data_bit` was set in `owned` (before the line above cleared it) and
        //   `self.cache[data_bit]` is initialized.
        // - The caller's contract also guarantees `data_bit` is passed at most once per view
        //   instance, so this is the only read of that slot (the `mem::replace` additionally
        //   leaves an uninitialized placeholder behind, so a second call would not observe
        //   stale initialized data even if the contract were violated).
        std::mem::replace(&mut self.cache[data_bit as usize], MaybeUninit::uninit()).assume_init()
    }

    unsafe fn get_child(&mut self, child_bit: u32) -> Self {
        // SAFETY: forwarded from this method's own contract.
        let mut view = unsafe { self.view.get_child(child_bit) };
        let (mask, cache) = Self::build_cache(&mut view, &self.f);
        Self {
            view,
            f: self.f.clone(),
            mask,
            owned: mask,
            cache,
        }
    }

    unsafe fn reposition(&mut self, key: <Self::P as Prefix>::R, prefix_len: u32) {
        // SAFETY: forwarded from this method's own contract.
        unsafe { self.view.reposition(key, prefix_len) };
        // `reposition` only narrows the cursor (it never reveals data bits outside what
        // `new`/`get_child` already fetched), so we must not call `build_cache` again here: it
        // would call `self.view.get_data` a second time for already-cached bits, violating the
        // "at most once" contract. Instead, trust `self.view`'s own (freshly repositioned)
        // bitmap for what's currently in scope -- `self.view` may be an arbitrary composed view
        // with its own narrowing semantics, so we must not reimplement that logic here.
        let new_scope = self.view.data_bitmap();
        // Bits that were alive but fall outside the new scope are gone from this cursor for
        // good: `reposition` only narrows monotonically (never widens back), so there's no
        // later point at which they'd become reachable again. Drop them now instead of
        // leaving them in `owned` to linger until the whole view is dropped.
        let mut abandoned = self.owned & !new_scope;
        while abandoned != 0 {
            let b = abandoned.trailing_zeros() as usize;
            abandoned &= abandoned - 1;
            // SAFETY: `b` is set in `self.owned`, so `self.cache[b]` is initialized and has not
            // been dropped or taken yet.
            unsafe { self.cache[b].assume_init_drop() };
        }
        self.owned &= new_scope;
        self.mask = self.owned;
    }
}

impl<'a, V, F> AsView<'a> for FilterView<'a, V, F>
where
    V: TrieView<'a>,
    F: Fn(V::P, &V::T) -> bool + Clone,
{
    type P = V::P;
    type View = Self;

    fn view(self) -> Self {
        self
    }
}

impl<'a, V, F> IntoIterator for FilterView<'a, V, F>
where
    V: TrieView<'a>,
    F: Fn(V::P, &V::T) -> bool + Clone,
{
    type Item = (V::P, V::T);
    type IntoIter = ViewIter<'a, Self>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        trieview::{AsView, TrieView},
        Prefix, PrefixMap,
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
    fn filter_view_iter_and_as_view() {
        // /8, /16, and /24 land in different `MultiBitNode`s (K = 5), so this exercises
        // `get_child` rebuilding the cache across node boundaries.
        let m = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a010100, 24, 3),
            (0x0a020000, 16, 4),
        ]);
        let filtered = m.view().filter(|_, x| *x % 2 == 0).copied();
        // AsView::view() on a FilterView returns itself.
        let got: Vec<(P, i32)> = filtered.view().into_iter().collect();
        assert_eq!(got, vec![(p(0x0a010000, 16), 2), (p(0x0a020000, 16), 4)]);
    }

    #[test]
    fn filter_view_uses_prefix() {
        let m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 3)]);
        let filtered = m
            .view()
            .filter(|prefix, _| prefix.prefix_len() == 16)
            .copied();
        let got: Vec<(P, i32)> = filtered.view().into_iter().collect();
        assert_eq!(got, vec![(p(0x0a010000, 16), 2)]);
    }

    #[test]
    fn filter_view_none_match() {
        let m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 3)]);
        let filtered = m.view().filter(|_, _| false).copied();
        let got: Vec<(P, i32)> = filtered.view().into_iter().collect();
        assert_eq!(got, Vec::<(P, i32)>::new());
    }

    #[test]
    fn filter_view_mut_mutates_only_matching() {
        // Mutable view: `&V::T` is `&&mut i32` here, so the predicate derefs twice.
        let mut m = map_from(&[
            (0x0a000000, 8, 1),
            (0x0a010000, 16, 2),
            (0x0a010100, 24, 3),
            (0x0a020000, 16, 4),
        ]);
        for v in (&mut m).view().filter(|_, x| **x % 2 == 0).values() {
            *v += 100;
        }
        assert_eq!(
            m.into_iter().collect::<Vec<_>>(),
            vec![
                (p(0x0a000000, 8), 1),
                (p(0x0a010000, 16), 102),
                (p(0x0a010100, 24), 3),
                (p(0x0a020000, 16), 104),
            ]
        );
    }

    #[test]
    fn filter_view_over_union() {
        // Filter composed on top of a set operation: only keep prefixes present in both.
        let left = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);
        let right = map_from(&[(0x0a010000, 16, 20), (0x0a020000, 16, 30)]);

        let both: Vec<P> = left
            .view()
            .union(&right)
            .filter(|_, item| item.both().is_some())
            .keys()
            .collect();
        assert_eq!(both, vec![p(0x0a010000, 16)]);
    }

    #[test]
    fn filter_view_over_covering_difference() {
        // right's /20 covers left's /24 (10.1.1.0 falls inside 10.1.0.0/20) but not left's /8
        // or /16 (both shorter than /20). `covering_difference` already excludes the /24 entry;
        // `filter`'s closure must never see it.
        let left = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 3)]);
        let right = map_from(&[(0x0a010000, 20, 99)]);

        let got: Vec<P> = left
            .view()
            .copied()
            .covering_difference(&right)
            .filter(|prefix, x| {
                assert_ne!(prefix, p(0x0a010100, 24));
                *x != 1
            })
            .keys()
            .collect();
        assert_eq!(got, vec![p(0x0a010000, 16)]);
    }

    // -----------------------------------------------------------------------------
    // Drop / aliasing tests. `FilterView` manages `MaybeUninit` storage by hand, so these
    // exercise every path that touches `cache`/`mask`/`owned` (filtered-out-immediately,
    // never-taken, taken-once, hidden-by-reposition, and cloned) with a value type that
    // screams on double-drop or missing drop -- exactly what `cargo miri test` needs to be
    // able to catch.
    //
    // `m.view()` alone yields `&DropProbe`, and dropping a reference is a no-op, so these all
    // go through `.cloned()` first to get owned values into `FilterView`'s cache. That means
    // the original `m` still owns its own independent `DropProbe`s, which is why every test
    // finishes by dropping `m` explicitly to account for those too.
    // -----------------------------------------------------------------------------

    use std::{cell::RefCell, rc::Rc};

    /// A value whose `Drop` records its id, so tests can assert every live value is dropped
    /// **exactly once** (no leak, no double-drop), regardless of whether it failed the filter,
    /// was taken via `get_data`, was hidden by `reposition`, or was duplicated by `Clone`.
    #[derive(Clone)]
    struct DropProbe(i32, Rc<RefCell<Vec<i32>>>);

    impl Drop for DropProbe {
        fn drop(&mut self) {
            self.1.borrow_mut().push(self.0);
        }
    }

    fn probe_map(
        entries: &[(u32, u8, i32)],
        log: &Rc<RefCell<Vec<i32>>>,
    ) -> PrefixMap<P, DropProbe> {
        let mut m = PrefixMap::new();
        for &(repr, len, id) in entries {
            m.insert(p(repr, len), DropProbe(id, log.clone()));
        }
        m
    }

    fn sorted(mut v: Vec<i32>) -> Vec<i32> {
        v.sort_unstable();
        v
    }

    #[test]
    fn filter_view_drops_filtered_out_value_immediately() {
        let log = Rc::new(RefCell::new(Vec::new()));
        let m = probe_map(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)], &log);

        let filtered = m.view().cloned().filter(|_, x| x.0 % 2 == 0);
        // Nothing has been visited yet: both entries live below the root's own node (which
        // covers lengths 0..=4), so `build_cache` at construction touched neither of them.
        assert_eq!(*log.borrow(), Vec::<i32>::new());

        // Navigate into the node holding the length-8 entry (a single `get_child` away from
        // the root). This runs `build_cache` on it, which drops the odd id (1) immediately
        // since it fails the predicate; `find` then correctly reports it as absent. The
        // length-16 entry lives in a different, deeper node that this never touches.
        assert!(filtered.find(&p(0x0a000000, 8)).is_some());
        assert_eq!(*log.borrow(), vec![1]);

        drop(m);
    }

    #[test]
    fn filter_view_dropped_without_iterating_drops_only_the_current_node() {
        let log = Rc::new(RefCell::new(Vec::new()));
        // 1 and 2 are within the root's own node (lengths 0..=4), so `FilterView::new` caches
        // them without any `get_child` call. 3 lives in a different, deeper node that is never
        // visited in this test, so it must never be cloned or appear in the log at all.
        let m = probe_map(&[(0, 1, 1), (0, 2, 2), (0x0a000000, 8, 3)], &log);

        let filtered = m.view().cloned().filter(|_, x| x.0 % 2 == 0);
        // 1 is odd and fails the predicate, so it's dropped immediately during `build_cache`.
        assert_eq!(*log.borrow(), vec![1]);

        // Dropping the view without ever navigating into 3's node drops only what's cached
        // for the current (root) node: the matched-but-untaken 2. 3 stays untouched.
        drop(filtered);
        assert_eq!(sorted(log.borrow().clone()), vec![1, 2]);

        drop(m);
    }

    #[test]
    fn filter_view_full_iteration_drops_each_value_exactly_once() {
        let log = Rc::new(RefCell::new(Vec::new()));
        let m = probe_map(
            &[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 3)],
            &log,
        );

        let got: Vec<(P, DropProbe)> = m
            .view()
            .cloned()
            .filter(|_, x| x.0 % 2 == 0)
            .into_iter()
            .collect();
        // 1 filtered out and already dropped; 2 taken and still alive in `got`.
        assert_eq!(*log.borrow(), vec![1, 3]);

        drop(got);
        assert_eq!(sorted(log.borrow().clone()), vec![1, 2, 3]);

        drop(m);
    }

    #[test]
    fn filter_view_get_child_drops_abandoned_ancestor_values() {
        let log = Rc::new(RefCell::new(Vec::new()));
        // All three entries lie on the same key path but in three different `MultiBitNode`s
        // (K = 5): depths 8, 16, and 24. `find_exact_value` walks `get_child` through the
        // ancestor nodes and `reposition`s within the final one.
        let m = probe_map(
            &[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a010100, 24, 4)],
            &log,
        );

        let got = m
            .view()
            .cloned()
            .filter(|_, x| x.0 % 2 == 0)
            .find_exact_value(&p(0x0a010100, 24));

        // 1 dropped immediately (filtered out in its node's `build_cache`).
        // 2 passed the filter but wasn't on the path taken by the final `reposition`; it's
        // abandoned (and dropped) when its parent `FilterView` is overwritten by
        // `view = view.get_child(...)` during `navigate_to`.
        // 4 is the match and is still alive, held by `got`.
        assert_eq!(sorted(log.borrow().clone()), vec![1, 2]);
        assert_eq!(got.as_ref().unwrap().1 .0, 4);

        drop(got);
        assert_eq!(sorted(log.borrow().clone()), vec![1, 2, 4]);

        drop(m);
    }

    #[test]
    fn filter_view_reposition_drops_abandoned_ancestor_within_same_node() {
        let log = Rc::new(RefCell::new(Vec::new()));
        // Both entries fall in the same `MultiBitNode` (K = 5 covers depths 5..=9): length 6
        // is an ancestor of length 8 along the same key path. `find_exact_value` for the
        // length-8 entry reaches this node via a single `get_child` from the root (which
        // caches both), then narrows to the exact target purely via `reposition` -- no
        // further `get_child` is involved. This is the only path that abandons a same-node
        // ancestor via `reposition`'s own drop loop rather than a `get_child` overwrite.
        let m = probe_map(&[(0, 6, 2), (0, 8, 4)], &log);

        let got = m
            .view()
            .cloned()
            .filter(|_, x| x.0 % 2 == 0)
            .find_exact_value(&p(0, 8));

        // 2 (length 6) passed the filter and was cached when `get_child` reached this node,
        // but falls outside the exact length-8 target's scope once `reposition` narrows to
        // it, so it's abandoned and dropped right there.
        assert_eq!(*log.borrow(), vec![2]);
        assert_eq!(got.as_ref().unwrap().1 .0, 4);

        drop(got);
        assert_eq!(sorted(log.borrow().clone()), vec![2, 4]);

        drop(m);
    }

    #[test]
    fn filter_view_clone_after_reposition_drops_hidden_owned_value_once() {
        let log = Rc::new(RefCell::new(Vec::new()));
        // Same same-node ancestor/descendant setup as above, but this time we clone the view
        // *after* it has been narrowed down to the length-8 target (via `find`, which uses
        // `reposition` internally), so the length-6 value is still `owned` but no longer in
        // `mask`. `Clone` must duplicate it from `owned`, not `mask`, or one of the two
        // independent copies would under-count its drops and the other would double drop.
        //
        // Length 7 (odd) sits on the same path and fails the filter outright, so it's dropped
        // immediately during `build_cache` and never enters `owned`/`cache` at all. It's here
        // to confirm `Clone` doesn't somehow resurrect or double-drop a value that was never
        // cached in the first place.
        let m = probe_map(&[(0, 6, 2), (0, 7, 3), (0, 8, 4)], &log);

        let view = m
            .view()
            .cloned()
            .filter(|_, x| x.0 % 2 == 0)
            .find(&p(0, 8))
            .unwrap();
        // 3 (length 7) failed the filter and was dropped during `build_cache`; 2 (length 6) is
        // now abandoned by `reposition` (inside `find`) and already dropped too.
        assert_eq!(sorted(log.borrow().clone()), vec![2, 3]);

        let cloned = view.clone();
        // Cloning must not re-observe or re-drop the already-gone length-6/length-7 values;
        // only the still-owned length-8 value gets duplicated.
        assert_eq!(sorted(log.borrow().clone()), vec![2, 3]);

        drop(view);
        drop(cloned);
        assert_eq!(sorted(log.borrow().clone()), vec![2, 3, 4, 4]);

        drop(m);
    }

    #[test]
    fn filter_view_clone_then_diverge_navigates_independently() {
        let log = Rc::new(RefCell::new(Vec::new()));
        // Predicate keeps even ids. 1/2 sit in the root's own node (lengths 1 and 2); 1 fails,
        // 2 passes. 3/4 and 5/6 sit under two *different* children of the root (the key's top
        // 5 bits differ: all-zero vs. starting with a 1), each pair mirroring the root's
        // fail/pass shape one node deeper (length 7 fails, length 10 passes and is the
        // `find_exact_value` target).
        let m = probe_map(
            &[
                (0x00000000, 1, 1),
                (0x00000000, 2, 2),
                (0x00000000, 7, 3),
                (0x00000000, 10, 4),
                (0x80000000, 7, 5),
                (0x80000000, 10, 6),
            ],
            &log,
        );

        let root = m.view().cloned().filter(|_, x| x.0 % 2 == 0);
        // 1 is odd and fails the predicate, dropped immediately; 2 passes and is cached.
        assert_eq!(*log.borrow(), vec![1]);

        let cloned = root.clone();
        // Cloning duplicated 2 (three independent copies now exist: `m`'s, `root`'s, and
        // `cloned`'s); nothing new dropped by the clone itself.
        assert_eq!(*log.borrow(), vec![1]);

        let got_left = root.find_exact_value(&p(0x00000000, 10));
        let got_right = cloned.find_exact_value(&p(0x80000000, 10));
        // Each traversal: abandons (drops) its own copy of 2 on the first `get_child` hop away
        // from the root, then drops its own copy of the odd, filtered-out 3/5 one node down.
        assert_eq!(sorted(log.borrow().clone()), vec![1, 2, 2, 3, 5]);
        assert_eq!(got_left.as_ref().unwrap().1 .0, 4);
        assert_eq!(got_right.as_ref().unwrap().1 .0, 6);

        drop(got_left);
        drop(got_right);
        assert_eq!(sorted(log.borrow().clone()), vec![1, 2, 2, 3, 4, 5, 6]);

        drop(m);
    }
}
