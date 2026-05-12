//! Composable trie-view trait for [`crate::PrefixMap`].
//!
//! # Architecture
//!
//! [`TrieView`] is a **trait** implemented by any cursor (mutable or immutable)
//! into a prefix trie:
//! - [`TrieRef`]: an immutable cursor yielding `&T`
//! - [`TrieRefMut`]: a mutable cursor yielding `&mut T`
//! - Composed views: [`IntersectionView`], [`UnionView`], [`CoveringUnionView`],
//!   [`DifferenceView`], [`CoveringDifferenceView`]
//!
//! This design makes set operations **composable**:
//!
//! ```
//! # use prefix_trie::{PrefixMap, PrefixSet, AsView, TrieView};
//! # use prefix_trie::trieview::union::UnionItem;
//! # type P = (u32, u8);
//! let mut target: PrefixMap::<P, _> = [((0, 8), 1), ((0, 16), 2), ((0, 24), 3)].into_iter().collect();
//! let source:     PrefixMap::<P, _> = [((0, 8), 9), ((0, 16), 1)].into_iter().collect();
//! let ignore:     PrefixSet::<P>    = [ (0, 10)].into_iter().collect();
//!
//! (&mut target)
//!     .view()
//!     .union(&source)
//!     .covering_difference(&ignore)
//!     .values()
//!     .for_each(|x| if let UnionItem::Both(l, r) = x {
//!         *l += *r
//!     });
//!
//! assert_eq!(
//!     target.into_iter().collect::<Vec<_>>(),
//!     vec![((0, 8), 10), ((0, 16), 2), ((0, 24), 3)], // only (0, 8) got updated
//! );
//! ```
//!
//! # Safety contract for `get_data`, `get_child`, and `reposition`
//!
//! The three unsafe primitives carry the following contracts:
//!
//! - **`get_data`**: each `data_bit` must be passed **at most once** per view instance.
//! - **`get_child`**: each `child_bit` must be passed **at most once** per view instance.
//! - For mutable views, values reached through different data bits, values reachable through
//!   different child bits, and values stored in a node versus values reachable through its child
//!   views must be disjoint from each other.
//! - **`reposition`**: the returned cursor shares the same underlying node as `self`.
//!   For mutable views the caller must ensure the two cursors' effective bitmaps are
//!   disjoint, or that the original is not used for data access after the call.
//!
//! All default methods uphold these invariants internally.
//!
//! # Clone and mutable views
//!
//! The `TrieView` trait does **not** require `Self: Clone`. Mutable views
//! ([`TrieRefMut`]) intentionally do not implement `Clone` to prevent aliasing
//! `&mut` references. Methods that need to retain an earlier cursor while descending,
//! such as [`find_lpm`][TrieView::find_lpm], require `Self: Clone`. Methods that
//! return an element directly, such as [`find_lpm_value`][TrieView::find_lpm_value],
//! can work with mutable views because they do not need to return a saved cursor.
//!
//! Composed views implement `Clone` only when their sides do. This naturally means clone-backed
//! methods such as [`find_lpm`][TrieView::find_lpm] are unavailable on composed mutable views,
//! while consuming methods such as [`find_lpm_value`][TrieView::find_lpm_value] remain usable.

pub mod covering_difference;
pub mod covering_union;
pub mod difference;
pub mod intersection;
pub(crate) mod iter;
pub mod trie_ref;
pub mod trie_ref_mut;
pub mod union;

pub use covering_difference::CoveringDifferenceView;
pub use covering_union::{CoveringUnionItem, CoveringUnionView};
pub use difference::DifferenceView;
pub use intersection::IntersectionView;
pub use iter::{ViewIter, ViewKeys, ViewValues};
pub use trie_ref::TrieRef;
pub use trie_ref_mut::TrieRefMut;
pub use union::{UnionItem, UnionView};

use num_traits::{One, PrimInt, Zero};

use crate::{
    prefix::mask_from_prefix_len,
    Prefix,
    {
        node::{child_bit, data_bit, data_lpm_mask, DATA_BIT_TO_PREFIX},
        table::K,
    },
};

/// An immutable or mutable view into a (possibly composed) prefix trie.
///
/// # Required methods
///
/// Eight methods that concrete and composed views must implement:
/// - **Position**: [`Self::depth`], [`Self::key`], [`Self::prefix_len`]
/// - **Bitmaps**: [`Self::data_bitmap`], [`Self::child_bitmap`]
/// - **Primitives** (unsafe): [`Self::get_data`], [`Self::get_child`], [`Self::reposition`]
///
/// # Default methods
///
/// All other methods (`left`/`right`/`find`/`find_lpm`/`iter`/etc.) are
/// provided as defaults built from the eight required methods.
pub trait TrieView<'a>: Sized {
    /// The prefix type.
    type P: Prefix;
    /// The value type yielded by this view (e.g. `&'a T`, `&'a mut T`, `(&'a L, &'a R)`).
    type T: 'a;

    /// Depth of the underlying `MultiBitNode`: always a multiple of `K`.
    fn depth(&self) -> u32;

    /// Accumulated key bits; only the top [`prefix_len`][Self::prefix_len] bits are significant.
    fn key(&self) -> <Self::P as Prefix>::R;

    /// Binary-tree depth of this view's root position (`depth <= prefix_len < depth + K`).
    fn prefix_len(&self) -> u32;

    /// Effective data bitmap (node bitmap ANDed with cover mask and any set-op filter).
    ///
    /// A set bit at position `b` means there is a value accessible via
    /// [`get_data(b)`][Self::get_data].
    fn data_bitmap(&self) -> u32;

    /// Effective child bitmap (node bitmap ANDed with cover mask and any set-op filter).
    ///
    /// A set bit at position `b` means there is a non-empty sub-trie reachable via
    /// [`get_child(b)`][Self::get_child].
    fn child_bitmap(&self) -> u32;

    /// Return the value at `data_bit`.
    ///
    /// # Safety
    /// Each `data_bit` must be passed to this method **at most once** per view instance.
    /// For mutable views (`T = &'a mut T`), calling with the same bit twice produces two
    /// aliasing `&'a mut T` references -> undefined behavior.
    ///
    /// # Panics
    /// May panic or return garbage if `data_bit` is not set in [`data_bitmap`][Self::data_bitmap].
    unsafe fn get_data(&mut self, data_bit: u32) -> Self::T;

    /// Return a child view at `child_bit`.
    ///
    /// The returned view has `depth = self.depth() + K`, `prefix_len = self.depth() + K`,
    /// and `key = extend_repr(self.key(), self.depth(), child_bit)`.
    ///
    /// # Safety
    /// Each `child_bit` must be passed to this method **at most once** per view instance.
    /// For mutable views, calling with the same bit twice creates two views with overlapping
    /// mutable access to the same child node -> undefined behavior. Different bits always
    /// refer to disjoint child nodes and are safe to combine.
    ///
    /// # Panics
    /// May panic if `child_bit` is not set in [`child_bitmap`][Self::child_bitmap].
    unsafe fn get_child(&mut self, child_bit: u32) -> Self;

    /// Move the cursor to a different location within the same multibit-node.
    ///
    /// The underlying node location (and all data pointers) remain unchanged; only the
    /// position cursor is updated.
    ///
    /// # Safety
    /// For mutable views, the returned cursor shares the same `raw_ptr` and `node_loc`
    /// as `self`. The caller must ensure that the returned cursor and `self` are never
    /// simultaneously used to access overlapping data -> either by ensuring their effective
    /// bitmaps are disjoint or by not accessing `self`'s data after the call (as in
    /// `navigate_to` and `step`).
    unsafe fn reposition(&mut self, key: <Self::P as Prefix>::R, prefix_len: u32);

    // -----------------------------------------------------------------------------
    // Default implementations
    // -----------------------------------------------------------------------------

    /// Whether the sub-trie rooted at this view position is non-empty.
    ///
    /// A shallow bitmap check: `true` means data or children exist worth exploring.
    /// `false` means the sub-trie is definitely empty.
    #[inline]
    fn is_non_empty(&self) -> bool {
        self.data_bitmap() != 0 || self.child_bitmap() != 0
    }

    /// Reconstruct the prefix at this view's root position.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map = PrefixMap::new();
    /// map.insert(net!("192.168.0.0/20"), 1);
    /// map.insert(net!("192.168.0.0/22"), 2);
    ///
    /// let view = map.view().find(&net!("192.168.0.0/21")).unwrap();
    /// assert_eq!(view.prefix(), net!("192.168.0.0/21"));
    /// # }
    /// ```
    #[inline]
    fn prefix(&self) -> Self::P {
        let masked = self.key() & mask_from_prefix_len(self.prefix_len() as u8);
        Self::P::from_repr_len(masked, self.prefix_len() as u8)
    }

    /// Return the value stored exactly at this view's root position, if any.
    ///
    /// This method consumes the view, which makes it suitable for mutable views.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map = PrefixMap::new();
    /// map.insert(net!("192.168.0.0/20"), 1);
    /// map.insert(net!("192.168.0.0/22"), 2);
    ///
    /// assert_eq!(map.view().find_exact(&net!("192.168.0.0/22")).unwrap().value(), Some(&2));
    /// assert_eq!(map.view().find(&net!("192.168.0.0/21")).unwrap().value(), None);
    /// # }
    /// ```
    #[inline]
    fn value(mut self) -> Option<Self::T> {
        let data_bit = data_bit(self.key(), self.prefix_len());
        if (self.data_bitmap() >> data_bit) & 1 == 1 {
            // SAFETY: `value` consumes the view and calls `get_data` for one bit.
            Some(unsafe { self.get_data(data_bit) })
        } else {
            None
        }
    }

    /// Return the prefix and value stored exactly at this view's root position, if any.
    ///
    /// This method consumes the view, which makes it suitable for mutable views.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map = PrefixMap::new();
    /// map.insert(net!("192.168.0.0/22"), 2);
    ///
    /// let view = map.view().find_exact(&net!("192.168.0.0/22")).unwrap();
    /// assert_eq!(view.prefix_value(), Some((net!("192.168.0.0/22"), &2)));
    /// # }
    /// ```
    #[inline]
    fn prefix_value(mut self) -> Option<(Self::P, Self::T)> {
        let data_bit = data_bit(self.key(), self.prefix_len());
        if (self.data_bitmap() >> data_bit) & 1 == 1 {
            let prefix = self.prefix();
            // SAFETY: `prefix_value` consumes the view and calls `get_data` for one bit.
            Some((prefix, unsafe { self.get_data(data_bit) }))
        } else {
            None
        }
    }

    /// Return a view into the left (0-bit) child sub-trie, or `None` if empty.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map = PrefixMap::new();
    /// map.insert(net!("10.0.0.0/8"), 1);
    ///
    /// let left = map.view().left().unwrap();
    /// assert_eq!(left.prefix(), net!("0.0.0.0/1"));
    /// assert_eq!(left.keys().collect::<Vec<_>>(), vec![net!("10.0.0.0/8")]);
    /// # }
    /// ```
    #[inline]
    fn left(self) -> Option<Self> {
        self.step(false)
    }

    /// Return a view into the right (1-bit) child sub-trie, or `None` if empty.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map = PrefixMap::new();
    /// map.insert(net!("128.0.0.0/1"), 1);
    ///
    /// let right = map.view().right().unwrap();
    /// assert_eq!(right.prefix(), net!("128.0.0.0/1"));
    /// assert_eq!(right.value(), Some(&1));
    /// # }
    /// ```
    #[inline]
    fn right(self) -> Option<Self> {
        self.step(true)
    }

    /// Navigate toward `(target_key, target_len)` from this view's node.
    ///
    /// Returns `None` if a required child node does not exist in [`child_bitmap`][Self::child_bitmap].
    fn navigate_to(mut self, target_key: <Self::P as Prefix>::R, target_len: u32) -> Option<Self> {
        while target_len >= self.depth() + K {
            let child_bit = child_bit(self.depth(), target_key);
            if (self.child_bitmap() >> child_bit) & 1 == 0 {
                return None;
            }
            // SAFETY: follows a single path; each child_bit used exactly once per
            // view instance before view is replaced by the returned child.
            self = unsafe { self.get_child(child_bit) };
        }
        // SAFETY: view is replaced by the repositioned cursor; the old position is
        // not used for data access after this point.
        unsafe { self.reposition(target_key, target_len) }
        Some(self)
    }

    /// Navigate to `prefix` and return the view if the sub-trie is non-empty.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map = PrefixMap::new();
    /// map.insert(net!("192.168.0.0/20"), 1);
    /// map.insert(net!("192.168.0.0/22"), 2);
    /// map.insert(net!("192.168.0.0/24"), 3);
    ///
    /// let sub = map.view().find(&net!("192.168.0.0/21")).unwrap();
    /// assert_eq!(
    ///     sub.keys().collect::<Vec<_>>(),
    ///     vec![net!("192.168.0.0/22"), net!("192.168.0.0/24")]
    /// );
    /// # }
    /// ```
    #[inline]
    fn find(self, prefix: &Self::P) -> Option<Self> {
        let view = self.navigate_to(prefix.mask(), prefix.prefix_len() as u32)?;
        if view.is_non_empty() {
            Some(view)
        } else {
            None
        }
    }

    /// Navigate to `prefix` and return the view only if a value is stored exactly there.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map = PrefixMap::new();
    /// map.insert(net!("192.168.0.0/20"), 1);
    /// map.insert(net!("192.168.0.0/22"), 2);
    ///
    /// assert!(map.view().find_exact(&net!("192.168.0.0/21")).is_none());
    /// assert_eq!(
    ///     map.view().find_exact(&net!("192.168.0.0/22")).unwrap().value(),
    ///     Some(&2)
    /// );
    /// # }
    /// ```
    #[inline]
    fn find_exact(self, prefix: &Self::P) -> Option<Self> {
        let view = self.navigate_to(prefix.mask(), prefix.prefix_len() as u32)?;
        let data_bit = data_bit(view.key(), view.prefix_len());
        if (view.data_bitmap() >> data_bit) & 1 == 1 {
            Some(view)
        } else {
            None
        }
    }

    /// Navigate to `prefix` and return its prefix/value pair if a value is stored exactly there.
    ///
    /// This method consumes the view and does not require `Self: Clone`, so it also works with
    /// mutable views.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map = PrefixMap::new();
    /// map.insert(net!("192.168.0.0/22"), 2);
    ///
    /// assert_eq!(
    ///     map.view().find_exact_value(&net!("192.168.0.0/22")),
    ///     Some((net!("192.168.0.0/22"), &2))
    /// );
    /// assert_eq!(map.view().find_exact_value(&net!("192.168.0.0/21")), None);
    /// # }
    /// ```
    #[inline]
    fn find_exact_value(self, prefix: &Self::P) -> Option<(Self::P, Self::T)> {
        let view = self.navigate_to(prefix.mask(), prefix.prefix_len() as u32)?;
        view.prefix_value()
    }

    /// Find the view pointing at the longest prefix match for `prefix`.
    ///
    /// This method requires `Self: Clone` because the search must remember the best matching view
    /// while it continues descending toward more-specific prefixes.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map = PrefixMap::new();
    /// map.insert(net!("192.168.0.0/20"), 1);
    /// map.insert(net!("192.168.0.0/22"), 2);
    ///
    /// let view = map.view().find_lpm(&net!("192.168.0.0/21")).unwrap();
    /// assert_eq!(view.prefix(), net!("192.168.0.0/20"));
    /// assert_eq!(view.value(), Some(&1));
    /// # }
    /// ```
    fn find_lpm(mut self, prefix: &Self::P) -> Option<Self>
    where
        Self: Clone,
    {
        let target_key = prefix.mask();
        let target_len = prefix.prefix_len() as u32;
        if !contains_key::<Self::P>(self.key(), self.prefix_len(), target_key, target_len) {
            return None;
        }
        let mut best = None;

        loop {
            if let Some(data_bit) = lpm_data_bit(&self, target_key, target_len) {
                let prefix = reconstruct_prefix::<Self::P>(self.depth(), self.key(), data_bit);
                let mut view = self.clone();
                // SAFETY: the cloned cursor is moved within its current multibit node.
                unsafe { view.reposition(prefix.mask(), prefix.prefix_len() as u32) };
                best = Some(view);
            }

            if target_len < self.depth() + K {
                return best;
            }

            let child_bit = child_bit(self.depth(), target_key);
            if (self.child_bitmap() >> child_bit) & 1 == 0 {
                return best;
            }

            // SAFETY: follows a single path; each child bit is used at most once per view.
            self = unsafe { self.get_child(child_bit) };
        }
    }

    /// Find the longest prefix match for `prefix` and return its prefix/value pair.
    ///
    /// This method does not require `Self: Clone`; it can therefore be used with views that yield
    /// mutable references. It consumes the view and only returns the matched element, not a cursor.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map = PrefixMap::new();
    /// map.insert(net!("192.168.0.0/20"), 1);
    /// map.insert(net!("192.168.0.0/22"), 2);
    ///
    /// let (prefix, value) = (&mut map)
    ///     .view()
    ///     .find_lpm_value(&net!("192.168.0.0/21"))
    ///     .unwrap();
    ///
    /// assert_eq!(prefix, net!("192.168.0.0/20"));
    /// *value += 10;
    /// assert_eq!(map.get(&net!("192.168.0.0/20")), Some(&11));
    /// # }
    /// ```
    fn find_lpm_value(mut self, prefix: &Self::P) -> Option<(Self::P, Self::T)> {
        let target_key = prefix.mask();
        let target_len = prefix.prefix_len() as u32;
        if !contains_key::<Self::P>(self.key(), self.prefix_len(), target_key, target_len) {
            return None;
        }
        let mut best = None;

        loop {
            if let Some(data_bit) = lpm_data_bit(&self, target_key, target_len) {
                let prefix = reconstruct_prefix::<Self::P>(self.depth(), self.key(), data_bit);
                drop(best.take());
                // SAFETY: each node on the target path is visited at most once, and we keep only
                // the most-specific matched value.
                best = Some((prefix, unsafe { self.get_data(data_bit) }));
            }

            if target_len < self.depth() + K {
                return best;
            }

            let child_bit = child_bit(self.depth(), target_key);
            if (self.child_bitmap() >> child_bit) & 1 == 0 {
                return best;
            }

            // SAFETY: follows a single path; each child bit is used at most once per view.
            self = unsafe { self.get_child(child_bit) };
        }
    }

    /// Return an iterator over all `(prefix, value)` pairs in this sub-trie.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map = PrefixMap::new();
    /// map.insert(net!("192.168.0.0/20"), 1);
    /// map.insert(net!("192.168.0.0/22"), 2);
    /// map.insert(net!("192.168.0.0/24"), 3);
    ///
    /// let sub = map.view().find(&net!("192.168.0.0/22")).unwrap();
    /// assert_eq!(
    ///     sub.iter().collect::<Vec<_>>(),
    ///     vec![(net!("192.168.0.0/22"), &2), (net!("192.168.0.0/24"), &3)]
    /// );
    /// # }
    /// ```
    #[inline]
    fn iter(self) -> ViewIter<'a, Self> {
        ViewIter::new(self)
    }

    /// Return an iterator over all prefixes in this sub-trie.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map = PrefixMap::new();
    /// map.insert(net!("192.168.0.0/20"), 1);
    /// map.insert(net!("192.168.0.0/22"), 2);
    /// map.insert(net!("192.168.0.0/24"), 3);
    ///
    /// let sub = map.view().find(&net!("192.168.0.0/22")).unwrap();
    /// assert_eq!(
    ///     sub.keys().collect::<Vec<_>>(),
    ///     vec![net!("192.168.0.0/22"), net!("192.168.0.0/24")]
    /// );
    /// # }
    /// ```
    #[inline]
    fn keys(self) -> ViewKeys<'a, Self> {
        ViewKeys::new(self)
    }

    /// Return an iterator over all values in this sub-trie.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut map = PrefixMap::new();
    /// map.insert(net!("192.168.0.0/20"), 1);
    /// map.insert(net!("192.168.0.0/22"), 2);
    /// map.insert(net!("192.168.0.0/24"), 3);
    ///
    /// let sub = map.view().find(&net!("192.168.0.0/22")).unwrap();
    /// assert_eq!(sub.values().copied().collect::<Vec<_>>(), vec![2, 3]);
    /// # }
    /// ```
    #[inline]
    fn values(self) -> ViewValues<'a, Self> {
        ViewValues::new(self)
    }

    /// Return the intersection of `self` and `other` as a view, or `None` if disjoint.
    ///
    /// The returned [`IntersectionView`] iterates over every prefix present in **both**
    /// sub-tries, yielding `(prefix, (left_value, right_value))` in lexicographic order.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut left = PrefixMap::new();
    /// left.insert(net!("10.0.0.0/8"), 1);
    /// left.insert(net!("10.1.0.0/16"), 2);
    ///
    /// let mut right = PrefixMap::new();
    /// right.insert(net!("10.1.0.0/16"), 20);
    /// right.insert(net!("10.1.1.0/24"), 30);
    ///
    /// let got: Vec<_> = left
    ///     .view()
    ///     .intersection(&right)
    ///     .unwrap()
    ///     .iter()
    ///     .map(|(prefix, (left, right))| (prefix, *left, *right))
    ///     .collect();
    ///
    /// assert_eq!(got, vec![(net!("10.1.0.0/16"), 2, 20)]);
    /// # }
    /// ```
    #[inline]
    fn intersection<R>(self, other: R) -> Option<IntersectionView<'a, Self, R::View>>
    where
        R: AsView<'a, P = Self::P>,
    {
        IntersectionView::new(self, other.view())
    }

    /// Return the union of `self` and `other` as a view.
    ///
    /// The returned [`UnionView`] iterates over every prefix present in **either** sub-trie,
    /// yielding `(prefix, UnionItem)` in lexicographic order.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # use prefix_trie::trieview::union::UnionItem;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut left = PrefixMap::new();
    /// left.insert(net!("10.0.0.0/8"), 1);
    /// left.insert(net!("10.1.0.0/16"), 2);
    ///
    /// let mut right = PrefixMap::new();
    /// right.insert(net!("10.1.0.0/16"), 20);
    /// right.insert(net!("10.1.1.0/24"), 30);
    ///
    /// let got: Vec<_> = left
    ///     .view()
    ///     .union(&right)
    ///     .iter()
    ///     .map(|(prefix, item)| match item {
    ///         UnionItem::Left(left) => (prefix, Some(*left), None),
    ///         UnionItem::Right(right) => (prefix, None, Some(*right)),
    ///         UnionItem::Both(left, right) => (prefix, Some(*left), Some(*right)),
    ///     })
    ///     .collect();
    ///
    /// assert_eq!(
    ///     got,
    ///     vec![
    ///         (net!("10.0.0.0/8"), Some(1), None),
    ///         (net!("10.1.0.0/16"), Some(2), Some(20)),
    ///         (net!("10.1.1.0/24"), None, Some(30)),
    ///     ]
    /// );
    /// # }
    /// ```
    #[inline]
    fn union<R>(self, other: R) -> UnionView<'a, Self, R::View>
    where
        R: AsView<'a, P = Self::P>,
    {
        UnionView::new(self, other.view())
    }

    /// Return the covering union of `self` and `other` as a view.
    ///
    /// The returned [`CoveringUnionView`] iterates over every prefix present in either sub-trie.
    /// For prefixes present on only one side, the yielded item includes the longest prefix match
    /// from the opposite side when one exists inside that opposite view.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # use prefix_trie::trieview::CoveringUnionItem;
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut left = PrefixMap::new();
    /// left.insert(net!("10.1.0.0/16"), 2);
    ///
    /// let mut right = PrefixMap::new();
    /// right.insert(net!("10.0.0.0/8"), 10);
    ///
    /// let (_, item) = left
    ///     .view()
    ///     .covering_union(&right)
    ///     .iter()
    ///     .find(|(prefix, _)| prefix == &net!("10.1.0.0/16"))
    ///     .unwrap();
    ///
    /// match item {
    ///     CoveringUnionItem::Left {
    ///         left,
    ///         right_lpm: Some((right_prefix, right)),
    ///     } => {
    ///         assert_eq!(*left, 2);
    ///         assert_eq!(right_prefix, net!("10.0.0.0/8"));
    ///         assert_eq!(*right, 10);
    ///     }
    ///     _ => panic!("expected a left-only prefix covered by the right side"),
    /// }
    /// # }
    /// ```
    #[inline]
    fn covering_union<R>(self, other: R) -> CoveringUnionView<'a, Self, R::View>
    where
        Self: Clone,
        R: AsView<'a, P = Self::P>,
        R::View: Clone,
    {
        CoveringUnionView::new(self, other.view())
    }

    /// Return the difference of `self` minus `other` as a view.
    ///
    /// The returned [`DifferenceView`] iterates over every prefix present in `self` but
    /// **not** in `other`, yielding values from `self` in lexicographic order.
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut left = PrefixMap::new();
    /// left.insert(net!("10.0.0.0/8"), 1);
    /// left.insert(net!("10.1.0.0/16"), 2);
    /// left.insert(net!("10.1.1.0/24"), 3);
    ///
    /// let mut right = PrefixMap::new();
    /// right.insert(net!("10.1.0.0/16"), 20);
    ///
    /// let got: Vec<_> = left
    ///     .view()
    ///     .difference(&right)
    ///     .iter()
    ///     .map(|(prefix, value)| (prefix, *value))
    ///     .collect();
    ///
    /// assert_eq!(got, vec![(net!("10.0.0.0/8"), 1), (net!("10.1.1.0/24"), 3)]);
    /// # }
    /// ```
    #[inline]
    fn difference<R>(self, other: R) -> DifferenceView<'a, Self, R::View>
    where
        R: AsView<'a, P = Self::P>,
    {
        DifferenceView::new(self, other.view())
    }

    /// Return the covering difference of `self` minus `other` as a view.
    ///
    /// Iterates over every prefix `P_l` in `self` for which no covering prefix `P_r`
    /// exists in `other` (`P_r.len ≤ P_l.len` and `P_r` matches `P_l`'s leading bits).
    ///
    /// ```
    /// # use prefix_trie::{PrefixMap, AsView, TrieView};
    /// # #[cfg(feature = "ipnet")]
    /// macro_rules! net { ($x:literal) => { $x.parse::<ipnet::Ipv4Net>().unwrap() }; }
    ///
    /// # #[cfg(feature = "ipnet")]
    /// # {
    /// let mut left = PrefixMap::new();
    /// left.insert(net!("10.0.0.0/8"), 1);
    /// left.insert(net!("10.1.0.0/16"), 2);
    /// left.insert(net!("10.1.1.0/24"), 3);
    ///
    /// let mut right = PrefixMap::new();
    /// right.insert(net!("10.1.0.0/16"), 20);
    ///
    /// let got: Vec<_> = left
    ///     .view()
    ///     .covering_difference(&right)
    ///     .iter()
    ///     .map(|(prefix, value)| (prefix, *value))
    ///     .collect();
    ///
    /// assert_eq!(got, vec![(net!("10.0.0.0/8"), 1)]);
    /// # }
    /// ```
    #[inline]
    fn covering_difference<R>(self, other: R) -> CoveringDifferenceView<'a, Self, R::View>
    where
        R: AsView<'a, P = Self::P>,
    {
        CoveringDifferenceView::new(self, other.view())
    }

    // -----------------------------------------------------------------------------
    // Private helper
    // -----------------------------------------------------------------------------

    /// Step one binary level deeper, going left (0-bit) or right (1-bit).
    fn step(mut self, go_right: bool) -> Option<Self> {
        let new_prefix_len = self.prefix_len() + 1;
        let new_key = if go_right {
            let bit_pos = <Self::P as Prefix>::R::zero().count_zeros() - self.prefix_len() - 1;
            self.key() | <Self::P as Prefix>::R::one().unsigned_shl(bit_pos)
        } else {
            self.key()
        };

        if new_prefix_len < self.depth() + K {
            // Intra-node: narrow the position cursor within the same node.
            // SAFETY: self is not used for data access after this; only `view` is used.
            unsafe { self.reposition(new_key, new_prefix_len) };
            if self.is_non_empty() {
                Some(self)
            } else {
                None
            }
        } else {
            // Cross into a child node (new_prefix_len == depth + K).
            let child_bit = child_bit(self.depth(), new_key);
            if (self.child_bitmap() >> child_bit) & 1 == 0 {
                return None;
            }
            // SAFETY: step is called for one direction at a time; child_bit is used once.
            Some(unsafe { self.get_child(child_bit) })
        }
    }
}

fn contains_key<P: Prefix>(
    root_key: P::R,
    root_len: u32,
    target_key: P::R,
    target_len: u32,
) -> bool {
    if root_len > target_len {
        return false;
    }
    let mask = mask_from_prefix_len(root_len as u8);
    root_key & mask == target_key & mask
}

fn lpm_data_bit<'a, V: TrieView<'a>>(
    view: &V,
    target_key: <V::P as Prefix>::R,
    target_len: u32,
) -> Option<u32> {
    let data_bits = view.data_bitmap() & data_lpm_mask(view.depth(), target_key, target_len);
    if data_bits == 0 {
        None
    } else {
        Some(u32::BITS - 1 - data_bits.leading_zeros())
    }
}

/// Reconstruct the prefix at `data_bit` within the node starting at `depth`.
pub(crate) fn reconstruct_prefix<P: Prefix>(depth: u32, key: P::R, data_bit: u32) -> P {
    let (offset, level) = DATA_BIT_TO_PREFIX[data_bit as usize];
    let prefix_len = depth + level as u32;
    let root = key & mask_from_prefix_len(depth as u8);
    let offset_r = <P::R as num_traits::cast::NumCast>::from(offset).unwrap();
    let offset_bits = K - 1;
    let total_width = P::num_bits();
    let shifted = if total_width > depth + offset_bits {
        offset_r << (total_width - (depth + offset_bits)) as usize
    } else {
        offset_r >> (depth + offset_bits - total_width) as usize
    };
    P::from_repr_len(root | shifted, prefix_len as u8)
}

/// Trait that is implemented on structures that can be turned into a view.
pub trait AsView<'a> {
    /// The prefix type.
    type P: Prefix;
    /// The concrete view type returned by [`view`][AsView::view].
    type View: TrieView<'a, P = Self::P>;

    /// Get a view rooted at the origin (the entire trie).
    fn view(self) -> Self::View;

    /// Get a view rooted at `prefix`, or `None` if the sub-trie is empty.
    fn view_at(self, prefix: &Self::P) -> Option<Self::View>
    where
        Self: Sized,
    {
        self.view().find(prefix)
    }
}
