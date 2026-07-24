//! Map view
//!
//! [`MapView`] only applies a transformation function to values of a view.

use std::marker::PhantomData;

use crate::{trieview::ViewIter, AsView, TrieView};

/// Applies a transformation to each value of its wrapping view.
#[derive(Clone, Copy)]
pub struct MapView<'a, V, F, U> {
    pub(super) view: V,
    pub(super) f: F,
    pub(super) _marker: PhantomData<&'a U>,
}

impl<'a, V, F, U> TrieView<'a> for MapView<'a, V, F, U>
where
    V: TrieView<'a>,
    F: Fn(V::T) -> U + Clone,
    U: 'a,
{
    type P = V::P;
    type T = U;

    fn depth(&self) -> u32 {
        self.view.depth()
    }

    fn key(&self) -> <Self::P as crate::Prefix>::R {
        self.view.key()
    }

    fn prefix_len(&self) -> u32 {
        self.view.prefix_len()
    }

    fn data_bitmap(&self) -> u32 {
        self.view.data_bitmap()
    }

    fn child_bitmap(&self) -> u32 {
        self.view.child_bitmap()
    }

    unsafe fn get_data(&mut self, data_bit: u32) -> Self::T {
        let inner = self.view.get_data(data_bit);
        (self.f)(inner)
    }

    unsafe fn get_child(&mut self, child_bit: u32) -> Self {
        Self {
            view: self.view.get_child(child_bit),
            f: self.f.clone(),
            _marker: PhantomData,
        }
    }

    unsafe fn reposition(&mut self, key: <Self::P as crate::Prefix>::R, prefix_len: u32) {
        self.view.reposition(key, prefix_len)
    }
}

impl<'a, V, F, U> AsView<'a> for MapView<'a, V, F, U>
where
    V: TrieView<'a>,
    F: Fn(V::T) -> U + Clone,
    U: 'a,
{
    type P = V::P;
    type View = Self;

    fn view(self) -> Self {
        self
    }
}

impl<'a, V, F, U> IntoIterator for MapView<'a, V, F, U>
where
    V: TrieView<'a>,
    F: Fn(V::T) -> U + Clone,
    U: 'a,
{
    type Item = (V::P, U);
    type IntoIter = ViewIter<'a, Self>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
