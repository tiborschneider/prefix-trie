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

/// Clones each value of the wrapped view before yielding them.
#[derive(Clone, Copy)]
pub struct ClonedView<'a, V, T> {
    pub(super) view: V,
    pub(super) _marker: PhantomData<&'a T>,
}

impl<'a, 'b, V, T> TrieView<'a> for ClonedView<'a, V, T>
where
    V: TrieView<'a, T = &'b T>,
    T: Clone + 'b,
{
    type P = V::P;
    type T = T;

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
        inner.clone()
    }

    unsafe fn get_child(&mut self, child_bit: u32) -> Self {
        Self {
            view: self.view.get_child(child_bit),
            _marker: PhantomData,
        }
    }

    unsafe fn reposition(&mut self, key: <Self::P as crate::Prefix>::R, prefix_len: u32) {
        self.view.reposition(key, prefix_len)
    }
}

impl<'a, 'b, V, T> AsView<'a> for ClonedView<'a, V, T>
where
    V: TrieView<'a, T = &'b T>,
    T: Clone + 'b,
{
    type P = V::P;
    type View = Self;

    fn view(self) -> Self {
        self
    }
}

impl<'a, 'b, V, T> IntoIterator for ClonedView<'a, V, T>
where
    V: TrieView<'a, T = &'b T>,
    T: Clone + 'b,
{
    type Item = (V::P, T);
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
    fn map_view_iter_and_as_view() {
        let m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2), (0x0a020000, 16, 3)]);
        let mapped = m.view().map(|x| *x * 10);
        // AsView::view() on a MapView returns itself.
        let got: Vec<(P, i32)> = mapped.view().into_iter().collect();
        assert_eq!(
            got,
            vec![
                (p(0x0a000000, 8), 10),
                (p(0x0a010000, 16), 20),
                (p(0x0a020000, 16), 30),
            ]
        );
    }

    #[test]
    fn cloned_view_into_iter_and_as_view() {
        let mut m: PrefixMap<P, Vec<i32>> = PrefixMap::new();
        m.insert(p(0x0a000000, 8), vec![1]);
        m.insert(p(0x0a010000, 16), vec![2, 3]);

        let cloned = m.view().cloned();
        let got: Vec<(P, Vec<i32>)> = cloned.view().into_iter().collect();
        assert_eq!(
            got,
            vec![(p(0x0a000000, 8), vec![1]), (p(0x0a010000, 16), vec![2, 3])]
        );
    }

    #[test]
    fn copied_view_into_iter_and_as_view() {
        let m = map_from(&[(0x0a000000, 8, 1), (0x0a010000, 16, 2)]);

        let copied = m.view().copied();
        let got: Vec<(P, i32)> = copied.view().into_iter().collect();
        assert_eq!(got, vec![(p(0x0a000000, 8), 1), (p(0x0a010000, 16), 2)]);
    }
}

/// Copies each value of the wrapped view before yielding them.
#[derive(Clone, Copy)]
pub struct CopiedView<'a, V, T> {
    pub(super) view: V,
    pub(super) _marker: PhantomData<&'a T>,
}

impl<'a, 'b, V, T> TrieView<'a> for CopiedView<'a, V, T>
where
    V: TrieView<'a, T = &'b T>,
    T: Copy + 'b,
{
    type P = V::P;
    type T = T;

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
        *inner
    }

    unsafe fn get_child(&mut self, child_bit: u32) -> Self {
        Self {
            view: self.view.get_child(child_bit),
            _marker: PhantomData,
        }
    }

    unsafe fn reposition(&mut self, key: <Self::P as crate::Prefix>::R, prefix_len: u32) {
        self.view.reposition(key, prefix_len)
    }
}

impl<'a, 'b, V, T> AsView<'a> for CopiedView<'a, V, T>
where
    V: TrieView<'a, T = &'b T>,
    T: Copy + 'b,
{
    type P = V::P;
    type View = Self;

    fn view(self) -> Self {
        self
    }
}

impl<'a, 'b, V, T> IntoIterator for CopiedView<'a, V, T>
where
    V: TrieView<'a, T = &'b T>,
    T: Copy + 'b,
{
    type Item = (V::P, T);
    type IntoIter = ViewIter<'a, Self>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
