use crate::{
    fuzzing::*,
    joint::{JointPrefix, JointPrefixMap, JointPrefixSet},
    qc, Prefix, PrefixMap, PrefixSet,
};
use rkyv::{
    access,
    api::high::{HighSerializer, HighValidator},
    bytecheck::CheckBytes,
    from_bytes,
    rancor::Error,
    ser::allocator::ArenaHandle,
    to_bytes,
    util::AlignedVec,
};

macro_rules! rkyv_eq_test {
    ($X:ident < $P:ident $(, $T:ty)?>, $fn:ident () $(.$collect:ident())?) => {
        paste::paste! {
            qc!($fn, [<_ $fn>]);
            #[allow(unused_parens)]
            fn [<_ $fn>](ops: Vec<Operation<$P, ($($T)?)>>) -> bool {
                let trie = <$X<$P $(, $T)?>>::from_ops(ops);
                let a = trie.$fn()$(.$collect::<Vec<_>>())?.into_owned();
                let b = rkyv_map(&trie, |x| x.$fn()$(.$collect::<Vec<_>>())?.into_native());
                a == b
            }
        }
    };
    ($X:ident < $P:ident $(, $T:ty)?>, $fn:ident ($arg:ty) $(.$collect:ident())?) => {
        paste::paste! {
            qc!($fn, [<_ $fn>]);
            #[allow(unused_parens)]
            fn [<_ $fn>]((ops, arg): (Vec<Operation<$P, ($($T)?)>>, $arg)) -> bool {
                let trie = <$X<$P $(, $T)?>>::from_ops(ops);
                let a = trie.$fn(&arg)$(.$collect::<Vec<_>>())?.into_owned();
                let b = rkyv_map(&trie, |x| x.$fn(&arg)$(.$collect::<Vec<_>>())?.into_native());
                a == b
            }
        }
    };
    ($X:ident < $P:ident $(, $T:ty)?>, $fn:ident ($arg1:ty, $arg2:ty) $(.$collect:ident())?) => {
        paste::paste! {
            qc!($fn, [<_ $fn>]);
            #[allow(unused_parens)]
            fn [<_ $fn>]((ops, arg1, arg2): (Vec<Operation<$P, ($($T)?)>>, $arg1, $arg2)) -> bool {
                let trie = <$X<$P $(, $T)?>>::from_ops(ops);
                let a = trie.$fn(&arg1, arg2)$(.$collect::<Vec<_>>())?.into_owned();
                let b = rkyv_map(&trie, |x| x.$fn(&arg1, arg2)$(.$collect::<Vec<_>>())?.into_native());
                a == b
            }
        }
    };
}

mod map {

    use super::*;
    type P = TestPrefix;

    qc!(serialize_canonical_bytes, _serialize_canonical_bytes);
    fn _serialize_canonical_bytes(ops: Vec<Operation<P, i32>>) -> bool {
        let trie = <PrefixMap<P, i32>>::from_ops(ops);
        let fresh: PrefixMap<_, _> = trie.iter().map(|(p, t)| (p, *t)).collect();

        let trie_bytes = to_bytes::<Error>(&trie).unwrap();
        let fresh_bytes = to_bytes::<Error>(&fresh).unwrap();

        trie_bytes.as_slice() == fresh_bytes.as_slice()
    }

    qc!(deserialize_validate, _deserialize_validate);
    fn _deserialize_validate(ops: Vec<Operation<P, i32>>) -> bool {
        let trie = <PrefixMap<P, i32>>::from_ops(ops);
        let trie_bytes = to_bytes::<Error>(&trie).unwrap();
        let archived = from_bytes::<PrefixMap<P, i32>, Error>(trie_bytes.as_slice()).unwrap();

        trie == archived
    }

    rkyv_eq_test!(PrefixMap<P, i32>, len());
    rkyv_eq_test!(PrefixMap<P, i32>, is_empty());
    rkyv_eq_test!(PrefixMap<P, i32>, address_count());
    rkyv_eq_test!(PrefixMap<P, i32>, get(P));
    rkyv_eq_test!(PrefixMap<P, i32>, contains_key(P));
    rkyv_eq_test!(PrefixMap<P, i32>, get_key_value(P));
    rkyv_eq_test!(PrefixMap<P, i32>, get_lpm(P));
    rkyv_eq_test!(PrefixMap<P, i32>, get_lpm_prefix(P));
    rkyv_eq_test!(PrefixMap<P, i32>, get_spm(P));
    rkyv_eq_test!(PrefixMap<P, i32>, get_spm_prefix(P));
    rkyv_eq_test!(PrefixMap<P, i32>, iter().collect());
    rkyv_eq_test!(PrefixMap<P, i32>, keys().collect());
    rkyv_eq_test!(PrefixMap<P, i32>, values().collect());
    rkyv_eq_test!(PrefixMap<P, i32>, iter_from(P, bool).collect());
    rkyv_eq_test!(PrefixMap<P, i32>, cover(P).collect());
    rkyv_eq_test!(PrefixMap<P, i32>, cover_keys(P).collect());
    rkyv_eq_test!(PrefixMap<P, i32>, cover_values(P).collect());
}

mod set {
    use super::*;
    type P = TestPrefix;

    qc!(serialize_canonical_bytes, _serialize_canonical_bytes);
    fn _serialize_canonical_bytes(ops: Vec<Operation<P, ()>>) -> bool {
        let trie = <PrefixSet<P>>::from_ops(ops);
        let fresh: PrefixSet<_> = trie.iter().collect();

        let trie_bytes = to_bytes::<Error>(&trie).unwrap();
        let fresh_bytes = to_bytes::<Error>(&fresh).unwrap();

        trie_bytes.as_slice() == fresh_bytes.as_slice()
    }

    qc!(deserialize_validate, _deserialize_validate);
    fn _deserialize_validate(ops: Vec<Operation<P, ()>>) -> bool {
        let trie = <PrefixSet<P>>::from_ops(ops);
        let trie_bytes = to_bytes::<Error>(&trie).unwrap();
        let archived = from_bytes::<PrefixSet<P>, Error>(trie_bytes.as_slice()).unwrap();

        trie == archived
    }

    rkyv_eq_test!(PrefixSet<P>, len());
    rkyv_eq_test!(PrefixSet<P>, is_empty());
    rkyv_eq_test!(PrefixSet<P>, address_count());
    rkyv_eq_test!(PrefixSet<P>, contains(P));
    rkyv_eq_test!(PrefixSet<P>, get(P));
    rkyv_eq_test!(PrefixSet<P>, get_lpm(P));
    rkyv_eq_test!(PrefixSet<P>, get_spm(P));
    rkyv_eq_test!(PrefixSet<P>, iter().collect());
    rkyv_eq_test!(PrefixSet<P>, iter_from(P, bool).collect());
    rkyv_eq_test!(PrefixSet<P>, cover(P).collect());
}

mod joint {
    use super::*;
    type P = JointTestPrefix;

    mod map {
        use super::*;

        qc!(serialize_canonical_bytes, _serialize_canonical_bytes);
        fn _serialize_canonical_bytes(ops: Vec<Operation<P, i32>>) -> bool {
            let trie = <JointPrefixMap<P, i32>>::from_ops(ops);

            let t1: PrefixMap<_, _> = trie.t1.iter().map(|(p, t)| (p, *t)).collect();
            let t2: PrefixMap<_, _> = trie.t2.iter().map(|(p, t)| (p, *t)).collect();
            let fresh = JointPrefixMap::<P, _> { t1, t2 };

            let trie_bytes = to_bytes::<Error>(&trie).unwrap();
            let fresh_bytes = to_bytes::<Error>(&fresh).unwrap();

            trie_bytes.as_slice() == fresh_bytes.as_slice()
        }

        qc!(deserialize_validate, _deserialize_validate);
        fn _deserialize_validate(ops: Vec<Operation<P, i32>>) -> bool {
            let trie = <JointPrefixMap<P, i32>>::from_ops(ops);

            let trie_bytes = to_bytes::<Error>(&trie).unwrap();
            let archived =
                from_bytes::<JointPrefixMap<P, i32>, Error>(trie_bytes.as_slice()).unwrap();

            trie == archived
        }

        rkyv_eq_test!(JointPrefixMap<P, i32>, len());
        rkyv_eq_test!(JointPrefixMap<P, i32>, is_empty());
        rkyv_eq_test!(JointPrefixMap<P, i32>, address_count());
        rkyv_eq_test!(JointPrefixMap<P, i32>, get(P));
        rkyv_eq_test!(JointPrefixMap<P, i32>, contains_key(P));
        rkyv_eq_test!(JointPrefixMap<P, i32>, get_key_value(P));
        rkyv_eq_test!(JointPrefixMap<P, i32>, get_lpm(P));
        rkyv_eq_test!(JointPrefixMap<P, i32>, get_lpm_prefix(P));
        rkyv_eq_test!(JointPrefixMap<P, i32>, get_spm(P));
        rkyv_eq_test!(JointPrefixMap<P, i32>, get_spm_prefix(P));
        rkyv_eq_test!(JointPrefixMap<P, i32>, iter().collect());
        rkyv_eq_test!(JointPrefixMap<P, i32>, keys().collect());
        rkyv_eq_test!(JointPrefixMap<P, i32>, values().collect());
        rkyv_eq_test!(JointPrefixMap<P, i32>, iter_from(P, bool).collect());
        rkyv_eq_test!(JointPrefixMap<P, i32>, cover(P).collect());
        rkyv_eq_test!(JointPrefixMap<P, i32>, cover_keys(P).collect());
        rkyv_eq_test!(JointPrefixMap<P, i32>, cover_values(P).collect());
    }

    mod set {
        use super::*;

        qc!(serialize_canonical_bytes, _serialize_canonical_bytes);
        fn _serialize_canonical_bytes(ops: Vec<Operation<P, ()>>) -> bool {
            let trie = <JointPrefixSet<P>>::from_ops(ops);

            let t1: PrefixSet<_> = trie.t1.iter().collect();
            let t2: PrefixSet<_> = trie.t2.iter().collect();
            let fresh = JointPrefixSet::<P> { t1, t2 };

            let trie_bytes = to_bytes::<Error>(&trie).unwrap();
            let fresh_bytes = to_bytes::<Error>(&fresh).unwrap();

            trie_bytes.as_slice() == fresh_bytes.as_slice()
        }

        qc!(deserialize_validate, _deserialize_validate);
        fn _deserialize_validate(ops: Vec<Operation<P, ()>>) -> bool {
            let trie = <JointPrefixSet<P>>::from_ops(ops);
            let trie_bytes = to_bytes::<Error>(&trie).unwrap();
            let archived = from_bytes::<JointPrefixSet<P>, Error>(trie_bytes.as_slice()).unwrap();

            trie == archived
        }

        rkyv_eq_test!(JointPrefixSet<P>, len());
        rkyv_eq_test!(JointPrefixSet<P>, is_empty());
        rkyv_eq_test!(JointPrefixSet<P>, address_count());
        rkyv_eq_test!(JointPrefixSet<P>, contains(P));
        rkyv_eq_test!(JointPrefixSet<P>, get(P));
        rkyv_eq_test!(JointPrefixSet<P>, get_lpm(P));
        rkyv_eq_test!(JointPrefixSet<P>, get_spm(P));
        rkyv_eq_test!(JointPrefixSet<P>, iter().collect());
        rkyv_eq_test!(JointPrefixSet<P>, iter_from(P, bool).collect());
        rkyv_eq_test!(JointPrefixSet<P>, cover(P).collect());
    }
}

// ---------------------------------------------------------
// Traits and functions needed for the macro to work.
// ---------------------------------------------------------

#[rustfmt::skip]
mod helper {
    use super::*;

    pub(super) fn rkyv_map<T, R>(value: &T, f: impl FnOnce(&rkyv::Archived<T>) -> R) -> R
    where
        T: for<'a> rkyv::Serialize<HighSerializer<AlignedVec, ArenaHandle<'a>, Error>>,
        rkyv::Archived<T>: for<'a> CheckBytes<HighValidator<'a, Error>>,
    {
        let bytes = to_bytes::<Error>(value).unwrap();
        let archived = access::<rkyv::Archived<T>, Error>(bytes.as_slice()).unwrap();
        f(archived)
    }

    pub(super) trait IntoNative {
        type Native;
        fn into_native(self) -> Self::Native;
    }

    macro_rules! impl_into_native {
        ($T:ty) => {
            impl IntoNative for $T {
                type Native = $T;
                fn into_native(self) -> $T { self }
            }
        };
    }

    impl_into_native!(TestPrefix);
    impl_into_native!(JointTestPrefix);
    impl_into_native!(usize);
    impl_into_native!(bool);
    impl_into_native!(u32);

    impl IntoNative for &rkyv::rend::i32_le {
        type Native = i32;
        fn into_native(self) -> i32 { self.to_native() }
    }

    impl<A: IntoNative, B: IntoNative> IntoNative for (A, B) {
        type Native = (A::Native, B::Native);
        fn into_native(self) -> Self::Native { (self.0.into_native(), self.1.into_native()) }
    }

    impl<T: IntoNative> IntoNative for Option<T> {
        type Native = Option<T::Native>;
        fn into_native(self) -> Self::Native { self.map(|x| x.into_native()) }
    }

    impl<T: IntoNative> IntoNative for Vec<T> {
        type Native = Vec<T::Native>;
        fn into_native(self) -> Self::Native { self.into_iter().map(|x| x.into_native()).collect() }
    }

    pub(super) trait IntoOwned {
        type Owned;
        fn into_owned(self) -> Self::Owned;
    }

    macro_rules! impl_into_owned {
        ($T:ty) => {
            impl IntoOwned for $T {
                type Owned = $T;
                fn into_owned(self) -> $T { self }
            }
        };
    }

    impl_into_owned!(TestPrefix);
    impl_into_owned!(JointTestPrefix);
    impl_into_owned!(usize);
    impl_into_owned!(bool);
    impl_into_owned!(u32);

    impl<T: Clone> IntoOwned for &T {
        type Owned = T;
        fn into_owned(self) -> T { self.clone() }
    }

    impl<A: IntoOwned, B: IntoOwned> IntoOwned for (A, B) {
        type Owned = (A::Owned, B::Owned);
        fn into_owned(self) -> Self::Owned { (self.0.into_owned(), self.1.into_owned()) }
    }

    impl<T: IntoOwned> IntoOwned for Option<T> {
        type Owned = Option<T::Owned>;
        fn into_owned(self) -> Self::Owned { self.map(|x| x.into_owned()) }
    }

    impl<T: IntoOwned> IntoOwned for Vec<T> {
        type Owned = Vec<T::Owned>;
        fn into_owned(self) -> Self::Owned { self.into_iter().map(|x| x.into_owned()).collect() }
    }

    pub(super) trait FromOps<P>: Sized {
        type Value;
        fn empty() -> Self;
        fn add(&mut self, prefix: P, value: Self::Value);
        fn del(&mut self, prefix: &P);
        fn del_children(&mut self, prefix: &P);

        fn from_ops(ops: Vec<Operation<P, Self::Value>>) -> Self {
            let mut this = Self::empty();
            for op in ops {
                match op {
                    Operation::Add(p, v) => this.add(p, v),
                    Operation::Remove(p) => this.del(&p),
                    Operation::RemoveChildren(p) => this.del_children(&p),
                }
            }
            this
        }
    }

    macro_rules! impl_from_ops {
        (map, $Map:ident : $P: ident) => {
            impl<P: $P> FromOps<P> for $Map<P, i32> {
                type Value = i32;
                fn empty() -> Self { Self::new() }
                fn add(&mut self, p: P, v: i32) { self.insert(p, v); }
                fn del(&mut self, p: &P) { self.remove(p); }
                fn del_children(&mut self, p: &P) { self.remove_children(p); }
            }
        };
        (set, $Set:ident : $P: ident) => {
            impl<P: $P> FromOps<P> for $Set<P> {
                type Value = ();
                fn empty() -> Self { Self::new() }
                fn add(&mut self, p: P, _: ()) { self.insert(p); }
                fn del(&mut self, p: &P) { self.remove(p); }
                fn del_children(&mut self, p: &P) { self.remove_children(p); }
            }
        };
    }

    impl_from_ops!(map, PrefixMap: Prefix);
    impl_from_ops!(map, JointPrefixMap: JointPrefix);
    impl_from_ops!(set, PrefixSet: Prefix);
    impl_from_ops!(set, JointPrefixSet: JointPrefix);
}

use helper::*;
