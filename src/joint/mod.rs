//! Module that defines the joint version of a prefix map and set, including all helper
//! functions. You can access each individual table of the prefix map, allowing you to perform the
//! usual operations set operations.
//!
//! Unfortunately, a joint prefix map always returns owned instances of the (joint) prefix, and,
//! thus, always creates copied of the prefixes. This should not be any problem, as IPv4 and IPv6
//! prefixes implement `Copy`. However, this might become an issue when using larger types.

macro_rules! fork {
    ($self:ident, $prefix:ident, $func:ident $(, $args:expr),*) => {
        match $prefix.p1_or_p2() {
            ::either::Either::Left(p) => $self.t1.$func(p$(, $args),*),
            ::either::Either::Right(p) => $self.t2.$func(p$(, $args),*),
        }
    };
    ($self:ident, $prefix:ident as ($P:ty,T), $func:ident $(, $args:expr),*) => {
        match $prefix.p1_or_p2() {
            ::either::Either::Left(p) => $self.t1.$func(p$(, $args),*).map(|(p, t)| ($P::from_p1(p), t)),
            ::either::Either::Right(p) => $self.t2.$func(p$(, $args),*).map(|(p, t)| ($P::from_p2(p), t)),
        }
    };
    ($self:ident, $prefix:ident as $P:ty, $func:ident $(, $args:expr),*) => {
        match $prefix.p1_or_p2() {
            ::either::Either::Left(p) => $self.t1.$func(p$(, $args),*).map(|p| $P::from_p1(p)),
            ::either::Either::Right(p) => $self.t2.$func(p$(, $args),*).map(|p| $P::from_p2(p)),
        }
    };
}

macro_rules! fork_ref {
    ($self:ident, $prefix:ident, $func:ident $(, $args:expr),*) => {
        match $prefix.p1_or_p2_ref() {
            ::either::Either::Left(p) => $self.t1.$func(p$(, $args),*),
            ::either::Either::Right(p) => $self.t2.$func(p$(, $args),*),
        }
    };
    ($self:ident, $prefix:ident as ($P:ty,T), $func:ident $(, $args:expr),*) => {
        match $prefix.p1_or_p2_ref() {
            ::either::Either::Left(p) => $self.t1.$func(p$(, $args),*).map(|(p, t)| (<$P>::from_p1(p), t)),
            ::either::Either::Right(p) => $self.t2.$func(p$(, $args),*).map(|(p, t)| (<$P>::from_p2(p), t)),
        }
    };
    ($self:ident, $prefix:ident as $P:ty, $func:ident $(, $args:expr),*) => {
        match $prefix.p1_or_p2_ref() {
            ::either::Either::Left(p) => $self.t1.$func(p$(, $args),*).map(|p| <$P>::from_p1(p)),
            ::either::Either::Right(p) => $self.t2.$func(p$(, $args),*).map(|p| <$P>::from_p2(p)),
        }
    };
}

pub mod map;
mod prefix;
pub mod set;

pub use map::JointPrefixMap;
pub use prefix::JointPrefix;
pub use set::JointPrefixSet;
