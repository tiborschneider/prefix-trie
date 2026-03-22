//! Prefix trait and implementations.

#[cfg(feature = "cidr")]
use cidr::{Ipv4Cidr, Ipv4Inet, Ipv6Cidr, Ipv6Inet};
#[cfg(feature = "ipnet")]
use ipnet::{Ipv4Net, Ipv6Net};
#[cfg(feature = "ipnetwork")]
use ipnetwork::{Ipv4Network, Ipv6Network};
use num_traits::{CheckedShr, One, PrimInt, Unsigned, Zero};

/// A fixed-width prefix key.
///
/// `PrefixMap` and `PrefixSet` store trie positions, not prefix values. They derive those
/// positions from [`Prefix::repr`] and [`Prefix::prefix_len`], and reconstruct returned prefixes
/// with [`Prefix::from_repr_len`]. Host bits outside the prefix length may be present in `repr()`,
/// but they are ignored for matching and are not preserved when prefixes are reconstructed.
pub trait Prefix: Sized + std::fmt::Debug {
    /// Unsigned integer representation used as the trie key.
    ///
    /// The most significant bit is the first prefix bit. This is normally one of the unsigned
    /// primitive integers (`u8`, `u16`, `u32`, `u64`, `u128`, or `usize`) and should have the same
    /// width as the address family being represented.
    type R: Unsigned + PrimInt + Zero + One + CheckedShr;

    /// Returns the number of bits used to represent addresses and prefixes.
    fn num_bits() -> u32 {
        Self::R::zero().count_zeros()
    }

    /// Returns the raw address bits.
    ///
    /// This value does not have to be masked to [`Prefix::prefix_len`]. For example, an IPv4
    /// `192.0.2.1/24` value may return the raw bits for `192.0.2.1`, not `192.0.2.0`. Implementors
    /// must ensure that the prefix bits occupy the most significant bits of the returned integer.
    fn repr(&self) -> Self::R;

    /// Returns the prefix length in bits.
    ///
    /// The returned value must be in the range `0..=Self::num_bits()`.
    fn prefix_len(&self) -> u8;

    /// Creates a prefix from raw address bits and a prefix length.
    ///
    /// The map and set call this with host bits already masked out when reconstructing stored
    /// prefixes. Implementations may also canonicalize `repr` themselves if the underlying prefix
    /// type cannot represent host bits.
    fn from_repr_len(repr: Self::R, len: u8) -> Self;

    /// Returns the canonical network bits for this prefix.
    ///
    /// The default implementation masks [`Prefix::repr`] using [`Prefix::prefix_len`]. Override
    /// this when the underlying type can return the masked network address directly.
    fn mask(&self) -> Self::R {
        self.repr() & mask_from_prefix_len(self.prefix_len())
    }

    /// Checks if `self` contains `other` in its prefix range. This function also returns `true` if
    /// `self` is identical to `other`.
    fn contains(&self, other: &Self) -> bool {
        if self.prefix_len() > other.prefix_len() {
            return false;
        }
        other.repr() & mask_from_prefix_len(self.prefix_len()) == self.mask()
    }
}

pub(crate) fn mask_from_prefix_len<R>(len: u8) -> R
where
    R: PrimInt + Zero,
{
    if len as u32 == R::zero().count_zeros() {
        !R::zero()
    } else if len == 0 {
        R::zero()
    } else {
        !((!R::zero()) >> len as usize)
    }
}

#[cfg(feature = "ipnet")]
impl Prefix for Ipv4Net {
    type R = u32;

    fn repr(&self) -> u32 {
        self.addr().into()
    }

    fn prefix_len(&self) -> u8 {
        self.prefix_len()
    }

    fn from_repr_len(repr: u32, len: u8) -> Self {
        Ipv4Net::new(repr.into(), len).unwrap()
    }

    fn mask(&self) -> u32 {
        self.network().into()
    }

    fn contains(&self, other: &Self) -> bool {
        self.contains(other)
    }
}

#[cfg(feature = "ipnet")]
impl Prefix for Ipv6Net {
    type R = u128;

    fn repr(&self) -> u128 {
        self.addr().into()
    }

    fn prefix_len(&self) -> u8 {
        self.prefix_len()
    }

    fn from_repr_len(repr: u128, len: u8) -> Self {
        Ipv6Net::new(repr.into(), len).unwrap()
    }

    fn mask(&self) -> u128 {
        self.network().into()
    }

    fn contains(&self, other: &Self) -> bool {
        self.contains(other)
    }
}

#[cfg(feature = "ipnetwork")]
impl Prefix for Ipv4Network {
    type R = u32;

    fn repr(&self) -> u32 {
        self.ip().into()
    }

    fn prefix_len(&self) -> u8 {
        self.prefix()
    }

    fn from_repr_len(repr: u32, len: u8) -> Self {
        Ipv4Network::new(repr.into(), len).unwrap()
    }

    fn mask(&self) -> u32 {
        self.network().into()
    }
}

#[cfg(feature = "ipnetwork")]
impl Prefix for Ipv6Network {
    type R = u128;

    fn repr(&self) -> u128 {
        self.ip().into()
    }

    fn prefix_len(&self) -> u8 {
        self.prefix()
    }

    fn from_repr_len(repr: u128, len: u8) -> Self {
        Ipv6Network::new(repr.into(), len).unwrap()
    }

    fn mask(&self) -> u128 {
        self.network().into()
    }
}

#[cfg(feature = "cidr")]
impl Prefix for Ipv4Cidr {
    type R = u32;

    fn repr(&self) -> Self::R {
        self.first_address().into()
    }

    fn prefix_len(&self) -> u8 {
        self.network_length()
    }

    fn from_repr_len(repr: Self::R, len: u8) -> Self {
        let repr = repr & mask_from_prefix_len::<Self::R>(len);
        Self::new(repr.into(), len).unwrap()
    }

    fn mask(&self) -> Self::R {
        self.first_address().into()
    }
}

#[cfg(feature = "cidr")]
impl Prefix for Ipv6Cidr {
    type R = u128;

    fn repr(&self) -> Self::R {
        self.first_address().into()
    }

    fn prefix_len(&self) -> u8 {
        self.network_length()
    }

    fn from_repr_len(repr: Self::R, len: u8) -> Self {
        let repr = repr & mask_from_prefix_len::<Self::R>(len);
        Self::new(repr.into(), len).unwrap()
    }

    fn mask(&self) -> Self::R {
        self.first_address().into()
    }
}

#[cfg(feature = "cidr")]
impl Prefix for Ipv4Inet {
    type R = u32;

    fn repr(&self) -> Self::R {
        self.address().into()
    }

    fn prefix_len(&self) -> u8 {
        self.network_length()
    }

    fn from_repr_len(repr: Self::R, len: u8) -> Self {
        Self::new(repr.into(), len).unwrap()
    }

    fn mask(&self) -> Self::R {
        self.network().first_address().into()
    }
}

#[cfg(feature = "cidr")]
impl Prefix for Ipv6Inet {
    type R = u128;

    fn repr(&self) -> Self::R {
        self.address().into()
    }

    fn prefix_len(&self) -> u8 {
        self.network_length()
    }

    fn from_repr_len(repr: Self::R, len: u8) -> Self {
        Self::new(repr.into(), len).unwrap()
    }

    fn mask(&self) -> Self::R {
        self.network().first_address().into()
    }
}

impl<R> Prefix for (R, u8)
where
    R: Unsigned + PrimInt + Zero + CheckedShr + std::fmt::Debug,
{
    type R = R;

    fn repr(&self) -> R {
        self.0
    }

    fn prefix_len(&self) -> u8 {
        self.1
    }

    fn from_repr_len(repr: R, len: u8) -> Self {
        (repr, len)
    }
}

#[cfg(test)]
#[cfg(feature = "ipnet")]
mod test {
    use super::*;

    macro_rules! pfx {
        ($p:literal) => {
            $p.parse::<Ipv4Net>().unwrap()
        };
    }

    #[test]
    fn mask_from_len() {
        assert_eq!(mask_from_prefix_len::<u8>(3), 0b11100000);
        assert_eq!(mask_from_prefix_len::<u8>(5), 0b11111000);
        assert_eq!(mask_from_prefix_len::<u8>(8), 0b11111111);
        assert_eq!(mask_from_prefix_len::<u8>(0), 0b00000000);

        assert_eq!(mask_from_prefix_len::<u32>(0), 0x00000000);
        assert_eq!(mask_from_prefix_len::<u32>(8), 0xff000000);
        assert_eq!(mask_from_prefix_len::<u32>(16), 0xffff0000);
        assert_eq!(mask_from_prefix_len::<u32>(24), 0xffffff00);
        assert_eq!(mask_from_prefix_len::<u32>(32), 0xffffffff);
    }

    #[test]
    fn prefix_mask() {
        let addr = pfx!("10.1.0.0/8");
        assert_eq!(Prefix::prefix_len(&addr), 8);
        assert_eq!(Prefix::repr(&addr), (10 << 24) + (1 << 16));
        assert_eq!(Prefix::mask(&addr), 10u32 << 24);
    }

    #[test]
    fn contains() {
        let larger = pfx!("10.128.0.0/9");
        let smaller = pfx!("10.0.0.0/8");
        let larger_c = pfx!("10.130.2.5/9");
        let smaller_c = pfx!("10.25.2.8/8");
        assert!(smaller.contains(&larger));
        assert!(smaller.contains(&larger_c));
        assert!(smaller_c.contains(&larger));
        assert!(smaller_c.contains(&larger_c));
        assert!(!larger.contains(&smaller));
        assert!(!larger.contains(&smaller_c));
        assert!(!larger_c.contains(&smaller));
        assert!(!larger_c.contains(&smaller_c));
        assert!(smaller.contains(&smaller));
        assert!(smaller.contains(&smaller_c));
        assert!(smaller_c.contains(&smaller));
        assert!(smaller_c.contains(&smaller_c));
    }

    #[generic_tests::define]
    mod t {
        use num_traits::NumCast;

        use super::*;

        fn new<P: Prefix>(repr: u32, len: u8) -> P {
            let repr = <<P as Prefix>::R as NumCast>::from(repr).unwrap();
            let num_zeros = <<P as Prefix>::R as Zero>::zero().count_zeros() as u8;
            let len = len + (num_zeros - 32);
            P::from_repr_len(repr, len)
        }

        #[test]
        fn repr_len<P: Prefix>() {
            for x in [0x01000000u32, 0x010f0000u32, 0xffff0000u32] {
                let repr = <<P as Prefix>::R as NumCast>::from(x).unwrap();
                let num_zeros = <<P as Prefix>::R as Zero>::zero().count_zeros() as u8;
                let len = 16 + (num_zeros - 32);
                let prefix = P::from_repr_len(repr, len);
                assert!(prefix.repr() == repr);
                assert!(prefix.prefix_len() == len);
            }
        }

        #[test]
        fn keep_host_addr<P: Prefix + 'static>() {
            #[allow(unused_mut)]
            #[allow(unused_assignments)]
            let mut prefix_is_masked = false;
            #[cfg(feature = "cidr")]
            {
                let p_id = std::any::TypeId::of::<P>();
                // Ipv4Cidr and Ipv6Cidr addresses are always masked.
                prefix_is_masked = p_id == std::any::TypeId::of::<cidr::Ipv4Cidr>()
                    || p_id == std::any::TypeId::of::<cidr::Ipv6Cidr>();
            }
            let mask = 0xffff0000u32;
            for mut x in [0x01001234u32, 0x010fabcdu32, 0xffff5678u32] {
                let prefix: P = new(x, 16);
                if prefix_is_masked {
                    x &= mask;
                }
                assert_eq!(<u32 as NumCast>::from(prefix.repr()), Some(x));
            }
        }

        #[test]
        fn mask<P: Prefix>() {
            let mask = 0xffff0000u32;
            for x in [0x01001234u32, 0x010fabcdu32, 0xffff5678u32] {
                let prefix: P = new(x, 16);
                assert_eq!(<u32 as NumCast>::from(prefix.mask()), Some(x & mask));
            }
        }

        #[test]
        fn contains<P: Prefix>() {
            assert!(new::<P>(0x01020000, 16).contains(&new(0x0102ffff, 24)));
            assert!(new::<P>(0x01020304, 16).contains(&new(0x0102ffff, 24)));
            assert!(new::<P>(0x01020304, 16).contains(&new(0x0102ffff, 16)));
            assert!(!new::<P>(0x01020304, 24).contains(&new(0x0102ffff, 16)));
        }

        #[instantiate_tests(<Ipv4Net>)]
        mod ipv4net {}

        #[instantiate_tests(<Ipv6Net>)]
        mod ipv6net {}

        #[cfg(feature = "ipnetwork")]
        #[instantiate_tests(<Ipv4Network>)]
        mod ipv4network {}

        #[cfg(feature = "ipnetwork")]
        #[instantiate_tests(<Ipv6Network>)]
        mod ipv6network {}

        #[cfg(feature = "cidr")]
        #[instantiate_tests(<Ipv4Cidr>)]
        mod ipv4cidr {}

        #[cfg(feature = "cidr")]
        #[instantiate_tests(<Ipv4Inet>)]
        mod ipv4inet {}

        #[cfg(feature = "cidr")]
        #[instantiate_tests(<Ipv6Cidr>)]
        mod ipv6cidr {}

        #[cfg(feature = "cidr")]
        #[instantiate_tests(<Ipv6Inet>)]
        mod ipv6inet {}

        #[instantiate_tests(<(u32, u8)>)]
        mod u32_u8 {}

        #[instantiate_tests(<(u64, u8)>)]
        mod u64_u8 {}
    }
}
