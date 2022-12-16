//! Description of the generic type `Prefix`.

use ipnet::{Ipv4Net, Ipv6Net};
use num_traits::{PrimInt, Unsigned, Zero};

/// Trait for defining prefixes.
pub trait Prefix: Sized {
    /// How can the prefix be represented. This must be one of `u8`, `u16`, `u32`, `u64`, or `u128`.
    type R: Unsigned + PrimInt + Zero;

    /// Get raw representation of the address, ignoring the prefix length. This function must return
    /// the representation with the mask already applied.
    fn repr(&self) -> Self::R;

    /// Prefix length
    fn prefix_len(&self) -> u8;

    /// Create a new prefix from the representation and the prefix pength.
    fn from_repr_len(repr: Self::R, len: u8) -> Self;

    /// mask `self.repr()` using `self.len()`. If you can guarantee that `repr` is already masked,
    /// them simply re-implement this function for your type.
    fn mask(&self) -> Self::R {
        self.repr() & mask_from_prefix_len(self.prefix_len())
    }

    /// Create a prefix that matches everything
    fn zero() -> Self {
        Self::from_repr_len(Self::R::zero(), 0)
    }

    /// longest common prefix
    fn longest_common_prefix(&self, other: &Self) -> Self {
        let a = self.mask();
        let b = other.mask();
        let len = ((a ^ b).leading_zeros() as u8)
            .min(self.prefix_len())
            .min(other.prefix_len());
        let repr = a & mask_from_prefix_len(len);
        Self::from_repr_len(repr, len)
    }

    /// Check if `self` contains `other` in its prefix range. This function also returns `True` if
    /// `self` is identical to `other`.
    fn contains(&self, other: &Self) -> bool {
        if self.prefix_len() > other.prefix_len() {
            return false;
        }
        other.repr() & mask_from_prefix_len(self.prefix_len()) == self.mask()
    }

    /// Check if a specific bit is set (counted from the left, where 0 is the first bit from the
    /// left).
    fn is_bit_set(&self, bit: u8) -> bool {
        let mask =
            ((!Self::R::zero()) >> bit as usize) ^ ((!Self::R::zero()) >> (1usize + bit as usize));
        mask & self.mask() != Self::R::zero()
    }

    /// Compare two prefixes together
    fn eq(&self, other: &Self) -> bool {
        self.mask() == other.mask() && self.prefix_len() == other.prefix_len()
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

    fn eq(&self, other: &Self) -> bool {
        self == other
    }

    fn mask(&self) -> u32 {
        self.network().into()
    }

    fn zero() -> Self {
        Default::default()
    }

    fn longest_common_prefix(&self, other: &Self) -> Self {
        let a = self.repr();
        let b = other.repr();
        let len = ((a ^ b).leading_zeros() as u8)
            .min(self.prefix_len())
            .min(other.prefix_len());
        let repr = a & mask_from_prefix_len::<u32>(len);
        Ipv4Net::new(repr.into(), len).unwrap()
    }

    fn contains(&self, other: &Self) -> bool {
        self.contains(other)
    }
}

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

    fn eq(&self, other: &Self) -> bool {
        self == other
    }

    fn mask(&self) -> u128 {
        self.network().into()
    }

    fn zero() -> Self {
        Default::default()
    }

    fn longest_common_prefix(&self, other: &Self) -> Self {
        let a = self.repr();
        let b = other.repr();
        let len = ((a ^ b).leading_zeros() as u8)
            .min(self.prefix_len())
            .min(other.prefix_len());
        let repr = a & mask_from_prefix_len::<u128>(len);
        Ipv6Net::new(repr.into(), len).unwrap()
    }

    fn contains(&self, other: &Self) -> bool {
        self.contains(other)
    }
}

impl<R> Prefix for (R, u8)
where
    R: Unsigned + PrimInt + Zero,
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

    fn eq(&self, other: &Self) -> bool {
        self == other
    }
}

#[cfg(test)]
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

    #[test]
    fn longest_common_prefix() {
        macro_rules! assert_lcp {
            ($a:literal, $b:literal, $c:literal) => {
                assert_eq!(pfx!($a).longest_common_prefix(&pfx!($b)), pfx!($c));
                assert_eq!(pfx!($b).longest_common_prefix(&pfx!($a)), pfx!($c));
            };
        }
        assert_lcp!("1.2.3.4/24", "1.3.3.4/24", "1.2.0.0/15");
        assert_lcp!("1.2.3.4/24", "1.1.3.4/24", "1.0.0.0/14");
        assert_lcp!("1.2.3.4/24", "1.2.3.4/30", "1.2.3.0/24");
    }

    #[test]
    fn is_bit_set() {
        assert!(pfx!("255.0.0.0/8").is_bit_set(0));
        assert!(pfx!("255.0.0.0/8").is_bit_set(7));
        assert!(!pfx!("255.0.0.0/8").is_bit_set(8));
        assert!(!pfx!("255.255.0.0/8").is_bit_set(8));
    }
}
