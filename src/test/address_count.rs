#[generic_tests::define]
mod t {
    use super::super::*;

    /// Helper: expected address count for a prefix of given length in a `P::num_bits()`-bit space.
    fn expected_count<P: Prefix>(prefix_len: u8) -> u128 {
        let host_bits = P::num_bits() - prefix_len as u32;
        1u128 << host_bits
    }

    // ── PrefixMap ──────────────────────────────────────────────────────────

    #[test]
    fn map_address_count_single_prefix<P: Prefix>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("10.0.0.0/24"), 1);
        assert_eq!(pm.address_count(), Some(expected_count::<P>(24)));
    }

    #[test]
    fn map_address_count_non_overlapping<P: Prefix>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("10.0.0.0/24"), 1);
        pm.insert(ip("10.0.1.0/24"), 2);
        assert_eq!(pm.address_count(), Some(2 * expected_count::<P>(24)));
    }

    #[test]
    fn map_address_count_overlapping<P: Prefix>() {
        // /24 covers /25; the /25 should not add extra addresses after aggregation
        let mut pm = Map::<P>::new();
        pm.insert(ip("10.0.0.0/24"), 1);
        pm.insert(ip("10.0.0.128/25"), 2);
        assert_eq!(pm.address_count(), Some(expected_count::<P>(24)));
    }

    #[test]
    fn map_address_count_duplicate_prefix<P: Prefix>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("10.0.0.0/24"), 1);
        pm.insert(ip("10.0.0.0/24"), 2);
        assert_eq!(pm.address_count(), Some(expected_count::<P>(24)));
    }

    #[test]
    fn map_address_count_empty<P: Prefix>() {
        let pm = Map::<P>::new();
        assert_eq!(pm.address_count(), Some(0));
    }

    #[test]
    fn map_address_count_full_space<P: Prefix>() {
        // /0 covers the entire address space: 2^num_bits addresses
        let mut pm = Map::<P>::new();
        pm.insert(ip("0.0.0.0/0"), 1);
        if P::num_bits() >= 128 {
            // 2^128 overflows u128
            assert_eq!(pm.address_count(), None);
        } else {
            assert_eq!(pm.address_count(), Some(1u128 << P::num_bits()));
        }
    }

    #[test]
    fn map_address_count_two_halves<P: Prefix>() {
        // Two /1 prefixes cover the full space: 2^(n-1) + 2^(n-1) = 2^n
        let mut pm = Map::<P>::new();
        pm.insert(ip("0.0.0.0/1"), 1);
        pm.insert(ip("128.0.0.0/1"), 2);
        if P::num_bits() >= 128 {
            assert_eq!(pm.address_count(), None);
        } else {
            assert_eq!(pm.address_count(), Some(1u128 << P::num_bits()));
        }
    }

    #[test]
    fn map_address_count_subprefix_inside_supernet<P: Prefix>() {
        // /16 + two /24s inside the /16 → aggregated to just /16
        // 10.0.0.0/16 covers 10.0.0.0 – 10.0.255.255
        let mut pm = Map::<P>::new();
        pm.insert(ip("10.0.0.0/16"), 1);
        pm.insert(ip("10.0.0.0/24"), 2);
        pm.insert(ip("10.0.1.0/24"), 3);
        assert_eq!(pm.address_count(), Some(expected_count::<P>(16)));
    }

    #[test]
    fn map_address_count_mixed_overlapping_and_distinct<P: Prefix>() {
        // /16 (covers 10.0.0.0/24) + a distinct /24
        let mut pm = Map::<P>::new();
        pm.insert(ip("10.0.0.0/16"), 1);
        pm.insert(ip("10.0.0.0/24"), 2); // inside /16
        pm.insert(ip("11.0.0.0/24"), 3); // outside /16
        assert_eq!(
            pm.address_count(),
            Some(expected_count::<P>(16) + expected_count::<P>(24))
        );
    }

    // ── PrefixSet ──────────────────────────────────────────────────────────

    #[test]
    fn set_address_count_single_prefix<P: Prefix + Copy + PartialEq>() {
        let set = PrefixSet::<P>::from_iter([ip("10.0.0.0/24")]);
        assert_eq!(set.address_count(), Some(expected_count::<P>(24)));
    }

    #[test]
    fn set_address_count_overlapping<P: Prefix + Copy + PartialEq>() {
        let set = PrefixSet::<P>::from_iter([ip("10.0.0.0/24"), ip("10.0.0.128/25")]);
        assert_eq!(set.address_count(), Some(expected_count::<P>(24)));
    }

    #[test]
    fn set_address_count_empty<P: Prefix + Copy + PartialEq>() {
        let set = PrefixSet::<P>::new();
        assert_eq!(set.address_count(), Some(0));
    }

    #[test]
    fn set_address_count_full_space<P: Prefix + Copy + PartialEq>() {
        let set = PrefixSet::<P>::from_iter([ip("0.0.0.0/0")]);
        if P::num_bits() >= 128 {
            assert_eq!(set.address_count(), None);
        } else {
            assert_eq!(set.address_count(), Some(1u128 << P::num_bits()));
        }
    }

    #[test]
    fn set_address_count_non_overlapping<P: Prefix + Copy + PartialEq>() {
        let set = PrefixSet::<P>::from_iter([ip("10.0.0.0/24"), ip("10.0.1.0/24")]);
        assert_eq!(set.address_count(), Some(2 * expected_count::<P>(24)));
    }

    #[test]
    fn set_address_count_two_halves<P: Prefix + Copy + PartialEq>() {
        let set = PrefixSet::<P>::from_iter([ip("0.0.0.0/1"), ip("128.0.0.0/1")]);
        if P::num_bits() >= 128 {
            assert_eq!(set.address_count(), None);
        } else {
            assert_eq!(set.address_count(), Some(1u128 << P::num_bits()));
        }
    }

    // ── Instantiations ─────────────────────────────────────────────────────

    #[instantiate_tests(<(u32, u8)>)]
    mod raw32 {}

    #[instantiate_tests(<(u64, u8)>)]
    mod raw64 {}

    #[instantiate_tests(<(u128, u8)>)]
    mod raw128 {}

    #[cfg(feature = "ipnet")]
    #[instantiate_tests(<ipnet::Ipv4Net>)]
    mod ipv4net {}

    #[cfg(feature = "ipnet")]
    #[instantiate_tests(<ipnet::Ipv6Net>)]
    mod ipv6net {}

    #[cfg(feature = "ipnetwork")]
    #[instantiate_tests(<ipnetwork::Ipv4Network>)]
    mod ipv4network {}

    #[cfg(feature = "ipnetwork")]
    #[instantiate_tests(<ipnetwork::Ipv6Network>)]
    mod ipv6network {}

    #[cfg(feature = "cidr")]
    #[instantiate_tests(<cidr::Ipv4Cidr>)]
    mod ipv4cidr {}

    #[cfg(feature = "cidr")]
    #[instantiate_tests(<cidr::Ipv6Cidr>)]
    mod ipv6cidr {}

    #[cfg(feature = "cidr")]
    #[instantiate_tests(<cidr::Ipv4Inet>)]
    mod ipv4inet {}

    #[cfg(feature = "cidr")]
    #[instantiate_tests(<cidr::Ipv6Inet>)]
    mod ipv6inet {}
}

// ── JointPrefixMap tests (ipnet only, not generic) ────────────────────────

#[cfg(feature = "ipnet")]
#[cfg(test)]
mod joint {
    use crate::joint::{JointPrefixMap, JointPrefixSet};

    #[test]
    fn joint_map_address_count_basic() {
        let mut pm: JointPrefixMap<ipnet::IpNet, u32> = JointPrefixMap::new();
        pm.insert("192.0.2.0/24".parse().unwrap(), 1);
        pm.insert("2001:db8::/48".parse().unwrap(), 2);
        let count = pm.address_count();
        assert_eq!(count.0, Some(256));
        assert_eq!(count.1, Some(1u128 << 80));
    }

    #[test]
    fn joint_set_address_count_basic() {
        let mut set: JointPrefixSet<ipnet::IpNet> = JointPrefixSet::new();
        set.insert("192.0.2.0/24".parse().unwrap());
        set.insert("192.0.2.128/25".parse().unwrap());
        set.insert("2001:db8::/48".parse().unwrap());
        assert_eq!(set.address_count(), (Some(256), Some(1u128 << 80)));
    }

    #[test]
    fn joint_map_address_count_empty() {
        let pm: JointPrefixMap<ipnet::IpNet, u32> = JointPrefixMap::new();
        let count = pm.address_count();
        assert_eq!(count.0, Some(0));
        assert_eq!(count.1, Some(0));
    }

    #[test]
    fn joint_map_address_count_full_ipv4_only() {
        let mut pm: JointPrefixMap<ipnet::IpNet, u32> = JointPrefixMap::new();
        pm.insert("0.0.0.0/0".parse().unwrap(), 1);
        let count = pm.address_count();
        // 2^32 fits in u128
        assert_eq!(count.0, Some(1u128 << 32));
        assert_eq!(count.1, Some(0));
    }

    #[test]
    fn joint_map_address_count_full_ipv6_only() {
        let mut pm: JointPrefixMap<ipnet::IpNet, u32> = JointPrefixMap::new();
        pm.insert("::/0".parse().unwrap(), 1);
        let count = pm.address_count();
        assert_eq!(count.0, Some(0));
        assert_eq!(count.1, None); // 2^128 overflows u128
    }

    #[test]
    fn joint_map_address_count_both_full() {
        let mut pm: JointPrefixMap<ipnet::IpNet, u32> = JointPrefixMap::new();
        pm.insert("0.0.0.0/0".parse().unwrap(), 1);
        pm.insert("::/0".parse().unwrap(), 2);
        let count = pm.address_count();
        assert_eq!(count.0, Some(1u128 << 32));
        assert_eq!(count.1, None);
    }

    #[test]
    fn joint_map_address_count_overlapping_v4() {
        let mut pm: JointPrefixMap<ipnet::IpNet, u32> = JointPrefixMap::new();
        pm.insert("192.0.2.0/24".parse().unwrap(), 1);
        pm.insert("192.0.2.128/25".parse().unwrap(), 2);
        pm.insert("198.51.100.0/24".parse().unwrap(), 3);
        let count = pm.address_count();
        assert_eq!(count.0, Some(512));
        assert_eq!(count.1, Some(0));
    }

    #[test]
    fn joint_map_address_count_overlapping_v6() {
        let mut pm: JointPrefixMap<ipnet::IpNet, u32> = JointPrefixMap::new();
        pm.insert("2001:db8::/48".parse().unwrap(), 1);
        pm.insert("2001:db8::/64".parse().unwrap(), 2); // inside /48
        pm.insert("2001:db9::/48".parse().unwrap(), 3); // distinct
        let count = pm.address_count();
        // /48 + /48 = 2 * 2^80
        assert_eq!(count.0, Some(0));
        assert_eq!(count.1, Some(2 * (1u128 << 80)));
    }
}
