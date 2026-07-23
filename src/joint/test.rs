use crate::joint::{JointPrefix, JointPrefixMap, JointPrefixSet};
use crate::*;
use ipnet::{Ipv4Net, Ipv6Net};
use num_traits::NumCast;
use std::fmt::Debug;

fn ipv4<P: Prefix>(s: &str) -> P {
    let ip: Ipv4Net = s.parse().unwrap();
    let r = ip.addr().to_bits();
    let len = ip.prefix_len();

    let type_len = P::num_bits() as usize;
    assert!(type_len == 32);

    let r: <P as Prefix>::R = <<P as Prefix>::R as NumCast>::from(r).unwrap();
    P::from_repr_len(r, len)
}

fn ipv6<P: Prefix>(s: &str) -> P {
    let ip: Ipv6Net = s.parse().unwrap();
    let r = ip.addr().to_bits();
    let len = ip.prefix_len();

    let type_len = P::num_bits() as usize;
    assert!(type_len == 128);

    let r: <P as Prefix>::R = <<P as Prefix>::R as NumCast>::from(r).unwrap();
    P::from_repr_len(r, len)
}

fn ip<P: JointPrefix + Debug + PartialEq>(s: &str) -> P {
    if s.contains(":") {
        P::from_p2(&ipv6(s))
    } else {
        P::from_p1(&ipv4(s))
    }
}

#[generic_tests::define]
mod set {
    use super::*;

    #[test]
    fn iter<P: JointPrefix + Debug + PartialEq>() {
        let mut set: JointPrefixSet<P> = JointPrefixSet::new();
        set.insert(ip("192.168.1.0/24"));
        set.insert(ip("192.168.0.0/24"));
        set.insert(ip("2001::1:0:0/96"));
        assert_eq!(
            set.iter().collect::<Vec<_>>(),
            vec![
                ip("192.168.0.0/24"),
                ip("192.168.1.0/24"),
                ip("2001::1:0:0/96")
            ],
        );
    }

    #[test]
    fn into_iter<P: JointPrefix + Debug + PartialEq>() {
        let mut set: JointPrefixSet<P> = JointPrefixSet::new();
        set.insert(ip("192.168.1.0/24"));
        set.insert(ip("192.168.0.0/24"));
        set.insert(ip("2001::1:0:0/96"));
        assert_eq!(
            set.into_iter().collect::<Vec<_>>(),
            vec![
                ip("192.168.0.0/24"),
                ip("192.168.1.0/24"),
                ip("2001::1:0:0/96")
            ],
        );
    }

    #[test]
    fn children<P: JointPrefix + Debug + PartialEq>() {
        let mut set: JointPrefixSet<P> = JointPrefixSet::new();
        set.insert(ip("192.168.0.0/22"));
        set.insert(ip("192.168.0.0/23"));
        set.insert(ip("192.168.2.0/23"));
        set.insert(ip("192.168.0.0/24"));
        set.insert(ip("192.168.2.0/24"));
        assert_eq!(
            set.children(&ip("192.168.0.0/23")).collect::<Vec<_>>(),
            vec![ip("192.168.0.0/23"), ip("192.168.0.0/24"),]
        );

        set.insert(ip("2001:0::/30"));
        set.insert(ip("2001:0::/31"));
        set.insert(ip("2001:2::/31"));
        set.insert(ip("2001:0::/32"));
        set.insert(ip("2001:2::/32"));
        assert_eq!(
            set.children(&ip("2001:0::/31")).collect::<Vec<_>>(),
            vec![ip("2001:0::/31"), ip("2001:0::/32"),]
        );
    }

    #[test]
    fn cover<P: JointPrefix + Debug + PartialEq>() {
        let mut set: JointPrefixSet<P> = JointPrefixSet::new();
        set.insert(ip("192.168.0.0/22"));
        set.insert(ip("192.168.0.0/23"));
        set.insert(ip("192.168.2.0/23"));
        set.insert(ip("192.168.0.0/24"));
        set.insert(ip("192.168.2.0/24"));
        assert_eq!(
            set.cover(&ip("192.168.2.0/24")).collect::<Vec<_>>(),
            vec![
                ip("192.168.0.0/22"),
                ip("192.168.2.0/23"),
                ip("192.168.2.0/24"),
            ]
        );

        set.insert(ip("2001:0::/30"));
        set.insert(ip("2001:0::/31"));
        set.insert(ip("2001:2::/31"));
        set.insert(ip("2001:0::/32"));
        set.insert(ip("2001:2::/32"));
        assert_eq!(
            set.cover(&ip("2001:2::/32")).collect::<Vec<_>>(),
            vec![ip("2001:0::/30"), ip("2001:2::/31"), ip("2001:2::/32"),]
        );
    }

    #[test]
    fn is_covered_in_aggregate_tiles_siblings<P: JointPrefix + Debug + PartialEq>() {
        // No single member covers the parent, but the two halves tile its entire range.
        let mut set: JointPrefixSet<P> = JointPrefixSet::new();
        set.insert(ip("10.0.0.0/9"));
        set.insert(ip("10.128.0.0/9"));
        assert!(!set.is_covered(&ip("10.0.0.0/8")));
        assert!(set.is_covered_in_aggregate(&ip("10.0.0.0/8")));

        set.insert(ip("2001:db8::/33"));
        set.insert(ip("2001:db8:8000::/33"));
        assert!(!set.is_covered(&ip("2001:db8::/32")));
        assert!(set.is_covered_in_aggregate(&ip("2001:db8::/32")));
    }

    #[test]
    fn is_covered_in_aggregate_partial_tiling_is_false<P: JointPrefix + Debug + PartialEq>() {
        // Only one half of the parent is present; its range is not fully covered either way.
        let mut set: JointPrefixSet<P> = JointPrefixSet::new();
        set.insert(ip("10.0.0.0/9"));
        assert!(!set.is_covered(&ip("10.0.0.0/8")));
        assert!(!set.is_covered_in_aggregate(&ip("10.0.0.0/8")));

        set.insert(ip("2001:db8::/33"));
        assert!(!set.is_covered(&ip("2001:db8::/32")));
        assert!(!set.is_covered_in_aggregate(&ip("2001:db8::/32")));
    }

    #[test]
    fn is_covered_in_aggregate_matches_is_covered_for_ancestor_member<
        P: JointPrefix + Debug + PartialEq,
    >() {
        // A direct covering ancestor member is caught by both, no tiling needed.
        let mut set: JointPrefixSet<P> = JointPrefixSet::new();
        set.insert(ip("10.0.0.0/8"));
        assert!(set.is_covered(&ip("10.1.2.0/24")));
        assert!(set.is_covered_in_aggregate(&ip("10.1.2.0/24")));

        set.insert(ip("2001:db8::/32"));
        assert!(set.is_covered(&ip("2001:db8:1::/48")));
        assert!(set.is_covered_in_aggregate(&ip("2001:db8:1::/48")));
    }

    #[instantiate_tests(<::either::Either<(u32, u8), (u128, u8)>>)]
    mod either {}

    #[cfg(feature = "ipnet")]
    #[instantiate_tests(<::ipnet::IpNet>)]
    mod ipnet {}

    #[cfg(feature = "ipnetwork")]
    #[instantiate_tests(<::ipnetwork::IpNetwork>)]
    mod ipnetwork {}

    #[cfg(feature = "cidr")]
    #[instantiate_tests(<::cidr::IpCidr>)]
    mod cidr {}
}

#[generic_tests::define]
mod map {
    use super::*;

    #[test]
    fn iter<P: JointPrefix + Debug + PartialEq>() {
        let mut map: JointPrefixMap<P, usize> = JointPrefixMap::new();
        map.insert(ip("192.168.1.0/24"), 0);
        map.insert(ip("192.168.0.0/24"), 1);
        map.insert(ip("2001::1:0:0/96"), 2);
        assert_eq!(
            map.iter().collect::<Vec<_>>(),
            vec![
                (ip("192.168.0.0/24"), &1),
                (ip("192.168.1.0/24"), &0),
                (ip("2001::1:0:0/96"), &2)
            ],
        );
    }

    #[test]
    fn into_iter<P: JointPrefix + Debug + PartialEq>() {
        let mut map: JointPrefixMap<P, usize> = JointPrefixMap::new();
        map.insert(ip("192.168.1.0/24"), 0);
        map.insert(ip("192.168.0.0/24"), 1);
        map.insert(ip("2001::1:0:0/96"), 2);
        assert_eq!(
            map.into_iter().collect::<Vec<_>>(),
            vec![
                (ip("192.168.0.0/24"), 1),
                (ip("192.168.1.0/24"), 0),
                (ip("2001::1:0:0/96"), 2)
            ],
        );
    }

    #[test]
    fn children<P: JointPrefix + Debug + PartialEq>() {
        let mut map: JointPrefixMap<P, usize> = JointPrefixMap::new();
        map.insert(ip("192.168.0.0/22"), 0);
        map.insert(ip("192.168.0.0/23"), 1);
        map.insert(ip("192.168.2.0/23"), 2);
        map.insert(ip("192.168.0.0/24"), 3);
        map.insert(ip("192.168.2.0/24"), 4);
        assert_eq!(
            map.children(&ip("192.168.0.0/23")).collect::<Vec<_>>(),
            vec![(ip("192.168.0.0/23"), &1), (ip("192.168.0.0/24"), &3)]
        );

        map.insert(ip("2001:0::/30"), 0);
        map.insert(ip("2001:0::/31"), 1);
        map.insert(ip("2001:2::/31"), 2);
        map.insert(ip("2001:0::/32"), 3);
        map.insert(ip("2001:2::/32"), 4);
        assert_eq!(
            map.children(&ip("2001:0::/31")).collect::<Vec<_>>(),
            vec![(ip("2001:0::/31"), &1), (ip("2001:0::/32"), &3)]
        );
    }

    #[test]
    fn cover<P: JointPrefix + Debug + PartialEq>() {
        let mut map: JointPrefixMap<P, usize> = JointPrefixMap::new();
        map.insert(ip("192.168.0.0/22"), 0);
        map.insert(ip("192.168.0.0/23"), 1);
        map.insert(ip("192.168.2.0/23"), 2);
        map.insert(ip("192.168.0.0/24"), 3);
        map.insert(ip("192.168.2.0/24"), 4);
        assert_eq!(
            map.cover(&ip("192.168.2.0/24")).collect::<Vec<_>>(),
            vec![
                (ip("192.168.0.0/22"), &0),
                (ip("192.168.2.0/23"), &2),
                (ip("192.168.2.0/24"), &4),
            ]
        );

        map.insert(ip("2001:0::/30"), 0);
        map.insert(ip("2001:0::/31"), 1);
        map.insert(ip("2001:2::/31"), 2);
        map.insert(ip("2001:0::/32"), 3);
        map.insert(ip("2001:2::/32"), 4);
        assert_eq!(
            map.cover(&ip("2001:2::/32")).collect::<Vec<_>>(),
            vec![
                (ip("2001:0::/30"), &0),
                (ip("2001:2::/31"), &2),
                (ip("2001:2::/32"), &4)
            ]
        );
    }

    #[test]
    fn is_covered_in_aggregate_tiles_siblings_regardless_of_value<
        P: JointPrefix + Debug + PartialEq,
    >() {
        // No single entry covers the parent, but the two halves tile its entire range. Coverage
        // only tracks which addresses are present, not whether the values agree.
        let mut map: JointPrefixMap<P, usize> = JointPrefixMap::new();
        map.insert(ip("10.0.0.0/9"), 1);
        map.insert(ip("10.128.0.0/9"), 2);
        assert!(!map.is_covered(&ip("10.0.0.0/8")));
        assert!(map.is_covered_in_aggregate(&ip("10.0.0.0/8")));

        map.insert(ip("2001:db8::/33"), 3);
        map.insert(ip("2001:db8:8000::/33"), 4);
        assert!(!map.is_covered(&ip("2001:db8::/32")));
        assert!(map.is_covered_in_aggregate(&ip("2001:db8::/32")));
    }

    #[test]
    fn is_covered_in_aggregate_partial_tiling_is_false<P: JointPrefix + Debug + PartialEq>() {
        // Only one half of the parent is present; its range is not fully covered either way.
        let mut map: JointPrefixMap<P, usize> = JointPrefixMap::new();
        map.insert(ip("10.0.0.0/9"), 1);
        assert!(!map.is_covered(&ip("10.0.0.0/8")));
        assert!(!map.is_covered_in_aggregate(&ip("10.0.0.0/8")));

        map.insert(ip("2001:db8::/33"), 3);
        assert!(!map.is_covered(&ip("2001:db8::/32")));
        assert!(!map.is_covered_in_aggregate(&ip("2001:db8::/32")));
    }

    #[test]
    fn is_covered_in_aggregate_matches_is_covered_for_ancestor_member<
        P: JointPrefix + Debug + PartialEq,
    >() {
        // A direct covering ancestor entry is caught by both, no tiling needed.
        let mut map: JointPrefixMap<P, usize> = JointPrefixMap::new();
        map.insert(ip("10.0.0.0/8"), 1);
        assert!(map.is_covered(&ip("10.1.2.0/24")));
        assert!(map.is_covered_in_aggregate(&ip("10.1.2.0/24")));

        map.insert(ip("2001:db8::/32"), 2);
        assert!(map.is_covered(&ip("2001:db8:1::/48")));
        assert!(map.is_covered_in_aggregate(&ip("2001:db8:1::/48")));
    }

    #[instantiate_tests(<::either::Either<(u32, u8), (u128, u8)>>)]
    mod either {}

    #[cfg(feature = "ipnet")]
    #[instantiate_tests(<::ipnet::IpNet>)]
    mod ipnet {}

    #[cfg(feature = "ipnetwork")]
    #[instantiate_tests(<::ipnetwork::IpNetwork>)]
    mod ipnetwork {}

    #[cfg(feature = "cidr")]
    #[instantiate_tests(<::cidr::IpCidr>)]
    mod cidr {}
}
