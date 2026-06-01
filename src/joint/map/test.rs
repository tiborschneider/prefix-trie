use crate::joint::map::*;
use crate::joint::{JointPrefix, JointPrefixMap};
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
mod entry {
    use super::*;

    #[test]
    fn entry_get<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();
        pm.insert(ip("192.168.1.0/24"), 1);
        assert_eq!(pm.entry(ip("192.168.1.0/24")).get(), Some(&1));
        assert_eq!(pm.entry(ip("192.168.2.0/24")).get(), None);

        pm.insert(ip("2001:1::/32"), 1);
        assert_eq!(pm.entry(ip("2001:1::/32")).get(), Some(&1));
        assert_eq!(pm.entry(ip("2001:2::/32")).get(), None);
    }

    #[test]
    fn entry_get_mut<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();
        pm.insert(ip("192.168.1.0/24"), 1);
        if let Some(x) = pm.entry(ip("192.168.1.0/24")).get_mut() {
            *x += 1
        };
        if let Some(x) = pm.entry(ip("192.168.2.0/24")).get_mut() {
            *x += 1
        };
        assert_eq!(pm.get(&ip("192.168.1.0/24")), Some(&2));
        assert_eq!(pm.get(&ip("192.168.2.0/24")), None);

        pm.insert(ip("2001:1::/48"), 1);
        if let Some(x) = pm.entry(ip("2001:1::/48")).get_mut() {
            *x += 1
        };
        if let Some(x) = pm.entry(ip("2001:2::/48")).get_mut() {
            *x += 1
        };
        assert_eq!(pm.get(&ip("2001:1::/48")), Some(&2));
        assert_eq!(pm.get(&ip("2001:2::/48")), None);
    }

    #[test]
    fn entry_key<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();
        pm.insert(ip("192.168.1.0/24"), 1);
        assert_eq!(pm.entry(ip("192.168.1.0/24")).key(), ip("192.168.1.0/24"));
        assert_eq!(pm.entry(ip("192.168.2.0/24")).key(), ip("192.168.2.0/24"));

        pm.insert(ip("2001:1::/48"), 1);
        assert_eq!(pm.entry(ip("2001:1::/48")).key(), ip("2001:1::/48"));
        assert_eq!(pm.entry(ip("2001:2::/48")).key(), ip("2001:2::/48"));
    }

    #[test]
    fn entry_insert<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();
        pm.insert(ip("192.168.1.0/24"), 1);
        assert_eq!(pm.entry(ip("192.168.1.0/24")).insert(10), Some(1));
        assert_eq!(pm.entry(ip("192.168.2.0/24")).insert(20), None);
        assert_eq!(pm.get(&ip("192.168.1.0/24")), Some(&10));
        assert_eq!(pm.get(&ip("192.168.2.0/24")), Some(&20));

        pm.insert(ip("2001:1::/48"), 1);
        assert_eq!(pm.entry(ip("2001:1::/48")).insert(10), Some(1));
        assert_eq!(pm.entry(ip("2001:2::/48")).insert(20), None);
        assert_eq!(pm.get(&ip("2001:1::/48")), Some(&10));
        assert_eq!(pm.get(&ip("2001:2::/48")), Some(&20));
    }

    #[test]
    fn entry_or_insert<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();

        pm.insert(ip("192.168.1.0/24"), 1);
        assert_eq!(pm.entry(ip("192.168.1.0/24")).or_insert(10), &1);
        assert_eq!(pm.entry(ip("192.168.2.0/24")).or_insert(20), &20);
        assert_eq!(pm.get(&ip("192.168.1.0/24")), Some(&1));
        assert_eq!(pm.get(&ip("192.168.2.0/24")), Some(&20));

        pm.insert(ip("2001:1::/48"), 1);
        assert_eq!(pm.entry(ip("2001:1::/48")).or_insert(10), &1);
        assert_eq!(pm.entry(ip("2001:2::/48")).or_insert(20), &20);
        assert_eq!(pm.get(&ip("2001:1::/48")), Some(&1));
        assert_eq!(pm.get(&ip("2001:2::/48")), Some(&20));
    }

    #[test]
    fn entry_or_insert_with<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();

        pm.insert(ip("192.168.1.0/24"), 1);
        assert_eq!(pm.entry(ip("192.168.1.0/24")).or_insert_with(|| 10), &1);
        assert_eq!(pm.entry(ip("192.168.2.0/24")).or_insert_with(|| 20), &20);
        assert_eq!(pm.get(&ip("192.168.1.0/24")), Some(&1));
        assert_eq!(pm.get(&ip("192.168.2.0/24")), Some(&20));

        pm.insert(ip("2001:1::/48"), 1);
        assert_eq!(pm.entry(ip("2001:1::/48")).or_insert_with(|| 10), &1);
        assert_eq!(pm.entry(ip("2001:2::/48")).or_insert_with(|| 20), &20);
        assert_eq!(pm.get(&ip("2001:1::/48")), Some(&1));
        assert_eq!(pm.get(&ip("2001:2::/48")), Some(&20));
    }

    #[test]
    fn entry_and_modify<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();
        pm.insert(ip("192.168.1.0/24"), 0);
        assert_eq!(
            pm.entry(ip("192.168.1.0/24")).and_modify(|x| *x += 1).get(),
            Some(&1)
        );
        assert_eq!(
            pm.entry(ip("192.168.2.0/24")).and_modify(|x| *x += 1).get(),
            None
        );

        pm.insert(ip("2001:1::/48"), 0);
        assert_eq!(
            pm.entry(ip("2001:1::/48")).and_modify(|x| *x += 1).get(),
            Some(&1)
        );
        assert_eq!(
            pm.entry(ip("2001:2::/48")).and_modify(|x| *x += 1).get(),
            None
        );
    }

    #[test]
    fn entry_or_default<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();

        pm.insert(ip("192.168.1.0/24"), 1);
        assert_eq!(pm.entry(ip("192.168.1.0/24")).or_default(), &1);
        assert_eq!(pm.entry(ip("192.168.2.0/24")).or_default(), &0);
        assert_eq!(pm.get(&ip("192.168.1.0/24")), Some(&1));
        assert_eq!(pm.get(&ip("192.168.2.0/24")), Some(&0));

        pm.insert(ip("2001:1::/48"), 1);
        assert_eq!(pm.entry(ip("2001:1::/48")).or_default(), &1);
        assert_eq!(pm.entry(ip("2001:2::/48")).or_default(), &0);
        assert_eq!(pm.get(&ip("2001:1::/48")), Some(&1));
        assert_eq!(pm.get(&ip("2001:2::/48")), Some(&0));
    }

    #[test]
    fn entry_occupied_key<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();

        pm.insert(ip("192.168.1.0/24"), 1);
        if let Entry::Occupied(e) = pm.entry(ip("192.168.1.1/24")) {
            assert_eq!(e.key(), ip("192.168.1.0/24"))
        }

        pm.insert(ip("2001:1::/48"), 1);
        if let Entry::Occupied(e) = pm.entry(ip("2001:1::1/48")) {
            assert_eq!(e.key(), ip("2001:1::/48"))
        }
    }

    #[test]
    fn entry_occupied_get<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();

        pm.insert(ip("192.168.1.0/24"), 1);
        if let Entry::Occupied(e) = pm.entry(ip("192.168.1.0/24")) {
            assert_eq!(e.get(), &1)
        }

        pm.insert(ip("2001:1::/48"), 1);
        if let Entry::Occupied(e) = pm.entry(ip("2001:1::/48")) {
            assert_eq!(e.get(), &1)
        }
    }

    #[test]
    fn entry_occupied_get_mut<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();

        pm.insert(ip("192.168.1.0/24"), 1);
        if let Entry::Occupied(mut e) = pm.entry(ip("192.168.1.0/24")) {
            *e.get_mut() += 1
        }
        assert_eq!(pm.get(&ip("192.168.1.0/24")), Some(&2));

        pm.insert(ip("2001:1::/48"), 1);
        if let Entry::Occupied(mut e) = pm.entry(ip("2001:1::/48")) {
            *e.get_mut() += 1
        }
        assert_eq!(pm.get(&ip("2001:1::/48")), Some(&2));
    }

    #[test]
    fn entry_occupied_into_mut<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();

        pm.insert(ip("192.168.1.0/24"), 1);
        if let Entry::Occupied(e) = pm.entry(ip("192.168.1.0/24")) {
            *e.into_mut() += 1
        }
        assert_eq!(pm.get(&ip("192.168.1.0/24")), Some(&2));

        pm.insert(ip("2001:1::/48"), 1);
        if let Entry::Occupied(e) = pm.entry(ip("2001:1::/48")) {
            *e.into_mut() += 1
        }
        assert_eq!(pm.get(&ip("2001:1::/48")), Some(&2));
    }

    #[test]
    fn entry_occupied_insert<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();

        pm.insert(ip("192.168.1.0/24"), 1);
        if let Entry::Occupied(e) = pm.entry(ip("192.168.1.0/24")) {
            assert_eq!(e.insert(10), 1)
        }
        assert_eq!(pm.get(&ip("192.168.1.0/24")), Some(&10));

        pm.insert(ip("2001:1::/48"), 1);
        if let Entry::Occupied(e) = pm.entry(ip("2001:1::/48")) {
            assert_eq!(e.insert(10), 1)
        }
        assert_eq!(pm.get(&ip("2001:1::/48")), Some(&10));
    }

    #[test]
    fn entry_occupied_remove<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, i32> = JointPrefixMap::new();

        pm.insert(ip("192.168.1.0/24"), 1);
        if let Entry::Occupied(e) = pm.entry(ip("192.168.1.0/24")) {
            assert_eq!(e.remove(), 1)
        }
        assert_eq!(pm.get(&ip("192.168.1.0/24")), None);

        pm.insert(ip("2001:1::/48"), 1);
        if let Entry::Occupied(e) = pm.entry(ip("2001:1::/48")) {
            assert_eq!(e.remove(), 1)
        }
        assert_eq!(pm.get(&ip("2001:1::/48")), None);
    }

    #[test]
    fn entry_vacant_key<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, i32> = JointPrefixMap::new();

        if let Entry::Vacant(e) = pm.entry(ip("192.168.1.0/24")) {
            assert_eq!(e.key(), ip("192.168.1.0/24"))
        }

        if let Entry::Vacant(e) = pm.entry(ip("2001:1::/48")) {
            assert_eq!(e.key(), ip("2001:1::/48"))
        }
    }

    #[test]
    fn entry_vacant_insert<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, i32> = JointPrefixMap::new();

        if let Entry::Vacant(e) = pm.entry(ip("192.168.1.0/24")) {
            assert_eq!(e.insert(10), &10)
        }
        assert_eq!(pm.get(&ip("192.168.1.0/24")), Some(&10));

        if let Entry::Vacant(e) = pm.entry(ip("2001:1::/48")) {
            assert_eq!(e.insert(10), &10)
        }
        assert_eq!(pm.get(&ip("2001:1::/48")), Some(&10));
    }

    #[test]
    fn entry_vacant_insert_with<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, i32> = JointPrefixMap::new();

        if let Entry::Vacant(e) = pm.entry(ip("192.168.1.0/24")) {
            assert_eq!(e.insert_with(|| 10), &10)
        }
        assert_eq!(pm.get(&ip("192.168.1.0/24")), Some(&10));

        if let Entry::Vacant(e) = pm.entry(ip("2001:1::/48")) {
            assert_eq!(e.insert_with(|| 10), &10)
        }
        assert_eq!(pm.get(&ip("2001:1::/48")), Some(&10));
    }

    #[test]
    fn entry_vacant_default<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, i32> = JointPrefixMap::new();

        if let Entry::Vacant(e) = pm.entry(ip("192.168.1.0/24")) {
            assert_eq!(e.default(), &0)
        }
        assert_eq!(pm.get(&ip("192.168.1.0/24")), Some(&0));

        if let Entry::Vacant(e) = pm.entry(ip("2001:1::/48")) {
            assert_eq!(e.default(), &0)
        }
        assert_eq!(pm.get(&ip("2001:1::/48")), Some(&0));
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
mod iter_from {
    use super::*;
    use crate::joint::JointPrefixSet;

    #[test]
    fn map_inclusive<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();
        pm.insert(ip("10.0.0.0/8"), 1);
        pm.insert(ip("10.1.0.0/16"), 2);
        pm.insert(ip("10.2.0.0/16"), 3);
        pm.insert(ip("2001:1::/32"), 4);
        pm.insert(ip("2001:2::/32"), 5);

        // Inclusive from first yields everything
        let all: Vec<_> = pm.iter_from(&ip("10.0.0.0/8"), true).collect();
        assert_eq!(all, pm.iter().collect::<Vec<_>>());

        // Inclusive from an IPv4 middle entry
        let from: Vec<_> = pm.iter_from(&ip("10.2.0.0/16"), true).collect();
        assert_eq!(
            from,
            vec![
                (ip("10.2.0.0/16"), &3),
                (ip("2001:1::/32"), &4),
                (ip("2001:2::/32"), &5),
            ]
        );

        // Inclusive from an IPv6 entry
        let from: Vec<_> = pm.iter_from(&ip("2001:2::/32"), true).collect();
        assert_eq!(from, vec![(ip("2001:2::/32"), &5)]);
    }

    #[test]
    fn map_exclusive<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();
        pm.insert(ip("10.0.0.0/8"), 1);
        pm.insert(ip("10.1.0.0/16"), 2);
        pm.insert(ip("2001:1::/32"), 3);
        pm.insert(ip("2001:2::/32"), 4);

        // Exclusive from IPv4 entry skips it, continues into IPv6
        let from: Vec<_> = pm.iter_from(&ip("10.1.0.0/16"), false).collect();
        assert_eq!(from, vec![(ip("2001:1::/32"), &3), (ip("2001:2::/32"), &4)]);

        // Exclusive from last IPv6 entry yields nothing
        let from: Vec<_> = pm.iter_from(&ip("2001:2::/32"), false).collect();
        assert!(from.is_empty());

        // Pagination across address families
        let page: Vec<_> = pm.iter_from(&ip("10.0.0.0/8"), false).take(2).collect();
        assert_eq!(page, vec![(ip("10.1.0.0/16"), &2), (ip("2001:1::/32"), &3)]);
    }

    #[test]
    fn map_from_ipv6_skips_ipv4<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();
        pm.insert(ip("10.0.0.0/8"), 1);
        pm.insert(ip("10.1.0.0/16"), 2);
        pm.insert(ip("2001:1::/32"), 3);

        // Starting from an IPv6 prefix skips all IPv4 entries
        let from: Vec<_> = pm.iter_from(&ip("2001:1::/32"), true).collect();
        assert_eq!(from, vec![(ip("2001:1::/32"), &3)]);
    }

    #[test]
    fn map_empty<P: JointPrefix + Debug + PartialEq>() {
        let pm: JointPrefixMap<P, i32> = JointPrefixMap::new();
        let from: Vec<_> = pm.iter_from(&ip("10.0.0.0/8"), true).collect();
        assert!(from.is_empty());
        let from: Vec<_> = pm.iter_from(&ip("2001::/32"), false).collect();
        assert!(from.is_empty());
    }

    #[test]
    fn map_nonexistent<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();
        pm.insert(ip("10.0.0.0/8"), 1);
        pm.insert(ip("10.2.0.0/16"), 2);
        pm.insert(ip("2001:2::/32"), 3);

        // Non-existent IPv4 prefix between entries
        let from: Vec<_> = pm.iter_from(&ip("10.1.0.0/16"), true).collect();
        assert_eq!(from, vec![(ip("10.2.0.0/16"), &2), (ip("2001:2::/32"), &3)]);

        // Non-existent IPv6 prefix before existing one
        let from: Vec<_> = pm.iter_from(&ip("2001:1::/32"), true).collect();
        assert_eq!(from, vec![(ip("2001:2::/32"), &3)]);
    }

    #[test]
    fn map_iter_from_mut<P: JointPrefix + Debug + PartialEq>() {
        let mut pm: JointPrefixMap<P, _> = JointPrefixMap::new();
        pm.insert(ip("10.0.0.0/8"), 1);
        pm.insert(ip("10.1.0.0/16"), 2);
        pm.insert(ip("2001:1::/32"), 3);

        // Mutate entries from 10.1.0.0/16 onwards (crosses address families)
        pm.iter_from_mut(&ip("10.1.0.0/16"), true)
            .for_each(|(_, v)| *v *= 10);
        assert_eq!(pm.get(&ip("10.0.0.0/8")), Some(&1));
        assert_eq!(pm.get(&ip("10.1.0.0/16")), Some(&20));
        assert_eq!(pm.get(&ip("2001:1::/32")), Some(&30));
    }

    #[test]
    fn set_inclusive<P: JointPrefix + Debug + PartialEq>() {
        let mut set: JointPrefixSet<P> = JointPrefixSet::new();
        set.insert(ip("10.0.0.0/8"));
        set.insert(ip("10.1.0.0/16"));
        set.insert(ip("10.2.0.0/16"));
        set.insert(ip("2001:1::/32"));
        set.insert(ip("2001:2::/32"));

        // Inclusive from first yields everything
        let all: Vec<P> = set.iter_from(&ip("10.0.0.0/8"), true).collect();
        assert_eq!(all, set.iter().collect::<Vec<P>>());

        // Inclusive from IPv4 middle entry, continues into IPv6
        let from: Vec<P> = set.iter_from(&ip("10.2.0.0/16"), true).collect();
        assert_eq!(
            from,
            vec![ip("10.2.0.0/16"), ip("2001:1::/32"), ip("2001:2::/32")]
        );

        // Inclusive from IPv6 entry
        let from: Vec<P> = set.iter_from(&ip("2001:2::/32"), true).collect();
        assert_eq!(from, vec![ip::<P>("2001:2::/32")]);
    }

    #[test]
    fn set_exclusive<P: JointPrefix + Debug + PartialEq>() {
        let mut set: JointPrefixSet<P> = JointPrefixSet::new();
        set.insert(ip("10.0.0.0/8"));
        set.insert(ip("10.1.0.0/16"));
        set.insert(ip("2001:1::/32"));
        set.insert(ip("2001:2::/32"));

        // Exclusive from IPv4 entry, continues into IPv6
        let from: Vec<P> = set.iter_from(&ip("10.1.0.0/16"), false).collect();
        assert_eq!(from, vec![ip("2001:1::/32"), ip("2001:2::/32")]);

        // Exclusive from last yields nothing
        let from: Vec<P> = set.iter_from(&ip("2001:2::/32"), false).collect();
        assert!(from.is_empty());

        // Pagination across address families
        let page: Vec<P> = set.iter_from(&ip("10.0.0.0/8"), false).take(2).collect();
        assert_eq!(page, vec![ip("10.1.0.0/16"), ip("2001:1::/32")]);
    }

    #[test]
    fn set_from_ipv6_skips_ipv4<P: JointPrefix + Debug + PartialEq>() {
        let mut set: JointPrefixSet<P> = JointPrefixSet::new();
        set.insert(ip("10.0.0.0/8"));
        set.insert(ip("10.1.0.0/16"));
        set.insert(ip("2001:1::/32"));

        let from: Vec<P> = set.iter_from(&ip("2001:1::/32"), true).collect();
        assert_eq!(from, vec![ip::<P>("2001:1::/32")]);
    }

    #[test]
    fn set_empty<P: JointPrefix + Debug + PartialEq>() {
        let set: JointPrefixSet<P> = JointPrefixSet::new();
        let from: Vec<P> = set.iter_from(&ip("10.0.0.0/8"), true).collect();
        assert!(from.is_empty());
        let from: Vec<P> = set.iter_from(&ip("2001::/32"), false).collect();
        assert!(from.is_empty());
    }

    #[test]
    fn set_nonexistent<P: JointPrefix + Debug + PartialEq>() {
        let mut set: JointPrefixSet<P> = JointPrefixSet::new();
        set.insert(ip("10.0.0.0/8"));
        set.insert(ip("10.2.0.0/16"));
        set.insert(ip("2001:2::/32"));

        // Non-existent IPv4 prefix between entries
        let from: Vec<P> = set.iter_from(&ip("10.1.0.0/16"), true).collect();
        assert_eq!(from, vec![ip("10.2.0.0/16"), ip("2001:2::/32")]);

        // Non-existent IPv6 prefix after all entries
        let from: Vec<P> = set.iter_from(&ip("2002::/32"), true).collect();
        assert!(from.is_empty());
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
