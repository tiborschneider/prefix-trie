use crate::joint::map::*;
use crate::joint::{JointPrefix, JointPrefixMap};
use crate::*;
use ipnet::{Ipv4Net, Ipv6Net};
use num_traits::{NumCast, PrimInt};
use std::fmt::Debug;

fn ipv4<P: Prefix>(s: &str) -> P {
    let ip: Ipv4Net = s.parse().unwrap();
    let r = ip.addr().to_bits();
    let len = ip.prefix_len();

    let type_len = P::zero().repr().count_zeros() as usize;
    assert!(type_len == 32);

    let r: <P as Prefix>::R = <<P as Prefix>::R as NumCast>::from(r).unwrap();
    P::from_repr_len(r, len)
}

fn ipv6<P: Prefix>(s: &str) -> P {
    let ip: Ipv6Net = s.parse().unwrap();
    let r = ip.addr().to_bits();
    let len = ip.prefix_len();

    let type_len = P::zero().repr().count_zeros() as usize;
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
        if let Entry::Occupied(mut e) = pm.entry(ip("192.168.1.0/24")) {
            assert_eq!(e.remove(), 1)
        }
        assert_eq!(pm.get(&ip("192.168.1.0/24")), None);

        pm.insert(ip("2001:1::/48"), 1);
        if let Entry::Occupied(mut e) = pm.entry(ip("2001:1::/48")) {
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
