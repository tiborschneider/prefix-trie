use ipnet::Ipv4Net;
use num_traits::NumCast;

use super::*;

type Map<P> = PrefixMap<P, u32>;

fn ip<P: Prefix>(s: &str) -> P {
    let ip: Ipv4Net = s.parse().unwrap();
    let r = ip.addr().to_bits();
    let len = ip.prefix_len();

    let type_len = P::num_bits() as usize;
    assert!(type_len >= 32);

    let r: <P as Prefix>::R = <<P as Prefix>::R as NumCast>::from(r).unwrap() << (type_len - 32);
    P::from_repr_len(r, len)
}

macro_rules! assert_map {
    ($exp:expr, ($($acq:tt),+)) => {
        let _ = &$exp;
    };
}

macro_rules! assert_get_exact {
    ($map:expr, $ip:expr, $val:expr) => {
        if $val.is_some() {
            assert!($map.contains_key(&ip($ip)), "Missing prefix {}", $ip,);
        }
        assert_eq!(
            $map.get(&ip($ip)).cloned(),
            $val,
            "Invalid content for prefix {}",
            $ip,
        );
        assert_eq!(
            $map.get_key_value(&ip($ip)).map(|(p, v)| (p, *v)),
            $val.map(|v| (ip($ip), v)),
            "Invalid content for prefix {}",
            $ip,
        );
        assert_eq!(
            $map.get_mut(&ip($ip)).cloned(),
            $val,
            "Invalid content for prefix {}",
            $ip,
        );
        if let Some(val) = $val {
            *$map.get_mut(&ip($ip)).unwrap() += 1;
            assert_eq!(
                $map.get_mut(&ip($ip)).cloned(),
                Some(val + 1),
                "Invalid content for prefix {} after increment",
                $ip,
            );
            *$map.get_mut(&ip($ip)).unwrap() -= 1;
        }
    };
}

macro_rules! assert_get_lpm {
    ($map:expr, $ip:expr, $lpm:expr, $val:expr) => {
        assert_eq!(
            $map.get_lpm_prefix(&ip($ip)),
            $val.map(|_| ip($lpm)),
            "Invalid LPM prefix for prefix {}",
            $ip,
        );
        assert_eq!(
            $map.get_lpm(&ip($ip)).map(|(p, v)| (p, *v)),
            $val.map(|v| (ip($lpm), v)),
            "Invalid LPM match for prefix {}",
            $ip,
        );
    };
}

macro_rules! assert_get {
    ($map:expr, $ip:literal, $val:literal) => {
        assert_get_exact!($map, $ip, Some($val));
        assert_get_lpm!($map, $ip, $ip, Some($val));
    };
}

macro_rules! assert_remove {
    ($map:expr, $ip:literal, $val:literal) => {
        assert_get!($map, $ip, $val);
        assert_eq!($map.remove_keep_tree(&ip($ip)), Some($val));
        assert_get_exact!($map, $ip, None::<u32>);
    };
}

macro_rules! assert_iter {
    ($map:expr) => {
        assert_iter!($map,)
    };
    ($map:expr, $(($ip:literal, $val:literal)),*) => {
        let exp: Vec<(_, u32)> = vec![$((ip($ip), $val)),*];
        assert_iter!($map, exp);
    };
    ($map:expr, $exp:expr) => {
        let own_i: Vec<(_, u32)> = $exp.clone();
        let own_p: Vec<_> = $exp.iter().map(|(p, _)| *p).collect();
        let own_v: Vec<u32> = $exp.iter().map(|(_, v)| *v).collect();

        let mut duplicate_a = $map.clone();
        let mut duplicate_b = $map.clone();
        let double: Vec<(_, u32)> = $exp.iter().map(|(p, v)| (*p, v * 2)).collect();

        pretty_assertions::assert_eq!(
            $map.iter().map(|(p, v)| (p, *v)).collect::<Vec<_>>(),
            own_i
        );
        pretty_assertions::assert_eq!($map.keys().collect::<Vec<_>>(), own_p);
        pretty_assertions::assert_eq!($map.values().copied().collect::<Vec<_>>(), own_v);
        pretty_assertions::assert_eq!($map.clone().into_iter().collect::<Vec<_>>(), own_i);
        pretty_assertions::assert_eq!($map.clone().into_keys().collect::<Vec<_>>(), own_p);
        pretty_assertions::assert_eq!($map.clone().into_values().collect::<Vec<_>>(), own_v);

        duplicate_a.iter_mut().for_each(|(_, v)| *v *= 2);
        duplicate_b.values_mut().for_each(|v| *v *= 2);
        pretty_assertions::assert_eq!(duplicate_a.into_iter().collect::<Vec<_>>(), double);
        pretty_assertions::assert_eq!(duplicate_b.into_iter().collect::<Vec<_>>(), double);
    };
}

#[generic_tests::define]
mod t {
    use super::*;

    #[test]
    fn child<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("1.0.0.0/8"), 1);
        assert_map!(pm, ("0.0.0.0/0", ("1.0.0.0/8", 1), ()));
        assert_iter!(pm, ("1.0.0.0/8", 1));
        assert_get!(pm, "1.0.0.0/8", 1);
        assert_eq!(pm.len(), 1);
    }

    #[test]
    fn chain<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("1.0.0.0/8"), 1);
        pm.insert(ip("1.2.0.0/16"), 2);
        pm.insert(ip("1.2.3.0/24"), 3);
        assert_eq!(pm.len(), 3);

        assert_map!(
            pm,
            (
                "0.0.0.0/0",
                ("1.0.0.0/8", 1, ("1.2.0.0/16", 2, ("1.2.3.0/24", 3), ()), ()),
                ()
            )
        );

        assert_iter!(pm, ("1.0.0.0/8", 1), ("1.2.0.0/16", 2), ("1.2.3.0/24", 3));

        assert_remove!(pm, "1.0.0.0/8", 1);
        assert_remove!(pm, "1.2.0.0/16", 2);
        assert_remove!(pm, "1.2.3.0/24", 3);

        assert_eq!(pm.len(), 0);

        assert_map!(
            pm,
            (
                "0.0.0.0/0",
                ("1.0.0.0/8", ("1.2.0.0/16", ("1.2.3.0/24"), ()), ()),
                ()
            )
        );

        assert_iter!(pm);
    }

    #[test]
    fn chain_reverse<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("1.2.3.0/24"), 3);
        pm.insert(ip("1.2.0.0/16"), 2);
        pm.insert(ip("1.0.0.0/8"), 1);

        assert_eq!(pm.len(), 3);

        assert_map!(
            pm,
            (
                "0.0.0.0/0",
                ("1.0.0.0/8", 1, ("1.2.0.0/16", 2, ("1.2.3.0/24", 3), ()), ()),
                ()
            )
        );

        assert_iter!(pm, ("1.0.0.0/8", 1), ("1.2.0.0/16", 2), ("1.2.3.0/24", 3));

        assert_remove!(pm, "1.0.0.0/8", 1);
        assert_remove!(pm, "1.2.0.0/16", 2);
        assert_remove!(pm, "1.2.3.0/24", 3);

        assert_eq!(pm.len(), 0);

        assert_map!(
            pm,
            (
                "0.0.0.0/0",
                ("1.0.0.0/8", ("1.2.0.0/16", ("1.2.3.0/24"), ()), ()),
                ()
            )
        );
        assert_iter!(pm);
    }

    #[test]
    fn branch_direct<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("0.0.0.0/7"), 1);
        pm.insert(ip("0.0.0.0/8"), 2);
        pm.insert(ip("1.0.0.0/8"), 3);

        assert_eq!(pm.len(), 3);

        assert_map!(
            pm,
            (
                "0.0.0.0/0",
                ("0.0.0.0/7", 1, ("0.0.0.0/8", 2), ("1.0.0.0/8", 3)),
                ()
            )
        );

        assert_iter!(pm, ("0.0.0.0/7", 1), ("0.0.0.0/8", 2), ("1.0.0.0/8", 3));

        assert_remove!(pm, "0.0.0.0/7", 1);
        assert_remove!(pm, "0.0.0.0/8", 2);
        assert_remove!(pm, "1.0.0.0/8", 3);

        assert_eq!(pm.len(), 0);

        assert_map!(
            pm,
            ("0.0.0.0/0", ("0.0.0.0/7", ("0.0.0.0/8"), ("1.0.0.0/8")), ())
        );
        assert_iter!(pm);
    }

    #[test]
    fn branch_indirect<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("0.0.0.0/8"), 1);
        pm.insert(ip("1.0.0.0/8"), 2);

        assert_eq!(pm.len(), 2);

        assert_map!(
            pm,
            (
                "0.0.0.0/0",
                ("0.0.0.0/7", ("0.0.0.0/8", 1), ("1.0.0.0/8", 2)),
                ()
            )
        );

        assert_iter!(pm, ("0.0.0.0/8", 1), ("1.0.0.0/8", 2));

        assert_remove!(pm, "0.0.0.0/8", 1);
        assert_remove!(pm, "1.0.0.0/8", 2);
        assert_map!(
            pm,
            ("0.0.0.0/0", ("0.0.0.0/7", ("0.0.0.0/8"), ("1.0.0.0/8")), ())
        );
        assert_eq!(pm.len(), 0);
        assert_iter!(pm);
    }

    #[test]
    fn branch_indirect_child<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("0.0.0.0/8"), 1);
        pm.insert(ip("4.0.0.0/8"), 2);
        assert_eq!(pm.len(), 2);
        assert_map!(
            pm,
            (
                "0.0.0.0/0",
                ("0.0.0.0/5", ("0.0.0.0/8", 1), ("4.0.0.0/8", 2)),
                ()
            )
        );

        assert_iter!(pm, ("0.0.0.0/8", 1), ("4.0.0.0/8", 2));

        assert_remove!(pm, "0.0.0.0/8", 1);
        assert_remove!(pm, "4.0.0.0/8", 2);
        assert_eq!(pm.len(), 0);
        assert_map!(
            pm,
            ("0.0.0.0/0", ("0.0.0.0/5", ("0.0.0.0/8"), ("4.0.0.0/8")), ())
        );
        assert_iter!(pm);
    }

    #[test]
    fn branch_indirect_with_value<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("0.0.0.0/8"), 1);
        pm.insert(ip("4.0.0.0/8"), 2);
        pm.insert(ip("0.0.0.0/5"), 3);
        assert_eq!(pm.len(), 3);
        assert_map!(
            pm,
            (
                "0.0.0.0/0",
                ("0.0.0.0/5", 3, ("0.0.0.0/8", 1), ("4.0.0.0/8", 2)),
                ()
            )
        );

        assert_iter!(pm, ("0.0.0.0/5", 3), ("0.0.0.0/8", 1), ("4.0.0.0/8", 2));

        assert_remove!(pm, "0.0.0.0/8", 1);
        assert_remove!(pm, "4.0.0.0/8", 2);
        assert_remove!(pm, "0.0.0.0/5", 3);
        assert_eq!(pm.len(), 0);
        assert_map!(
            pm,
            ("0.0.0.0/0", ("0.0.0.0/5", ("0.0.0.0/8"), ("4.0.0.0/8")), ())
        );
        assert_iter!(pm);
    }

    #[test]
    fn branch_indirect_twice<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("0.0.0.0/8"), 1);
        pm.insert(ip("4.0.0.0/8"), 2);
        pm.insert(ip("8.0.0.0/8"), 3);
        assert_eq!(pm.len(), 3);
        assert_map!(
            pm,
            (
                "0.0.0.0/0",
                (
                    "0.0.0.0/4",
                    ("0.0.0.0/5", ("0.0.0.0/8", 1), ("4.0.0.0/8", 2)),
                    ("8.0.0.0/8", 3)
                ),
                ()
            )
        );

        assert_iter!(pm, ("0.0.0.0/8", 1), ("4.0.0.0/8", 2), ("8.0.0.0/8", 3));

        assert_remove!(pm, "0.0.0.0/8", 1);
        assert_remove!(pm, "4.0.0.0/8", 2);
        assert_remove!(pm, "8.0.0.0/8", 3);
        assert_eq!(pm.len(), 0);
        assert_map!(
            pm,
            (
                "0.0.0.0/0",
                (
                    "0.0.0.0/4",
                    ("0.0.0.0/5", ("0.0.0.0/8"), ("4.0.0.0/8")),
                    ("8.0.0.0/8")
                ),
                ()
            )
        );
        assert_iter!(pm);
    }

    #[test]
    fn get_exact<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("0.0.0.0/8"), 1);
        pm.insert(ip("4.0.0.0/8"), 2);
        pm.insert(ip("8.0.0.0/8"), 3);
        pm.insert(ip("0.0.0.0/4"), 4);
        assert_eq!(pm.len(), 4);
        assert_map!(
            pm,
            (
                "0.0.0.0/0",
                (
                    "0.0.0.0/4",
                    4,
                    ("0.0.0.0/5", ("0.0.0.0/8", 1), ("4.0.0.0/8", 2)),
                    ("8.0.0.0/8", 3)
                ),
                ()
            )
        );
        eprintln!("FOO");

        assert_iter!(
            pm,
            ("0.0.0.0/4", 4),
            ("0.0.0.0/8", 1),
            ("4.0.0.0/8", 2),
            ("8.0.0.0/8", 3)
        );

        assert_get_exact!(pm, "0.0.0.0/0", None::<u32>);
        assert_get_exact!(pm, "0.0.0.0/1", None::<u32>);
        assert_get_exact!(pm, "0.0.0.0/2", None::<u32>);
        assert_get_exact!(pm, "0.0.0.0/3", None::<u32>);
        assert_get_exact!(pm, "0.0.0.0/4", Some(4));
        assert_get_exact!(pm, "0.0.0.0/5", None::<u32>);
        assert_get_exact!(pm, "0.0.0.0/6", None::<u32>);
        assert_get_exact!(pm, "0.0.0.0/7", None::<u32>);
        assert_get_exact!(pm, "0.0.0.0/8", Some(1));
        assert_get_exact!(pm, "0.0.0.0/5", None::<u32>);
        assert_get_exact!(pm, "4.0.0.0/6", None::<u32>);
        assert_get_exact!(pm, "4.0.0.0/7", None::<u32>);
        assert_get_exact!(pm, "4.0.0.0/8", Some(2));
        assert_get_exact!(pm, "8.0.0.0/5", None::<u32>);
        assert_get_exact!(pm, "8.0.0.0/6", None::<u32>);
        assert_get_exact!(pm, "8.0.0.0/7", None::<u32>);
        assert_get_exact!(pm, "8.0.0.0/8", Some(3));
    }

    #[test]
    fn get_lpm<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("0.0.0.0/8"), 1);
        pm.insert(ip("4.0.0.0/8"), 2);
        pm.insert(ip("8.0.0.0/8"), 3);
        pm.insert(ip("0.0.0.0/4"), 4);
        assert_eq!(pm.len(), 4);
        assert_map!(
            pm,
            (
                "0.0.0.0/0",
                (
                    "0.0.0.0/4",
                    4,
                    ("0.0.0.0/5", ("0.0.0.0/8", 1), ("4.0.0.0/8", 2)),
                    ("8.0.0.0/8", 3)
                ),
                ()
            )
        );
        assert_get_lpm!(pm, "0.0.0.0/0", "0.0.0.0/0", None::<u32>);
        assert_get_lpm!(pm, "0.0.0.0/1", "0.0.0.0/0", None::<u32>);
        assert_get_lpm!(pm, "0.0.0.0/2", "0.0.0.0/0", None::<u32>);
        assert_get_lpm!(pm, "0.0.0.0/3", "0.0.0.0/0", None::<u32>);
        assert_get_lpm!(pm, "0.0.0.0/4", "0.0.0.0/4", Some(4));

        assert_get_lpm!(pm, "0.0.0.0/5", "0.0.0.0/4", Some(4));
        assert_get_lpm!(pm, "0.0.0.0/6", "0.0.0.0/4", Some(4));
        assert_get_lpm!(pm, "0.0.0.0/7", "0.0.0.0/4", Some(4));
        assert_get_lpm!(pm, "0.0.0.0/8", "0.0.0.0/8", Some(1));
        assert_get_lpm!(pm, "0.0.0.0/9", "0.0.0.0/8", Some(1));

        assert_get_lpm!(pm, "0.0.0.0/5", "0.0.0.0/4", Some(4));
        assert_get_lpm!(pm, "4.0.0.0/6", "0.0.0.0/4", Some(4));
        assert_get_lpm!(pm, "4.0.0.0/7", "0.0.0.0/4", Some(4));
        assert_get_lpm!(pm, "4.0.0.0/8", "4.0.0.0/8", Some(2));
        assert_get_lpm!(pm, "4.0.0.0/9", "4.0.0.0/8", Some(2));

        assert_get_lpm!(pm, "8.0.0.0/5", "0.0.0.0/4", Some(4));
        assert_get_lpm!(pm, "8.0.0.0/6", "0.0.0.0/4", Some(4));
        assert_get_lpm!(pm, "8.0.0.0/7", "0.0.0.0/4", Some(4));
        assert_get_lpm!(pm, "8.0.0.0/8", "8.0.0.0/8", Some(3));
        assert_get_lpm!(pm, "8.0.0.0/9", "8.0.0.0/8", Some(3));

        assert_get_lpm!(pm, "9.0.0.0/8", "0.0.0.0/4", Some(4));
        assert_get_lpm!(pm, "10.0.0.0/8", "0.0.0.0/4", Some(4));
    }

    #[test]
    fn test_spm_vs_lpm_all_routes<P: Prefix + Copy + PartialEq>() {
        let prefix_set = PrefixSet::<P>::from_iter(vec![
            ip("0.0.0.0/0"),
            ip("192.168.0.0/23"),
            ip("192.168.0.0/24"),
        ]);

        let prefix = ip("192.168.0.1/32");

        assert_eq!(prefix_set.get_spm(&prefix).unwrap(), ip("0.0.0.0/0"));
        assert_eq!(prefix_set.get_lpm(&prefix).unwrap(), ip("192.168.0.0/24"));
    }

    #[test]
    fn insert_with_host_part<P: Prefix + Copy + PartialEq>() {
        let mut set = PrefixSet::<P>::new();
        set.insert(ip("192.168.0.254/24"));
        set.insert(ip("192.168.1.254/24"));
        // Now, we have a branching node at 192.168.0.0/23 with that address.
        set.insert(ip("192.168.0.254/23"));
        // This will not overwrite the address
        assert_eq!(
            Vec::from_iter(set),
            vec![
                ip("192.168.0.0/23"),
                ip("192.168.0.0/24"),
                ip("192.168.1.0/24"),
            ]
        );
    }

    #[test]
    fn replace_with_host_part<P: Prefix + Copy + PartialEq>() {
        let mut set = PrefixSet::<P>::new();
        set.insert(ip("192.168.0.0/24"));
        set.insert(ip("192.168.0.1/24"));
        // This will not overwrite the address
        assert_eq!(Vec::from_iter(set), vec![ip("192.168.0.0/24")]);
    }

    #[test]
    fn entry_with_host_part<P: Prefix + Copy + PartialEq>() {
        let mut set = PrefixMap::<P, _>::new();
        set.insert(ip("192.168.0.254/24"), 1);
        set.insert(ip("192.168.1.254/24"), 2);
        println!("{set:?}");
        // Now, we have a branching node at 192.168.0.0/23 with that address.
        set.entry(ip("192.168.0.254/23")).or_insert(3);
        println!("{set:?}");
        // This will not overwrite the address
        assert_eq!(
            Vec::from_iter(set),
            vec![
                (ip("192.168.0.0/23"), 3),
                (ip("192.168.0.0/24"), 1),
                (ip("192.168.1.0/24"), 2),
            ]
        );
    }

    #[test]
    fn replace_entry_with_host_part<P: Prefix + Copy + PartialEq>() {
        let mut map = PrefixMap::<P, _>::new();
        map.insert(ip("192.168.0.0/24"), 0);
        map.entry(ip("192.168.0.1/24")).insert(0);
        // This will not overwrite the address
        assert_eq!(Vec::from_iter(map), vec![(ip("192.168.0.0/24"), 0)]);
    }

    #[test]
    fn from_iter_with_host_part<P: Prefix + Copy + PartialEq>() {
        let set = PrefixSet::<P>::from_iter([
            ip("192.168.0.254/24"),
            ip("192.168.1.0/24"),
            ip("192.168.0.254/23"),
            ip("192.168.1.254/24"),
        ]);
        assert_eq!(
            Vec::from_iter(set),
            vec![
                ip("192.168.0.0/23"),
                ip("192.168.0.0/24"),
                ip("192.168.1.0/24"),
            ]
        );
    }

    #[test]
    fn regression_free_list_on_parent_collapse<P: Prefix + Copy + PartialEq>() {
        // Regression test for issue #23: Memory leak when removing leaf nodes

        let mut pm = Map::<P>::new();

        // a custom tree to force a valueless branch node
        // root -> branch(10.0.0.0/8) -> [leaf1(10.0.0.0/10), leaf2(10.128.0.0/10)]
        pm.insert(ip("10.0.0.0/10"), 1);
        pm.insert(ip("10.128.0.0/10"), 2);

        // Remove a leaf, which triggers the parent branch to collapse.
        assert_eq!(pm.remove(&ip("10.128.0.0/10")), Some(2));

        // check for memory leaks
        assert!(pm.check_memory_alloc());
    }

    #[test]
    fn iter_from_inclusive<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("10.0.0.0/8"), 1);
        pm.insert(ip("10.1.0.0/16"), 2);
        pm.insert(ip("10.2.0.0/16"), 3);
        pm.insert(ip("10.3.0.0/16"), 4);
        pm.insert(ip("10.4.0.0/16"), 5);

        // Inclusive from the first entry yields everything
        let all: Vec<_> = pm.iter_from(&ip("10.0.0.0/8"), true).collect();
        assert_eq!(all, pm.iter().collect::<Vec<_>>());

        // Inclusive from a middle entry
        let from_mid: Vec<_> = pm.iter_from(&ip("10.2.0.0/16"), true).collect();
        assert_eq!(
            from_mid,
            vec![
                (ip("10.2.0.0/16"), &3),
                (ip("10.3.0.0/16"), &4),
                (ip("10.4.0.0/16"), &5)
            ]
        );

        // Inclusive from the last entry
        let from_last: Vec<_> = pm.iter_from(&ip("10.4.0.0/16"), true).collect();
        assert_eq!(from_last, vec![(ip("10.4.0.0/16"), &5)]);
    }

    #[test]
    fn iter_from_exclusive<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("10.0.0.0/8"), 1);
        pm.insert(ip("10.1.0.0/16"), 2);
        pm.insert(ip("10.2.0.0/16"), 3);
        pm.insert(ip("10.3.0.0/16"), 4);
        pm.insert(ip("10.4.0.0/16"), 5);

        // Exclusive from a middle entry (cursor pagination)
        let after_mid: Vec<_> = pm.iter_from(&ip("10.2.0.0/16"), false).collect();
        assert_eq!(
            after_mid,
            vec![(ip("10.3.0.0/16"), &4), (ip("10.4.0.0/16"), &5)]
        );

        // Exclusive from the last entry yields nothing
        let after_last: Vec<_> = pm.iter_from(&ip("10.4.0.0/16"), false).collect();
        assert!(after_last.is_empty());

        // Exclusive with take for pagination
        let page: Vec<_> = pm.iter_from(&ip("10.1.0.0/16"), false).take(2).collect();
        assert_eq!(page, vec![(ip("10.2.0.0/16"), &3), (ip("10.3.0.0/16"), &4)]);
    }

    #[test]
    fn iter_from_nonexistent<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("10.0.0.0/8"), 1);
        pm.insert(ip("10.2.0.0/16"), 2);
        pm.insert(ip("10.4.0.0/16"), 3);

        // Non-existent prefix between existing entries: starts at the next entry
        let from: Vec<_> = pm.iter_from(&ip("10.1.0.0/16"), true).collect();
        assert_eq!(from, vec![(ip("10.2.0.0/16"), &2), (ip("10.4.0.0/16"), &3)]);

        let from: Vec<_> = pm.iter_from(&ip("10.1.0.0/16"), false).collect();
        assert_eq!(from, vec![(ip("10.2.0.0/16"), &2), (ip("10.4.0.0/16"), &3)]);

        // Non-existent prefix after all entries
        let from: Vec<_> = pm.iter_from(&ip("11.0.0.0/8"), true).collect();
        assert!(from.is_empty());
    }

    #[test]
    fn iter_from_empty_map<P: Prefix + Copy + PartialEq>() {
        let pm = Map::<P>::new();
        let from: Vec<_> = pm.iter_from(&ip("10.0.0.0/8"), true).collect();
        assert!(from.is_empty());
        let from: Vec<_> = pm.iter_from(&ip("10.0.0.0/8"), false).collect();
        assert!(from.is_empty());
    }

    #[test]
    fn iter_from_with_parent_child<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("10.0.0.0/8"), 1);
        pm.insert(ip("10.0.0.0/16"), 2);
        pm.insert(ip("10.0.0.0/24"), 3);
        pm.insert(ip("10.1.0.0/16"), 4);

        // From the parent prefix, inclusive: yields parent and all children
        let from: Vec<_> = pm.iter_from(&ip("10.0.0.0/8"), true).collect();
        assert_eq!(from, pm.iter().collect::<Vec<_>>());

        // From the parent prefix, exclusive: yields only children
        let from: Vec<_> = pm.iter_from(&ip("10.0.0.0/8"), false).collect();
        assert_eq!(
            from,
            vec![
                (ip("10.0.0.0/16"), &2),
                (ip("10.0.0.0/24"), &3),
                (ip("10.1.0.0/16"), &4),
            ]
        );

        // From a child prefix: yields that child and later entries
        let from: Vec<_> = pm.iter_from(&ip("10.0.0.0/16"), false).collect();
        assert_eq!(from, vec![(ip("10.0.0.0/24"), &3), (ip("10.1.0.0/16"), &4)]);
    }

    #[test]
    fn iter_from_set_inclusive<P: Prefix + Copy + PartialEq>() {
        let mut set = PrefixSet::<P>::new();
        set.insert(ip("10.0.0.0/8"));
        set.insert(ip("10.1.0.0/16"));
        set.insert(ip("10.2.0.0/16"));
        set.insert(ip("10.3.0.0/16"));

        // Inclusive from the first entry yields everything
        let all: Vec<P> = set.iter_from(&ip("10.0.0.0/8"), true).collect();
        assert_eq!(all, set.iter().collect::<Vec<_>>());

        // Inclusive from a middle entry
        let from_mid: Vec<P> = set.iter_from(&ip("10.2.0.0/16"), true).collect();
        assert_eq!(from_mid, vec![ip("10.2.0.0/16"), ip("10.3.0.0/16")]);

        // Inclusive from the last entry
        let from_last: Vec<P> = set.iter_from(&ip("10.3.0.0/16"), true).collect();
        assert_eq!(from_last, vec![ip("10.3.0.0/16")]);
    }

    #[test]
    fn iter_from_set_exclusive<P: Prefix + Copy + PartialEq>() {
        let mut set = PrefixSet::<P>::new();
        set.insert(ip("10.0.0.0/8"));
        set.insert(ip("10.1.0.0/16"));
        set.insert(ip("10.2.0.0/16"));
        set.insert(ip("10.3.0.0/16"));

        // Exclusive from a middle entry
        let after_mid: Vec<P> = set.iter_from(&ip("10.1.0.0/16"), false).collect();
        assert_eq!(after_mid, vec![ip("10.2.0.0/16"), ip("10.3.0.0/16")]);

        // Exclusive from the last entry yields nothing
        let after_last: Vec<P> = set.iter_from(&ip("10.3.0.0/16"), false).collect();
        assert!(after_last.is_empty());

        // Exclusive with take for pagination
        let page: Vec<P> = set.iter_from(&ip("10.0.0.0/8"), false).take(2).collect();
        assert_eq!(page, vec![ip("10.1.0.0/16"), ip("10.2.0.0/16")]);
    }

    #[test]
    fn iter_from_set_empty<P: Prefix + Copy + PartialEq>() {
        let set = PrefixSet::<P>::new();
        let from: Vec<P> = set.iter_from(&ip("10.0.0.0/8"), true).collect();
        assert!(from.is_empty());
        let from: Vec<P> = set.iter_from(&ip("10.0.0.0/8"), false).collect();
        assert!(from.is_empty());
    }

    #[test]
    fn iter_from_set_nonexistent<P: Prefix + Copy + PartialEq>() {
        let mut set = PrefixSet::<P>::new();
        set.insert(ip("10.0.0.0/8"));
        set.insert(ip("10.2.0.0/16"));
        set.insert(ip("10.4.0.0/16"));

        // Non-existent prefix between existing entries
        let from: Vec<P> = set.iter_from(&ip("10.1.0.0/16"), true).collect();
        assert_eq!(from, vec![ip("10.2.0.0/16"), ip("10.4.0.0/16")]);

        // Non-existent prefix after all entries
        let from: Vec<P> = set.iter_from(&ip("11.0.0.0/8"), true).collect();
        assert!(from.is_empty());
    }

    #[test]
    fn iter_from_mut_test<P: Prefix + Copy + PartialEq>() {
        let mut pm = Map::<P>::new();
        pm.insert(ip("10.0.0.0/8"), 1);
        pm.insert(ip("10.1.0.0/16"), 2);
        pm.insert(ip("10.2.0.0/16"), 3);

        // Mutate entries from 10.1.0.0/16 onwards
        pm.iter_from_mut(&ip("10.1.0.0/16"), true)
            .for_each(|(_, v)| *v *= 10);
        assert_eq!(pm.get(&ip("10.0.0.0/8")), Some(&1));
        assert_eq!(pm.get(&ip("10.1.0.0/16")), Some(&20));
        assert_eq!(pm.get(&ip("10.2.0.0/16")), Some(&30));
    }

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
