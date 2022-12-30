use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    net::Ipv4Addr,
};

use ipnet::Ipv4Net;

use super::map::Node;
use super::*;
use rand::prelude::*;

type Map = PrefixMap<Ipv4Net, u32>;
type Set = PrefixSet<Ipv4Net>;

fn ip(s: &str) -> Ipv4Net {
    s.parse().unwrap()
}

struct TestNode {
    prefix: Ipv4Net,
    value: Option<u32>,
    left: Option<Box<TestNode>>,
    right: Option<Box<TestNode>>,
}

impl TestNode {
    pub fn create(self) -> Map {
        assert_eq!(self.prefix, Default::default());
        let mut map = Map::new();
        self.build(&mut map);
        map
    }

    pub fn build(mut self, map: &mut PrefixMap<Ipv4Net, u32>) -> usize {
        let idx = if self.prefix == Default::default() {
            0
        } else {
            map.table.len()
        };
        map.table.push(Node {
            prefix: self.prefix,
            value: self.value,
            left: None,
            right: None,
        });
        if let Some(left) = self.left.take() {
            let left = left.build(map);
            map.table[idx].left = Some(left);
        }
        if let Some(right) = self.right.take() {
            let right = right.build(map);
            map.table[idx].right = Some(right);
        }
        idx
    }
}

macro_rules! map {
    ($($args:tt),* $(,)?) => {
        _map!($($args),*).create()
    }
}

macro_rules! _map {
    ($ip:literal $(,)?) => {
        TestNode {
            prefix: ip($ip),
            value: None,
            left: None,
            right: None,
        }
    };
    ($ip:literal, $val:literal $(,)?) => {
        TestNode {
            prefix: ip($ip),
            value: Some($val),
            left: None,
            right: None,
        }
    };
    ($ip:literal, (), ($($args:tt),+) $(,)?) => {
        TestNode {
            prefix: ip($ip),
            value: None,
            left: None
            right: Some(Box::new(_map!($($args),+))),
        }
    };
    ($ip:literal, ($($args:tt),+), () $(,)?) => {
        TestNode {
            prefix: ip($ip),
            value: None,
            left: Some(Box::new(_map!($($args),+))),
            right: None
        }
    };
    ($ip:literal, $val:literal, (), ($($args:tt),+) $(,)?) => {
        TestNode {
            prefix: ip($ip),
            value: Some($val),
            left: None,
            right: Some(Box::new(_map!($($args),+))),
        }
    };
    ($ip:literal, $val:literal, ($($args:tt),+), () $(,)?) => {
        TestNode {
            prefix: ip($ip),
            value: Some($val),
            left: Some(Box::new(_map!($($args),+))),
            right: None,
        }
    };
    ($ip:literal, ($($left:tt),+), ($($right:tt),+) $(,)?) => {
        TestNode {
            prefix: ip($ip),
            value: None,
            left: Some(Box::new(_map!($($left),+))),
            right: Some(Box::new(_map!($($right),+))),
        }
    };
    ($ip:literal, $val:literal, ($($left:tt),+), ($($right:tt),+) $(,)?) => {
        TestNode {
            prefix: ip($ip),
            value: Some($val),
            left: Some(Box::new(_map!($($left),+))),
            right: Some(Box::new(_map!($($right),+))),
        }
    };
}

macro_rules! assert_map {
    ($exp:expr, ($($acq:tt),+)) => {
        pretty_assertions::assert_eq!(format!("{:#?}", $exp), format!("{:#?}", map!($($acq),+)))
    };
}

macro_rules! assert_get_exact {
    ($map:expr, $ip:expr, $val:expr) => {
        let map_repr = format!("{:#?}", $map);
        if $val.is_some() {
            assert!(
                $map.contains_key(&ip($ip)),
                "Missing prefix {}\n{}",
                $ip,
                map_repr,
            );
        }
        assert_eq!(
            $map.get(&ip($ip)).cloned(),
            $val,
            "Invalid content for prefix {}\n{}",
            $ip,
            map_repr,
        );
        assert_eq!(
            $map.get_key_value(&ip($ip)).map(|(p, v)| (*p, *v)),
            $val.map(|v| (ip($ip), v)),
            "Invalid content for prefix {}\n{}",
            $ip,
            map_repr,
        );
        assert_eq!(
            $map.get_mut(&ip($ip)).cloned(),
            $val,
            "Invalid content for prefix {}\n{}",
            $ip,
            map_repr,
        );
        if let Some(val) = $val {
            *$map.get_mut(&ip($ip)).unwrap() += 1;
            assert_eq!(
                $map.get_mut(&ip($ip)).cloned(),
                Some(val + 1),
                "Invalid content for prefix {} after increment\n{}",
                $ip,
                map_repr,
            );
            *$map.get_mut(&ip($ip)).unwrap() -= 1;
        }
    };
}

macro_rules! assert_get_lpm {
    ($map:expr, $ip:expr, $lpm:expr, $val:expr) => {
        let map_repr = format!("{:#?}", $map);
        assert_eq!(
            $map.get_lpm_prefix(&ip($ip)).cloned(),
            $val.map(|_| ip($lpm)),
            "Invalid LPM prefix for prefix {}\n{}",
            $ip,
            map_repr,
        );
        assert_eq!(
            $map.get_lpm(&ip($ip)).map(|(p, v)| (*p, *v)),
            $val.map(|v| (ip($lpm), v)),
            "Invalid LPM match for prefix {}\n{}",
            $ip,
            map_repr,
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
        let exp: Vec<(Ipv4Net, u32)> = vec![$((ip($ip), $val)),*];
        assert_iter!($map, exp);
    };
    ($map:expr, $exp:expr) => {
        let own_i: Vec<(Ipv4Net, u32)> = $exp.clone();
        let ref_i: Vec<(&Ipv4Net, &u32)> = own_i.iter().map(|(p, v)| (p, v)).collect();
        let own_p: Vec<Ipv4Net> = $exp.iter().map(|(p, _)| *p).collect();
        let ref_p: Vec<&Ipv4Net> = own_p.iter().collect();
        let own_v: Vec<u32> = $exp.iter().map(|(_, v)| *v).collect();
        let ref_v: Vec<&u32> = own_v.iter().collect();

        let mut duplicate_a = $map.clone();
        let mut duplicate_b = $map.clone();
        let double: Vec<(Ipv4Net, u32)> = $exp.iter().map(|(p, v)| (*p, v * 2)).collect();

        pretty_assertions::assert_eq!($map.iter().collect::<Vec<_>>(), ref_i);
        pretty_assertions::assert_eq!($map.keys().collect::<Vec<_>>(), ref_p);
        pretty_assertions::assert_eq!($map.values().collect::<Vec<_>>(), ref_v);
        pretty_assertions::assert_eq!($map.clone().into_iter().collect::<Vec<_>>(), own_i);
        pretty_assertions::assert_eq!($map.clone().into_keys().collect::<Vec<_>>(), own_p);
        pretty_assertions::assert_eq!($map.clone().into_values().collect::<Vec<_>>(), own_v);

        duplicate_a.iter_mut().for_each(|(_, v)| *v *= 2);
        duplicate_b.values_mut().for_each(|v| *v *= 2);
        pretty_assertions::assert_eq!(duplicate_a.into_iter().collect::<Vec<_>>(), double);
        pretty_assertions::assert_eq!(duplicate_b.into_iter().collect::<Vec<_>>(), double);
    };
}

macro_rules! assert_iter_set {
    ($map:expr) => {
        assert_iter!($map,)
    };
    ($map:expr, $(($ip:literal, $val:literal)),*) => {
        let exp: Vec<(Ipv4Net, u32)> = vec![$((ip($ip), $val)),*];
        assert_iter!($map, exp);
    };
    ($map:expr, $exp:expr) => {
        let own_i: Vec<Ipv4Net> = $exp.clone();
        let ref_i: Vec<&Ipv4Net> = own_i.iter().collect();

        pretty_assertions::assert_eq!($map.iter().collect::<Vec<_>>(), ref_i);
        pretty_assertions::assert_eq!($map.clone().into_iter().collect::<Vec<_>>(), own_i);
    };
}

#[test]
fn child() {
    let mut pm = Map::new();
    pm.insert(ip("1.0.0.0/8"), 1);
    assert_map!(pm, ("0.0.0.0/0", ("1.0.0.0/8", 1), ()));
    assert_iter!(pm, ("1.0.0.0/8", 1));
    assert_get!(pm, "1.0.0.0/8", 1);
}

#[test]
fn chain() {
    let mut pm = Map::new();
    pm.insert(ip("1.0.0.0/8"), 1);
    pm.insert(ip("1.2.0.0/16"), 2);
    pm.insert(ip("1.2.3.0/24"), 3);

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
fn chain_reverse() {
    let mut pm = Map::new();
    pm.insert(ip("1.2.3.0/24"), 3);
    pm.insert(ip("1.2.0.0/16"), 2);
    pm.insert(ip("1.0.0.0/8"), 1);

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
fn branch_direct() {
    let mut pm = Map::new();
    pm.insert(ip("0.0.0.0/7"), 1);
    pm.insert(ip("0.0.0.0/8"), 2);
    pm.insert(ip("1.0.0.0/8"), 3);
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
    assert_map!(
        pm,
        ("0.0.0.0/0", ("0.0.0.0/7", ("0.0.0.0/8"), ("1.0.0.0/8")), ())
    );
    assert_iter!(pm);
}

#[test]
fn branch_indirect() {
    let mut pm = Map::new();
    pm.insert(ip("0.0.0.0/8"), 1);
    pm.insert(ip("1.0.0.0/8"), 2);
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
    assert_iter!(pm);
}

#[test]
fn branch_indirect_child() {
    let mut pm = Map::new();
    pm.insert(ip("0.0.0.0/8"), 1);
    pm.insert(ip("4.0.0.0/8"), 2);
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
    assert_map!(
        pm,
        ("0.0.0.0/0", ("0.0.0.0/5", ("0.0.0.0/8"), ("4.0.0.0/8")), ())
    );
    assert_iter!(pm);
}

#[test]
fn branch_indirect_with_value() {
    let mut pm = Map::new();
    pm.insert(ip("0.0.0.0/8"), 1);
    pm.insert(ip("4.0.0.0/8"), 2);
    pm.insert(ip("0.0.0.0/5"), 3);
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
    assert_map!(
        pm,
        ("0.0.0.0/0", ("0.0.0.0/5", ("0.0.0.0/8"), ("4.0.0.0/8")), ())
    );
    assert_iter!(pm);
}

#[test]
fn branch_indirect_twice() {
    let mut pm = Map::new();
    pm.insert(ip("0.0.0.0/8"), 1);
    pm.insert(ip("4.0.0.0/8"), 2);
    pm.insert(ip("8.0.0.0/8"), 3);
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
fn get_exact() {
    let mut pm = Map::new();
    pm.insert(ip("0.0.0.0/8"), 1);
    pm.insert(ip("4.0.0.0/8"), 2);
    pm.insert(ip("8.0.0.0/8"), 3);
    pm.insert(ip("0.0.0.0/4"), 4);
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
fn get_lpm() {
    let mut pm = Map::new();
    pm.insert(ip("0.0.0.0/8"), 1);
    pm.insert(ip("4.0.0.0/8"), 2);
    pm.insert(ip("8.0.0.0/8"), 3);
    pm.insert(ip("0.0.0.0/4"), 4);
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
fn fuzzing(n: usize) {
    let mut reference = BTreeMap::new();
    let mut pm = Map::new();

    let mut rng = thread_rng();

    for _ in 0..n {
        let prefix = Ipv4Net::new(Ipv4Addr::new(rng.gen(), 0, 0, 0), rng.gen_range(1..=8)).unwrap();
        let prefix = Ipv4Net::new(prefix.mask().into(), prefix.prefix_len()).unwrap();

        if rng.gen_bool(0.7) {
            // insert
            let value: u32 = rng.gen::<u16>() as u32;
            // insert either with entry syntax or with regular insert
            if rng.gen_bool(0.5) {
                let exp = reference.insert(prefix, value);
                let entry = pm.entry(prefix);
                assert_eq!(exp.as_ref(), entry.get());
                match rng.gen_range(1..=3) {
                    1 => {
                        *entry.or_default() = value;
                    }
                    2 => {
                        *entry.or_insert(1) = value;
                    }
                    _ => {
                        *entry.or_insert_with(|| 2) = value;
                    }
                }
            } else {
                // regular syntax
                assert_eq!(reference.insert(prefix, value), pm.insert(prefix, value));
            }
        } else {
            // remove anc compare the result
            assert_eq!(reference.remove(&prefix), pm.remove_keep_tree(&prefix));
        }

        let sorted = reference.iter().map(|(p, v)| (*p, *v)).collect::<Vec<_>>();
        assert_iter!(pm, sorted);

        // select a random prefix and check the iterator of children
        let prefix = Ipv4Net::new(Ipv4Addr::new(rng.gen(), 0, 0, 0), rng.gen_range(1..=6)).unwrap();
        let prefix = Ipv4Net::new(prefix.mask().into(), prefix.prefix_len()).unwrap();
        assert_eq!(
            pm.children(&prefix).collect::<Vec<_>>(),
            reference
                .iter()
                .filter(|(p, _)| prefix.contains(*p))
                .collect::<Vec<_>>()
        );
    }
}

fn fuzzing_check_removal(n: usize) {
    let mut reference = BTreeMap::new();
    let mut pm = Map::new();

    let mut rng = thread_rng();

    for _ in 0..n {
        let prefix = Ipv4Net::new(Ipv4Addr::new(rng.gen(), 0, 0, 0), rng.gen_range(1..=8)).unwrap();
        let prefix = Ipv4Net::new(prefix.mask().into(), prefix.prefix_len()).unwrap();

        if rng.gen_bool(0.7) {
            // insert
            let value: u32 = rng.gen::<u8>() as u32;

            // insert and make sure the result is the same
            assert_eq!(reference.insert(prefix, value), pm.insert(prefix, value));
        } else {
            // remove anc compare the result
            assert_eq!(reference.remove(&prefix), pm.remove(&prefix));

            let acq = format!("{:#?}", pm);
            let exp = format!(
                "{:#?}",
                Map::from_iter(reference.iter().map(|(p, v)| (*p, *v)))
            );
            if exp != acq {
                eprintln!("Error after removing {prefix}");
                pretty_assertions::assert_eq!(acq, exp);
            }
        }

        let sorted = reference.iter().map(|(p, v)| (*p, *v)).collect::<Vec<_>>();

        assert_iter!(pm, sorted);

        // select a random prefix and check the iterator of children
        let prefix = Ipv4Net::new(Ipv4Addr::new(rng.gen(), 0, 0, 0), rng.gen_range(1..=6)).unwrap();
        let prefix = Ipv4Net::new(prefix.mask().into(), prefix.prefix_len()).unwrap();
        assert_eq!(
            pm.children(&prefix).collect::<Vec<_>>(),
            reference
                .iter()
                .filter(|(p, _)| prefix.contains(*p))
                .collect::<Vec<_>>()
        );
    }
}

fn fuzzing_remove_children(n: usize) {
    let mut reference = BTreeMap::new();
    let mut pm = Map::new();

    let mut rng = thread_rng();

    for _ in 0..n {
        let insert = rng.gen_bool(0.9);
        let prefix_len = if insert {
            rng.gen_range(1..=8)
        } else {
            rng.gen_range(0..=5)
        };

        let prefix = Ipv4Net::new(Ipv4Addr::new(rng.gen(), 0, 0, 0), prefix_len).unwrap();
        let prefix = Ipv4Net::new(prefix.mask().into(), prefix.prefix_len()).unwrap();

        if insert {
            let value: u32 = rng.gen::<u8>() as u32;
            assert_eq!(reference.insert(prefix, value), pm.insert(prefix, value));
        } else {
            reference.retain(|p, _| !prefix.contains(p));
            pm.remove_children(&prefix);
        }
        let sorted = reference.iter().map(|(p, v)| (*p, *v)).collect::<Vec<_>>();
        assert_iter!(pm, sorted);

        // select a random prefix and check the iterator of children
        let prefix = Ipv4Net::new(Ipv4Addr::new(rng.gen(), 0, 0, 0), rng.gen_range(1..=6)).unwrap();
        let prefix = Ipv4Net::new(prefix.mask().into(), prefix.prefix_len()).unwrap();
        assert_eq!(
            pm.children(&prefix).collect::<Vec<_>>(),
            reference
                .iter()
                .filter(|(p, _)| prefix.contains(*p))
                .collect::<Vec<_>>()
        );
    }
}

fn fuzzing_set_union(n: usize) {
    let mut ref1 = BTreeSet::new();
    let mut ref2 = BTreeSet::new();
    let mut set1 = Set::new();
    let mut set2 = Set::new();

    let mut rng = thread_rng();

    fn mutate(set: &mut Set, reference: &mut BTreeSet<Ipv4Net>, rng: &mut ThreadRng) {
        let prefix = Ipv4Net::new(Ipv4Addr::new(rng.gen(), 0, 0, 0), rng.gen_range(1..=8)).unwrap();
        let prefix = Ipv4Net::new(prefix.mask().into(), prefix.prefix_len()).unwrap();
        if rng.gen_bool(0.7) {
            // insert either with entry syntax or with regular insert
            assert_eq!(reference.insert(prefix), set.insert(prefix));
        } else {
            // remove anc compare the result
            if rng.gen_bool(0.3) {
                assert_eq!(reference.remove(&prefix), set.remove_keep_tree(&prefix));
            } else {
                assert_eq!(reference.remove(&prefix), set.remove(&prefix));
            }
        }
    }

    for _ in 0..n {
        mutate(&mut set1, &mut ref1, &mut rng);
        mutate(&mut set2, &mut ref2, &mut rng);

        // check
        let sort1 = ref1.iter().copied().collect::<Vec<_>>();
        let sort2 = ref2.iter().copied().collect::<Vec<_>>();
        assert_iter_set!(set1, sort1);
        assert_iter_set!(set2, sort2);

        // check the union
        let ref_union = ref1.union(&ref2).copied().collect::<Vec<_>>();
        let union = set1.union(&set2).copied().collect::<Vec<_>>();
        assert_eq!(union, ref_union, "with\nset1: {set1:?}\nset2: {set2:?}");

        // check the intersection
        let ref_intr = ref1.intersection(&ref2).copied().collect::<Vec<_>>();
        let intr = set1.intersection(&set2).copied().collect::<Vec<_>>();
        assert_eq!(intr, ref_intr, "with\nset1: {set1:?}\nset2: {set2:?}");

        // check the difference
        let ref_diff = ref1.difference(&ref2).copied().collect::<Vec<_>>();
        let diff = set1.difference(&set2).copied().collect::<Vec<_>>();
        assert_eq!(diff, ref_diff, "with\nset1: {set1:?}\nset2: {set2:?}");
    }
}

fn fuzzing_retain(n: usize, m: usize) {
    let mut reference = BTreeMap::new();
    let mut pm = Map::new();

    let mut rng = thread_rng();

    for _ in 0..n {
        // insert m elements
        for _ in 0..m {
            let prefix =
                Ipv4Net::new(Ipv4Addr::new(rng.gen(), 0, 0, 0), rng.gen_range(1..=8)).unwrap();
            let prefix = Ipv4Net::new(prefix.mask().into(), prefix.prefix_len()).unwrap();
            let value: u32 = rng.gen::<u16>() as u32;
            pm.insert(prefix, value);
            reference.insert(prefix, value);
        }

        // retain elements randomly
        let mut choices: HashMap<(Ipv4Net, u32), bool> = HashMap::new();
        pm.retain(|p, v| {
            let choice = rng.gen_bool(0.9);
            choices.insert((*p, *v), choice);
            choice
        });

        reference.retain(|p, v| choices.remove(&(*p, *v)).unwrap());
        assert!(choices.is_empty());

        let sorted = reference.iter().map(|(p, v)| (*p, *v)).collect::<Vec<_>>();
        assert_iter!(pm, sorted);
    }
}

macro_rules! repeat_same {
    ($name:ident, $content:expr, 100) => {
        repeat_same!(
            $name,
            $content,
            00, 01, 02, 03, 04, 05, 06, 07, 08, 09,
            10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
            20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
            30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
            40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
            50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
            60, 61, 62, 63, 64, 65, 66, 67, 68, 69,
            70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
            80, 81, 82, 83, 84, 85, 86, 87, 88, 89,
            90, 91, 92, 93, 94, 95, 96, 97, 98, 99
        );
    };
    ($name:ident, $content:expr, $idx:literal) => {
        paste::paste! {
            #[test]
            fn [<$name _ $idx>]() {
                $content
            }
        }
    };
    ($name:ident, $content:expr, $idx:literal, $($others:literal),*) => {
        repeat_same!($name, $content, $idx);
        repeat_same!($name, $content, $($others),*);
    };
}

repeat_same!(fuzzing_build, fuzzing(500), 100);
repeat_same!(fuzzing_remove, fuzzing_check_removal(500), 100);
repeat_same!(fuzzing_remove_children, fuzzing_remove_children(2000), 100);
repeat_same!(fuzzing_set, fuzzing_set_union(500), 100);
repeat_same!(fuzzing_retain, fuzzing_retain(100, 10), 100);
