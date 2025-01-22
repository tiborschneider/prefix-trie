use ipnet::Ipv4Net;

use super::inner::Node;
use super::*;

type Map = PrefixMap<Ipv4Net, u32>;

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
            map.table.as_ref().len()
        };
        map.table.as_mut().push(Node {
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

#[test]
fn child() {
    let mut pm = Map::new();
    pm.insert(ip("1.0.0.0/8"), 1);
    assert_map!(pm, ("0.0.0.0/0", ("1.0.0.0/8", 1), ()));
    assert_iter!(pm, ("1.0.0.0/8", 1));
    assert_get!(pm, "1.0.0.0/8", 1);
    assert_eq!(pm.len(), 1);
}

#[test]
fn chain() {
    let mut pm = Map::new();
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
fn chain_reverse() {
    let mut pm = Map::new();
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
fn branch_direct() {
    let mut pm = Map::new();
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
fn branch_indirect() {
    let mut pm = Map::new();
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
fn branch_indirect_child() {
    let mut pm = Map::new();
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
fn branch_indirect_with_value() {
    let mut pm = Map::new();
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
fn branch_indirect_twice() {
    let mut pm = Map::new();
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
fn get_exact() {
    let mut pm = Map::new();
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
fn test_spm_vs_lpm_all_routes() {
    use std::str::FromStr;

    let prefix_set = PrefixSet::from_iter(vec![
        Ipv4Net::from_str("0.0.0.0/0").unwrap(),
        Ipv4Net::from_str("192.168.0.0/23").unwrap(),
        Ipv4Net::from_str("192.168.0.0/24").unwrap(),
    ]);

    let prefix = Ipv4Net::from_str("192.168.0.1/32").unwrap();

    assert_eq!(
        prefix_set.get_spm(&prefix).unwrap(),
        &Ipv4Net::from_str("0.0.0.0/0").unwrap()
    );
    assert_eq!(
        prefix_set.get_lpm(&prefix).unwrap(),
        &Ipv4Net::from_str("192.168.0.0/24").unwrap()
    );
}
