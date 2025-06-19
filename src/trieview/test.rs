use crate::*;
use ipnet::Ipv4Net;

#[test]
fn map_view_transformations() {
    let mut map: PrefixMap<Ipv4Net, usize> = PrefixMap::new();
    map.insert("10.0.0.1/8".parse().unwrap(), 1);
    map.insert("10.1.0.2/16".parse().unwrap(), 2);
    map.insert("10.2.0.3/16".parse().unwrap(), 3);

    let elems = map.keys().copied().collect::<Vec<_>>();

    assert_eq!(elems, map.view().keys().copied().collect::<Vec<_>>());
    assert_eq!(elems, map.view().view().keys().copied().collect::<Vec<_>>());
    assert_eq!(
        elems,
        map.view_mut().view().keys().copied().collect::<Vec<_>>()
    );

    let map_ref = &map;
    assert_eq!(elems, map_ref.view().keys().copied().collect::<Vec<_>>());
}

#[test]
fn set_view_transformations() {
    let mut set: PrefixSet<Ipv4Net> = PrefixSet::new();
    set.insert("10.0.0.1/8".parse().unwrap());
    set.insert("10.1.0.2/16".parse().unwrap());
    set.insert("10.2.0.3/16".parse().unwrap());

    let elems = set.iter().copied().collect::<Vec<_>>();

    assert_eq!(elems, set.view().keys().copied().collect::<Vec<_>>());
    assert_eq!(elems, set.view().view().keys().copied().collect::<Vec<_>>());
    assert_eq!(
        elems,
        set.view_mut().view().keys().copied().collect::<Vec<_>>()
    );

    let set_ref = &set;
    assert_eq!(elems, set_ref.view().keys().copied().collect::<Vec<_>>());
}

#[test]
fn debug() {
    let mut map: PrefixMap<Ipv4Net, usize> = PrefixMap::new();
    map.insert("10.0.0.1/8".parse().unwrap(), 1);
    map.insert("10.1.0.2/16".parse().unwrap(), 2);
    map.insert("10.2.0.3/16".parse().unwrap(), 3);

    assert_eq!(format!("{:?}", map.view()), "View(0.0.0.0/0)");
    assert_eq!(
        format!("{:?}", map.view_at("10.0.0.0/8".parse().unwrap()).unwrap()),
        "View(10.0.0.1/8)"
    );

    assert_eq!(format!("{:?}", map.view_mut()), "ViewMut(0.0.0.0/0)");
    assert_eq!(
        format!(
            "{:?}",
            map.view_mut_at("10.0.0.0/8".parse().unwrap()).unwrap()
        ),
        "ViewMut(10.0.0.1/8)"
    );
}

#[test]
fn eq() {
    let mut map1: PrefixMap<Ipv4Net, usize> = PrefixMap::new();
    map1.insert("10.0.0.1/8".parse().unwrap(), 1);
    map1.insert("10.1.0.2/16".parse().unwrap(), 2);
    map1.insert("10.2.0.3/16".parse().unwrap(), 3);

    let mut map2: PrefixMap<Ipv4Net, usize> = PrefixMap::new();
    map2.insert("10.0.0.1/8".parse().unwrap(), 1);
    map2.insert("10.1.0.2/16".parse().unwrap(), 2);
    map2.insert("10.2.0.3/16".parse().unwrap(), 3);

    let mut map3: PrefixMap<Ipv4Net, usize> = PrefixMap::new();
    map3.insert("10.0.0.1/8".parse().unwrap(), 1);
    map3.insert("10.1.0.2/16".parse().unwrap(), 2);
    map3.insert("10.2.0.9/16".parse().unwrap(), 3);

    assert_eq!(map1.view(), map2.view());
    assert_eq!(
        map1.view(),
        map2.view_at("10.0.0.0/8".parse().unwrap()).unwrap()
    );
    assert_ne!(map1.view(), map3.view());

    assert_eq!(map1.view_mut(), map2.view());
    assert_eq!(map1.view_mut(), map2.view_mut());
    assert_eq!(
        map1.view_mut(),
        map2.view_at("10.0.0.0/8".parse().unwrap()).unwrap()
    );
    assert_ne!(map1.view_mut(), map3.view_mut());
}
