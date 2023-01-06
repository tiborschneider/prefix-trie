use criterion::{criterion_group, criterion_main, Criterion};
use ip_network_table_deps_treebitmap::IpLookupTable;
use ipnet::Ipv4Net;
use prefix_trie::*;
use rand::prelude::*;
use std::net::Ipv4Addr;

fn do_random_inserts() {
    let mut pm = PrefixMap::<Ipv4Net, u32>::new();

    let mut rng = thread_rng();

    for _ in 0..1_000 {
        let addr: u32 = (rng.gen::<u32>()) & 0xfff00000;
        let prefix = Ipv4Net::new(addr.into(), rng.gen_range(1..=12)).unwrap();
        let prefix = Ipv4Net::new(prefix.mask().into(), prefix.prefix_len()).unwrap();

        let value: u32 = rng.gen::<u8>() as u32;
        pm.insert(prefix, value);
    }
}

pub fn random_inserts(c: &mut Criterion) {
    c.bench_function("randomized inserts", |b| b.iter(do_random_inserts));
}

enum Insn {
    Insert(Ipv4Addr, u8, u32),
    Remove(Ipv4Addr, u8),
    ExactMatch(Ipv4Addr, u8),
    LongestPrefixMatch(Ipv4Addr, u8),
}

fn generate_random_mods() -> Vec<Insn> {
    let mut rng = thread_rng();
    let mut result = Vec::new();

    for _ in 0..10_000 {
        let addr: u32 = (rng.gen::<u32>()) & 0xfff00000;
        let addr: Ipv4Addr = addr.into();
        let len = rng.gen_range(1..=12);
        let addr = Ipv4Net::new(addr, len).unwrap().mask().into();

        if rng.gen_bool(0.6) {
            let val = rng.gen::<u32>();
            result.push(Insn::Insert(addr, len, val));
        } else {
            result.push(Insn::Remove(addr, len));
        }
    }
    result
}

fn generate_random_lookups() -> Vec<Insn> {
    let mut rng = thread_rng();
    let mut result = Vec::new();

    for _ in 0..10_000 {
        let addr: u32 = (rng.gen::<u32>()) & 0xfff00000;
        let addr: Ipv4Addr = addr.into();
        let len = rng.gen_range(1..=12);
        let addr = Ipv4Net::new(addr, len).unwrap().mask().into();

        if rng.gen_bool(0.5) {
            result.push(Insn::ExactMatch(addr, len));
        } else {
            result.push(Insn::LongestPrefixMatch(addr, len));
        }
    }
    result
}

fn execute_prefix_map(map: &mut PrefixMap<Ipv4Net, u32>, insns: &Vec<Insn>) {
    for insn in insns {
        criterion::black_box(match insn {
            Insn::Insert(addr, len, val) => map.insert(Ipv4Net::new(*addr, *len).unwrap(), *val),
            Insn::Remove(addr, len) => map.remove(&Ipv4Net::new(*addr, *len).unwrap()),
            Insn::ExactMatch(addr, len) => map.get(&Ipv4Net::new(*addr, *len).unwrap()).copied(),
            Insn::LongestPrefixMatch(addr, len) => map
                .get_lpm(&Ipv4Net::new(*addr, *len).unwrap())
                .map(|(_, x)| *x),
        });
    }
}

fn lookup_prefix_map(map: &PrefixMap<Ipv4Net, u32>, insns: &Vec<Insn>) {
    for insn in insns {
        criterion::black_box(match insn {
            Insn::Insert(_, _, _) => unreachable!(),
            Insn::Remove(_, _) => unreachable!(),
            Insn::ExactMatch(addr, len) => map.get(&Ipv4Net::new(*addr, *len).unwrap()).copied(),
            Insn::LongestPrefixMatch(addr, len) => map
                .get_lpm(&Ipv4Net::new(*addr, *len).unwrap())
                .map(|(_, x)| *x),
        });
    }
}

fn execute_treebitmap(map: &mut IpLookupTable<Ipv4Addr, u32>, insns: &Vec<Insn>) {
    for insn in insns {
        criterion::black_box(match insn {
            Insn::Insert(addr, len, val) => map.insert(*addr, *len as u32, *val),
            Insn::Remove(addr, len) => map.remove(*addr, *len as u32),
            Insn::ExactMatch(addr, len) => map.exact_match(*addr, *len as u32).copied(),
            Insn::LongestPrefixMatch(addr, _) => {
                let mut octets = addr.octets();
                octets[3] += 1;
                let addr = octets.into();
                map.longest_match(addr).map(|(_, _, x)| *x)
            }
        });
    }
}

fn lookup_treebitmap(map: &IpLookupTable<Ipv4Addr, u32>, insns: &Vec<Insn>) {
    for insn in insns {
        criterion::black_box(match insn {
            Insn::Insert(_, _, _) => unreachable!(),
            Insn::Remove(_, _) => unreachable!(),
            Insn::ExactMatch(addr, len) => map.exact_match(*addr, *len as u32).copied(),
            Insn::LongestPrefixMatch(addr, _) => {
                let mut octets = addr.octets();
                octets[3] += 1;
                let addr = octets.into();
                map.longest_match(addr).map(|(_, _, x)| *x)
            }
        });
    }
}

pub fn compare_mods(c: &mut Criterion) {
    let insn = generate_random_mods();
    let mut group = c.benchmark_group("random modifications");

    group.bench_function("PrefixMap", |b| {
        b.iter(|| {
            let mut map = PrefixMap::new();
            execute_prefix_map(&mut map, &insn);
        })
    });
    group.bench_function("TreeBitMap", |b| {
        b.iter(|| {
            let mut map = IpLookupTable::new();
            execute_treebitmap(&mut map, &insn);
        })
    });

    group.finish();
}

pub fn compare_lookup(c: &mut Criterion) {
    let mods = generate_random_mods();
    let lookups = generate_random_lookups();

    let mut prefix_map = PrefixMap::new();
    let mut treebitmap = IpLookupTable::new();
    execute_prefix_map(&mut prefix_map, &mods);
    execute_treebitmap(&mut treebitmap, &mods);

    let mut group = c.benchmark_group("random lookups");

    group.bench_function("PrefixMap", |b| {
        b.iter(|| {
            lookup_prefix_map(&prefix_map, &lookups);
        })
    });
    group.bench_function("TreeBitMap", |b| {
        b.iter(|| {
            lookup_treebitmap(&treebitmap, &lookups);
        })
    });

    group.finish();
}

criterion_group!(benches, random_inserts, compare_lookup, compare_mods);
criterion_main!(benches);
