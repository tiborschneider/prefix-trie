use criterion::{criterion_group, criterion_main, Criterion};
use ip_network_table_deps_treebitmap::IpLookupTable;
use ipnet::Ipv4Net;
use prefix_trie::*;
use rand::prelude::*;
use std::collections::HashSet;
use std::net::Ipv4Addr;

const SPARSE_MASK: u32 = 0xffffffff;
const DENSE_MASK: u32 = 0x00000fff;
const ITERS: usize = 10_000;

enum Insn {
    Insert(Ipv4Addr, u8, u32),
    Remove(Ipv4Addr, u8),
    ExactMatch(Ipv4Addr, u8),
    LongestPrefixMatch(Ipv4Addr, u8),
}

fn min_prefix_len(addr: u32) -> u8 {
    let mut bit: u32 = 0x00000001;
    let mut len: u8 = 32;
    while len > 0 && bit & addr == 0 {
        len = len.saturating_sub(1);
        (bit, _) = bit.overflowing_shl(1);
    }
    len
}

fn random_addr(mask: u32, rng: &mut ThreadRng) -> (Ipv4Addr, u8) {
    let addr: u32 = rng.gen::<u32>() & mask;
    let max_len = min_prefix_len(mask);
    let min_len = min_prefix_len(addr);
    let len = rng.gen_range(min_len..=max_len);
    (addr.into(), len)
}

fn generate_random_mods(mask: u32) -> (Vec<Insn>, HashSet<(Ipv4Addr, u8)>) {
    let mut rng = thread_rng();
    let mut result = Vec::new();

    let mut addresses = HashSet::new();

    for _ in 0..ITERS {
        if addresses.is_empty() || rng.gen_bool(0.8) {
            let (addr, len) = random_addr(mask, &mut rng);
            let val = rng.gen::<u32>();
            result.push(Insn::Insert(addr, len, val));
            addresses.insert((addr, len));
        } else {
            let (addr, len) = addresses
                .iter()
                .choose(&mut rng)
                .map(|(addr, len)| (*addr, *len))
                .unwrap();
            addresses.remove(&(addr, len));
            result.push(Insn::Remove(addr, len));
        }
    }
    (result, addresses)
}

fn generate_random_lookups(mask: u32, addresses: &HashSet<(Ipv4Addr, u8)>) -> Vec<Insn> {
    let mut rng = thread_rng();
    let mut result = Vec::new();

    for _ in 0..ITERS {
        if rng.gen_bool(0.5) {
            let (addr, len) = if addresses.is_empty() || rng.gen_bool(0.5) {
                random_addr(mask, &mut rng)
            } else {
                addresses
                    .iter()
                    .choose(&mut rng)
                    .map(|(addr, len)| (*addr, *len))
                    .unwrap()
            };
            result.push(Insn::ExactMatch(addr, len));
        } else {
            let (addr, len) = random_addr(mask, &mut rng);
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
    let mut group = c.benchmark_group("random modifications");

    let (insn_dense, _) = generate_random_mods(DENSE_MASK);
    let (insn_sparse, _) = generate_random_mods(SPARSE_MASK);

    group.bench_function("PrefixMap dense", |b| {
        b.iter(|| {
            let mut map = PrefixMap::new();
            execute_prefix_map(&mut map, &insn_dense);
        })
    });
    group.bench_function("TreeBitMap dense", |b| {
        b.iter(|| {
            let mut map = IpLookupTable::new();
            execute_treebitmap(&mut map, &insn_dense);
        })
    });
    group.bench_function("PrefixMap sparse", |b| {
        b.iter(|| {
            let mut map = PrefixMap::new();
            execute_prefix_map(&mut map, &insn_sparse);
        })
    });
    group.bench_function("TreeBitMap sparse", |b| {
        b.iter(|| {
            let mut map = IpLookupTable::new();
            execute_treebitmap(&mut map, &insn_sparse);
        })
    });

    group.finish();
}

pub fn compare_lookup(c: &mut Criterion) {
    let (mods_dense, addrs) = generate_random_mods(DENSE_MASK);
    let lookups_dense = generate_random_lookups(DENSE_MASK, &addrs);
    let (mods_sparse, addrs) = generate_random_mods(SPARSE_MASK);
    let lookups_sparse = generate_random_lookups(SPARSE_MASK, &addrs);

    let mut prefix_map_dense = PrefixMap::new();
    let mut treebitmap_dense = IpLookupTable::new();
    let mut prefix_map_sparse = PrefixMap::new();
    let mut treebitmap_sparse = IpLookupTable::new();
    execute_prefix_map(&mut prefix_map_dense, &mods_dense);
    execute_treebitmap(&mut treebitmap_dense, &mods_dense);
    execute_prefix_map(&mut prefix_map_sparse, &mods_sparse);
    execute_treebitmap(&mut treebitmap_sparse, &mods_sparse);

    let mut group = c.benchmark_group("random lookups");

    group.bench_function("PrefixMap dense", |b| {
        b.iter(|| {
            lookup_prefix_map(&prefix_map_dense, &lookups_dense);
        })
    });
    group.bench_function("TreeBitMap dense", |b| {
        b.iter(|| {
            lookup_treebitmap(&treebitmap_dense, &lookups_dense);
        })
    });
    group.bench_function("PrefixMap sparse", |b| {
        b.iter(|| {
            lookup_prefix_map(&prefix_map_sparse, &lookups_sparse);
        })
    });
    group.bench_function("TreeBitMap sparse", |b| {
        b.iter(|| {
            lookup_treebitmap(&treebitmap_sparse, &lookups_sparse);
        })
    });

    group.finish();
}

pub fn compare_mods_sparse(c: &mut Criterion) {
    let (insn, _) = generate_random_mods(SPARSE_MASK);
    let mut group = c.benchmark_group("random sparse modifications");

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

pub fn compare_lookup_sparse(c: &mut Criterion) {
    let (mods, addrs) = generate_random_mods(SPARSE_MASK);
    let lookups = generate_random_lookups(SPARSE_MASK, &addrs);

    let mut prefix_map = PrefixMap::new();
    let mut treebitmap = IpLookupTable::new();
    execute_prefix_map(&mut prefix_map, &mods);
    execute_treebitmap(&mut treebitmap, &mods);

    let mut group = c.benchmark_group("random sparse lookups");

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

criterion_group!(benches, compare_lookup, compare_mods);
criterion_main!(benches);
