#![allow(dead_code)]
#![allow(clippy::incompatible_msrv)]

use ip_network_table_deps_treebitmap::IpLookupTable;
use ipnet::Ipv4Net;
use prefix_trie::*;
use rand::prelude::*;
use std::collections::HashSet;
use std::io::Read;
use std::net::Ipv4Addr;

pub enum Insn {
    Insert(Ipv4Addr, u8, u32),
    Remove(Ipv4Addr, u8),
    ExactMatch(Ipv4Addr, u8),
    LongestPrefixMatch(Ipv4Addr, u8),
}

pub fn random_addr(rng: &mut StdRng) -> (Ipv4Addr, u8) {
    let addr: Ipv4Addr = rng.gen::<u32>().into();
    let max_len = 24;
    let min_len = 8;
    let len = rng.gen_range(min_len..max_len);
    let net = Ipv4Net::new(addr, len).unwrap().trunc();
    (net.addr(), net.prefix_len())
}

pub fn bgp_ipv4_prefixes() -> Vec<(Ipv4Addr, u8)> {
    let compressed = include_bytes!("prefixes.txt.gz");
    let mut decoder = flate2::read::GzDecoder::new(&compressed[..]);
    let mut decompressed = Vec::new();
    decoder.read_to_end(&mut decompressed).unwrap();
    str::from_utf8(&decompressed)
        .unwrap()
        .lines()
        .filter_map(|x| x.parse::<Ipv4Net>().ok())
        .map(|net| (net.addr(), net.prefix_len()))
        .collect()
}

pub fn generate_random_mods_dense(seed: u64, iter: usize) -> (Vec<Insn>, HashSet<(Ipv4Addr, u8)>) {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut result = Vec::new();

    let mut addresses = HashSet::new();

    for _ in 0..iter {
        if addresses.is_empty() || rng.gen_bool(0.8) {
            let (addr, len) = random_addr(&mut rng);
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

pub fn generate_random_lookups_dense(
    seed: u64,
    iter: usize,
    addresses: &HashSet<(Ipv4Addr, u8)>,
) -> Vec<Insn> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut result = Vec::new();

    for _ in 0..iter {
        if rng.gen_bool(0.5) {
            let (addr, len) = if addresses.is_empty() || rng.gen_bool(0.5) {
                random_addr(&mut rng)
            } else {
                addresses
                    .iter()
                    .choose(&mut rng)
                    .map(|(addr, len)| (*addr, *len))
                    .unwrap()
            };
            result.push(Insn::ExactMatch(addr, len));
        } else {
            let (addr, len) = random_addr(&mut rng);
            result.push(Insn::LongestPrefixMatch(addr, len));
        }
    }
    result
}

pub fn sparse_addresses(seed: u64, num: usize) -> Vec<(Ipv4Addr, u8)> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..num).map(|_| random_addr(&mut rng)).collect()
}

pub fn fill_table(seed: u64, addresses: &[(Ipv4Addr, u8)]) -> Vec<Insn> {
    let mut rng = StdRng::seed_from_u64(seed);
    addresses
        .iter()
        .copied()
        .map(|(addr, len)| {
            let val = rng.gen::<u32>();
            Insn::Insert(addr, len, val)
        })
        .collect()
}

pub fn generate_random_mods_sparse(
    seed: u64,
    iter: usize,
    addresses: &[(Ipv4Addr, u8)],
) -> Vec<Insn> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..iter)
        .map(|_| {
            let (addr, len) = addresses.iter().choose(&mut rng).unwrap();
            if rng.gen_bool(0.5) {
                let val = rng.gen::<u32>();
                Insn::Insert(*addr, *len, val)
            } else {
                Insn::Remove(*addr, *len)
            }
        })
        .collect()
}

pub fn generate_random_lookups_sparse(
    seed: u64,
    iter: usize,
    addresses: &[(Ipv4Addr, u8)],
) -> Vec<Insn> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..iter)
        .map(|_| {
            let (addr, len) = addresses.iter().choose(&mut rng).unwrap();
            if rng.gen_bool(0.5) {
                Insn::ExactMatch(*addr, *len)
            } else {
                Insn::LongestPrefixMatch(*addr, *len)
            }
        })
        .collect()
}

pub fn execute_prefix_map(map: &mut PrefixMap<Ipv4Net, u32>, insns: &Vec<Insn>) {
    for insn in insns {
        std::hint::black_box(match insn {
            Insn::Insert(addr, len, val) => map.insert(Ipv4Net::new(*addr, *len).unwrap(), *val),
            Insn::Remove(addr, len) => map.remove(&Ipv4Net::new(*addr, *len).unwrap()),
            Insn::ExactMatch(addr, len) => map.get(&Ipv4Net::new(*addr, *len).unwrap()).copied(),
            Insn::LongestPrefixMatch(addr, len) => map
                .get_lpm(&Ipv4Net::new(*addr, *len).unwrap())
                .map(|(_, x)| *x),
        });
    }
}

pub fn execute_dense_prefix_map(map: &mut PrefixMap<Ipv4Net, u32>, insns: &Vec<Insn>) {
    for insn in insns {
        std::hint::black_box(match insn {
            Insn::Insert(addr, len, val) => map.insert(Ipv4Net::new(*addr, *len).unwrap(), *val),
            Insn::Remove(addr, len) => map.remove(&Ipv4Net::new(*addr, *len).unwrap()),
            Insn::ExactMatch(addr, len) => map.get(&Ipv4Net::new(*addr, *len).unwrap()).copied(),
            Insn::LongestPrefixMatch(addr, len) => map
                .get_lpm(&Ipv4Net::new(*addr, *len).unwrap())
                .map(|(_, x)| *x),
        });
    }
}

pub fn lookup_prefix_map(map: &PrefixMap<Ipv4Net, u32>, insns: &Vec<Insn>) {
    for insn in insns {
        std::hint::black_box(match insn {
            Insn::Insert(_, _, _) => unreachable!(),
            Insn::Remove(_, _) => unreachable!(),
            Insn::ExactMatch(addr, len) => map.get(&Ipv4Net::new(*addr, *len).unwrap()).copied(),
            Insn::LongestPrefixMatch(addr, len) => map
                .get_lpm(&Ipv4Net::new(*addr, *len).unwrap())
                .map(|(_, x)| *x),
        });
    }
}

pub fn lookup_dense_prefix_map(map: &PrefixMap<Ipv4Net, u32>, insns: &Vec<Insn>) {
    for insn in insns {
        std::hint::black_box(match insn {
            Insn::Insert(_, _, _) => unreachable!(),
            Insn::Remove(_, _) => unreachable!(),
            Insn::ExactMatch(addr, len) => map.get(&Ipv4Net::new(*addr, *len).unwrap()).copied(),
            Insn::LongestPrefixMatch(addr, len) => map
                .get_lpm(&Ipv4Net::new(*addr, *len).unwrap())
                .map(|(_, x)| *x),
        });
    }
}

pub fn execute_treebitmap(map: &mut IpLookupTable<Ipv4Addr, u32>, insns: &Vec<Insn>) {
    for insn in insns {
        std::hint::black_box(match insn {
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

pub fn lookup_treebitmap(map: &IpLookupTable<Ipv4Addr, u32>, insns: &Vec<Insn>) {
    for insn in insns {
        std::hint::black_box(match insn {
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
