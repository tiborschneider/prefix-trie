#![allow(dead_code)]
#![allow(clippy::incompatible_msrv)]

use ip_network_table_deps_treebitmap::IpLookupTable;
use ipnet::{Ipv4Net, Ipv6Net};
use parquet::file::reader::{FileReader, SerializedFileReader};
use parquet::record::RowAccessor;
use prefix_trie::*;
use rand::prelude::*;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs::File;
use std::hash::Hash;
use std::net::{Ipv4Addr, Ipv6Addr};

const PEER_MUTATIONS_IPV4_PARQUET: &str =
    "benches/data/20260511-mutations-peer-193.0.0.56AS3333.parquet";
const PEER_INITIAL_STATE_IPV4_PARQUET: &str =
    "benches/data/20260511-initial-state-peer-193.0.0.56AS3333.parquet";
const PEER_MUTATIONS_IPV6_PARQUET: &str =
    "benches/data/20260511-mutations-peer-193.0.0.56AS3333-ipv6.parquet";
const PEER_INITIAL_STATE_IPV6_PARQUET: &str =
    "benches/data/20260511-initial-state-peer-193.0.0.56AS3333-ipv6.parquet";

pub enum Ipv4 {}
pub enum Ipv6 {}

pub trait BenchFamily: Sized {
    type Addr: Copy + Eq + Hash + Ord;
    type Net;
    type PrefixMapImpl: BenchMap<Self>;
    type TreeBitmapImpl: BenchMap<Self>;
    type HashMapImpl: BenchMap<Self>;
    type BTreeMapImpl: BenchMap<Self>;

    const NAME: &'static str;
    const MUTATIONS_PARQUET: &'static str;
    const INITIAL_STATE_PARQUET: &'static str;

    fn parse_net(value: &str) -> Option<Self::Net>;
    fn addr(net: &Self::Net) -> Self::Addr;
    fn prefix_len(net: &Self::Net) -> u8;
    fn reverse_bits(addr: Self::Addr) -> u128;
}

impl BenchFamily for Ipv4 {
    type Addr = Ipv4Addr;
    type Net = Ipv4Net;
    type PrefixMapImpl = PrefixMap<Ipv4Net, u32>;
    type TreeBitmapImpl = IpLookupTable<Ipv4Addr, u32>;
    type HashMapImpl = HashMap<Ipv4Net, u32>;
    type BTreeMapImpl = BTreeMap<Ipv4Net, u32>;

    const NAME: &'static str = "IPv4";
    const MUTATIONS_PARQUET: &'static str = PEER_MUTATIONS_IPV4_PARQUET;
    const INITIAL_STATE_PARQUET: &'static str = PEER_INITIAL_STATE_IPV4_PARQUET;

    fn parse_net(value: &str) -> Option<Self::Net> {
        value.parse().ok()
    }

    fn addr(net: &Self::Net) -> Self::Addr {
        net.addr()
    }

    fn prefix_len(net: &Self::Net) -> u8 {
        net.prefix_len()
    }

    fn reverse_bits(addr: Self::Addr) -> u128 {
        u32::from(addr).reverse_bits() as u128
    }
}

impl BenchFamily for Ipv6 {
    type Addr = Ipv6Addr;
    type Net = Ipv6Net;
    type PrefixMapImpl = PrefixMap<Ipv6Net, u32>;
    type TreeBitmapImpl = IpLookupTable<Ipv6Addr, u32>;
    type HashMapImpl = HashMap<Ipv6Net, u32>;
    type BTreeMapImpl = BTreeMap<Ipv6Net, u32>;

    const NAME: &'static str = "IPv6";
    const MUTATIONS_PARQUET: &'static str = PEER_MUTATIONS_IPV6_PARQUET;
    const INITIAL_STATE_PARQUET: &'static str = PEER_INITIAL_STATE_IPV6_PARQUET;

    fn parse_net(value: &str) -> Option<Self::Net> {
        value.parse().ok()
    }

    fn addr(net: &Self::Net) -> Self::Addr {
        net.addr()
    }

    fn prefix_len(net: &Self::Net) -> u8 {
        net.prefix_len()
    }

    fn reverse_bits(addr: Self::Addr) -> u128 {
        u128::from(addr).reverse_bits()
    }
}

/// Sort prefixes in the deliberately adverse creation order used by the benchmarks:
/// shortest prefix first, then addresses by reversed bits, then raw address as a tie-breaker.
pub fn adverse_cmp<F: BenchFamily>(a: &(F::Addr, u8), b: &(F::Addr, u8)) -> Ordering {
    a.1.cmp(&b.1)
        .then(F::reverse_bits(a.0).cmp(&F::reverse_bits(b.0)))
        .then(a.0.cmp(&b.0))
}

pub enum Insn<F: BenchFamily> {
    Insert(F::Addr, u8, u32),
    Remove(F::Addr, u8),
    ExactMatch(F::Addr, u8),
}

pub trait BenchMap<F: BenchFamily>: Sized {
    const NAME: &'static str;
    fn new_empty() -> Self;
    fn insert(&mut self, addr: F::Addr, len: u8, val: u32);
    fn remove(&mut self, addr: F::Addr, len: u8);
    fn exact_match(&self, addr: F::Addr, len: u8) -> Option<u32>;
}

macro_rules! impl_net_bench_map {
    ($family:ty, $addr:ty, $net:ty, $map:ty, $name:literal) => {
        impl BenchMap<$family> for $map {
            const NAME: &'static str = $name;
            fn new_empty() -> Self {
                <$map>::new()
            }
            fn insert(&mut self, addr: $addr, len: u8, val: u32) {
                self.insert(<$net>::new(addr, len).unwrap(), val);
            }
            fn remove(&mut self, addr: $addr, len: u8) {
                self.remove(&<$net>::new(addr, len).unwrap());
            }
            fn exact_match(&self, addr: $addr, len: u8) -> Option<u32> {
                self.get(&<$net>::new(addr, len).unwrap()).copied()
            }
        }
    };
}

impl_net_bench_map!(
    Ipv4,
    Ipv4Addr,
    Ipv4Net,
    PrefixMap<Ipv4Net, u32>,
    "PrefixMap"
);
impl_net_bench_map!(
    Ipv6,
    Ipv6Addr,
    Ipv6Net,
    PrefixMap<Ipv6Net, u32>,
    "PrefixMap"
);
impl_net_bench_map!(
    Ipv4,
    Ipv4Addr,
    Ipv4Net,
    HashMap<Ipv4Net, u32>,
    "HashMap"
);
impl_net_bench_map!(
    Ipv6,
    Ipv6Addr,
    Ipv6Net,
    HashMap<Ipv6Net, u32>,
    "HashMap"
);
impl_net_bench_map!(
    Ipv4,
    Ipv4Addr,
    Ipv4Net,
    BTreeMap<Ipv4Net, u32>,
    "BTreeMap"
);
impl_net_bench_map!(
    Ipv6,
    Ipv6Addr,
    Ipv6Net,
    BTreeMap<Ipv6Net, u32>,
    "BTreeMap"
);

macro_rules! impl_treebitmap_bench_map {
    ($family:ty, $addr:ty) => {
        impl BenchMap<$family> for IpLookupTable<$addr, u32> {
            const NAME: &'static str = "TreeBitMap";
            fn new_empty() -> Self {
                IpLookupTable::new()
            }
            fn insert(&mut self, addr: $addr, len: u8, val: u32) {
                self.insert(addr, len as u32, val);
            }
            fn remove(&mut self, addr: $addr, len: u8) {
                self.remove(addr, len as u32);
            }
            fn exact_match(&self, addr: $addr, len: u8) -> Option<u32> {
                self.exact_match(addr, len as u32).copied()
            }
        }
    };
}

impl_treebitmap_bench_map!(Ipv4, Ipv4Addr);
impl_treebitmap_bench_map!(Ipv6, Ipv6Addr);

pub fn execute<F: BenchFamily, M: BenchMap<F>>(map: &mut M, insns: &[Insn<F>]) {
    for insn in insns {
        std::hint::black_box(match insn {
            Insn::Insert(addr, len, val) => {
                map.insert(*addr, *len, *val);
                None
            }
            Insn::Remove(addr, len) => {
                map.remove(*addr, *len);
                None
            }
            Insn::ExactMatch(addr, len) => map.exact_match(*addr, *len),
        });
    }
}

pub fn random_addr(rng: &mut StdRng) -> (Ipv4Addr, u8) {
    let addr: Ipv4Addr = rng.gen::<u32>().into();
    let max_len = 24;
    let min_len = 8;
    let len = rng.gen_range(min_len..max_len);
    let net = Ipv4Net::new(addr, len).unwrap().trunc();
    (net.addr(), net.prefix_len())
}

/// Return all prefixes in the RIB of a RIS peer, in random order.
pub fn ris_peer_initial_state<F: BenchFamily>(seed: u64) -> Vec<(F::Addr, u8)> {
    let mut rng = StdRng::seed_from_u64(seed);

    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(F::INITIAL_STATE_PARQUET);
    let file = File::open(&path).unwrap_or_else(|err| {
        panic!("failed to open {}: {err}", path.display());
    });
    let reader = SerializedFileReader::new(file).unwrap_or_else(|err| {
        panic!("failed to read {}: {err}", path.display());
    });

    let mut prefixes = Vec::with_capacity(reader.metadata().file_metadata().num_rows() as usize);

    for row in reader.get_row_iter(None).unwrap() {
        let row = row.unwrap();
        if let Some(prefix) = F::parse_net(row.get_string(0).unwrap()) {
            prefixes.push((F::addr(&prefix), F::prefix_len(&prefix)));
        }
    }

    prefixes.shuffle(&mut rng);

    prefixes
}

/// Return all mutations during 24h of a RIS peer
///
/// The data is sorted by time and the data is returned in original order.
pub fn ris_peer_mutations<F: BenchFamily>() -> Vec<Insn<F>> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(F::MUTATIONS_PARQUET);
    let file = File::open(&path).unwrap_or_else(|err| {
        panic!("failed to open {}: {err}", path.display());
    });
    let reader = SerializedFileReader::new(file).unwrap_or_else(|err| {
        panic!("failed to read {}: {err}", path.display());
    });
    let mut mutations = Vec::with_capacity(reader.metadata().file_metadata().num_rows() as usize);
    let mut rng = StdRng::seed_from_u64(0);

    for row in reader.get_row_iter(None).unwrap() {
        let row = row.unwrap();
        let operation = row.get_string(0).unwrap();
        let Some(prefix) = F::parse_net(row.get_string(1).unwrap()) else {
            continue;
        };

        let mutation = match operation.as_str() {
            "A" => Insn::Insert(F::addr(&prefix), F::prefix_len(&prefix), rng.gen::<u32>()),
            "W" => Insn::Remove(F::addr(&prefix), F::prefix_len(&prefix)),
            op => panic!("unknown mutation operation {op:?}"),
        };
        mutations.push(mutation);
    }

    mutations
}

pub fn generate_random_mods_dense(
    seed: u64,
    iter: usize,
) -> (Vec<Insn<Ipv4>>, HashSet<(Ipv4Addr, u8)>) {
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
) -> Vec<Insn<Ipv4>> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut result = Vec::new();

    for _ in 0..iter {
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
    }
    result
}

pub fn sparse_addresses(seed: u64, num: usize) -> Vec<(Ipv4Addr, u8)> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..num).map(|_| random_addr(&mut rng)).collect()
}

pub fn fill_table<F: BenchFamily>(seed: u64, addresses: &[(F::Addr, u8)]) -> Vec<Insn<F>> {
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

pub fn generate_random_mods_sparse<F: BenchFamily>(
    seed: u64,
    iter: usize,
    addresses: &[(F::Addr, u8)],
) -> Vec<Insn<F>> {
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

pub fn generate_random_lookups_sparse<F: BenchFamily>(
    seed: u64,
    iter: usize,
    addresses: &[(F::Addr, u8)],
) -> Vec<Insn<F>> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..iter)
        .map(|_| {
            let (addr, len) = addresses.iter().choose(&mut rng).unwrap();
            Insn::ExactMatch(*addr, *len)
        })
        .collect()
}
