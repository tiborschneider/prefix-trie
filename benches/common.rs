#![allow(dead_code)]

use std::{
    collections::{BTreeMap, HashMap},
    fs::File,
    hash::Hash,
    net::{Ipv4Addr, Ipv6Addr},
};

use ip_network_table_deps_treebitmap::IpLookupTable;
use ipnet::{Ipv4Net, Ipv6Net};
use num_traits::PrimInt;
use parquet::{
    file::reader::{FileReader, SerializedFileReader},
    record::RowAccessor,
};
use prefix_trie::{Prefix, PrefixMap};
use rand::prelude::*;

const PEER_MUTATIONS_IPV4_PARQUET: &str =
    "benches/data/20260511-mutations-peer-193.0.0.56AS3333.parquet";
const PEER_INITIAL_STATE_IPV4_PARQUET: &str =
    "benches/data/20260511-initial-state-peer-193.0.0.56AS3333.parquet";
const PEER_MUTATIONS_IPV6_PARQUET: &str =
    "benches/data/20260511-mutations-peer-193.0.0.56AS3333-ipv6.parquet";
const PEER_INITIAL_STATE_IPV6_PARQUET: &str =
    "benches/data/20260511-initial-state-peer-193.0.0.56AS3333-ipv6.parquet";

/// Sort prefixes in the deliberately adverse creation order used by the benchmarks:
/// shortest prefix first, then addresses by reversed bits, then raw address as a tie-breaker.
pub fn adverse_cmp<P: Prefix>(a: &P, b: &P) -> std::cmp::Ordering {
    a.prefix_len()
        .cmp(&b.prefix_len())
        .then(a.repr().reverse_bits().cmp(&b.repr().reverse_bits()))
        .then(a.repr().cmp(&b.repr()))
}

#[derive(Debug, Clone, Copy)]
pub enum Insn<P> {
    Insert(P, u32),
    Remove(P),
    ExactMatch(P),
}

impl<P: Prefix + Copy> Insn<P> {
    #[inline(always)]
    pub fn execute<M: BenchMap<P>>(&self, map: &mut M) -> Option<u32> {
        match self {
            Insn::Insert(p, v) => {
                map.insert(*p, *v);
                None
            }
            Insn::Remove(p) => map.remove(*p),
            Insn::ExactMatch(p) => map.exact_match(*p),
        }
    }
}

pub fn fill_table<P: Copy>(seed: u64, addresses: &[P]) -> Vec<Insn<P>> {
    let mut rng = StdRng::seed_from_u64(seed);
    addresses
        .iter()
        .copied()
        .map(|p| {
            let val = rng.gen::<u32>();
            Insn::Insert(p, val)
        })
        .collect()
}

#[derive(Debug, Clone, Copy)]
pub enum SortingOrder {
    Lexicographic,
    Random,
    /// Sorted by reversed bit order.
    Scattered,
}

pub trait DataSampler: Prefix + Sized + Copy {
    /// Associated Type to achieve the type bounds on the prefix.
    type IpLookupTable: BenchMap<Self>;

    fn ris_peer_initial_state(seed: u64, order: SortingOrder) -> Vec<Self>;
    fn ris_peer_mutations(seed: u64) -> Vec<Insn<Self>>;
    fn ris_peer_lookups() -> Vec<Insn<Self>> {
        Self::ris_peer_mutations(0)
            .into_iter()
            .map(|insn| match insn {
                Insn::Insert(p, _) | Insn::Remove(p) | Insn::ExactMatch(p) => Insn::ExactMatch(p),
            })
            .collect()
    }
    fn random_lookups(seed: u64, addresses: &[Self], iter: usize) -> Vec<Insn<Self>> {
        let mut rng = StdRng::seed_from_u64(seed);
        (0..iter)
            .map(|_| *addresses.iter().choose(&mut rng).unwrap())
            .map(|p| Insn::ExactMatch(p))
            .collect()
    }
    fn random_mutations(seed: u64, addresses: &[Self], iter: usize) -> Vec<Insn<Self>> {
        let mut rng = StdRng::seed_from_u64(seed);
        (0..iter)
            .map(|_| {
                let p = addresses.iter().choose(&mut rng).unwrap();
                if rng.gen_bool(0.5) {
                    let val = rng.gen::<u32>();
                    Insn::Insert(*p, val)
                } else {
                    Insn::Remove(*p)
                }
            })
            .collect()
    }
}

fn parquet_reader(filename: &str) -> SerializedFileReader<File> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(filename);
    let file = File::open(&path).unwrap_or_else(|err| {
        panic!("failed to open {}: {err}", path.display());
    });
    SerializedFileReader::new(file).unwrap_or_else(|err| {
        panic!("failed to read {}: {err}", path.display());
    })
}

impl DataSampler for Ipv4Net {
    type IpLookupTable = IpLookupTable<Ipv4Addr, u32>;

    fn ris_peer_initial_state(seed: u64, order: SortingOrder) -> Vec<Ipv4Net> {
        let reader = parquet_reader(PEER_INITIAL_STATE_IPV4_PARQUET);
        let mut rng = StdRng::seed_from_u64(seed);
        let mut prefixes = reader
            .get_row_iter(None)
            .unwrap()
            .map(|row| row.unwrap())
            .filter_map(|row| row.get_string(0).unwrap().parse::<Ipv4Net>().ok())
            .collect::<Vec<_>>();
        match order {
            SortingOrder::Lexicographic => prefixes.sort(),
            SortingOrder::Random => prefixes.shuffle(&mut rng),
            SortingOrder::Scattered => prefixes.sort_by(adverse_cmp),
        }
        prefixes
    }

    fn ris_peer_mutations(seed: u64) -> Vec<Insn<Ipv4Net>> {
        let reader = parquet_reader(PEER_MUTATIONS_IPV4_PARQUET);
        let mut mutations =
            Vec::with_capacity(reader.metadata().file_metadata().num_rows() as usize);
        let mut rng = StdRng::seed_from_u64(seed);

        for row in reader.get_row_iter(None).unwrap() {
            let row = row.unwrap();
            let operation = row.get_string(0).unwrap();
            let Ok(prefix) = row.get_string(1).unwrap().parse::<Ipv4Net>() else {
                continue;
            };

            let mutation = match operation.as_str() {
                "A" => Insn::Insert(prefix, rng.gen::<u32>()),
                "W" => Insn::Remove(prefix),
                op => panic!("unknown mutation operation {op:?}"),
            };
            mutations.push(mutation);
        }
        mutations
    }
}

impl DataSampler for Ipv6Net {
    type IpLookupTable = IpLookupTable<Ipv6Addr, u32>;

    fn ris_peer_initial_state(seed: u64, order: SortingOrder) -> Vec<Ipv6Net> {
        let reader = parquet_reader(PEER_INITIAL_STATE_IPV6_PARQUET);
        let mut rng = StdRng::seed_from_u64(seed);
        let mut prefixes = reader
            .get_row_iter(None)
            .unwrap()
            .map(|row| row.unwrap())
            .filter_map(|row| row.get_string(0).unwrap().parse::<Ipv6Net>().ok())
            .collect::<Vec<_>>();
        match order {
            SortingOrder::Lexicographic => prefixes.sort(),
            SortingOrder::Random => prefixes.shuffle(&mut rng),
            SortingOrder::Scattered => prefixes.sort_by(adverse_cmp),
        }
        prefixes
    }

    fn ris_peer_mutations(seed: u64) -> Vec<Insn<Ipv6Net>> {
        let reader = parquet_reader(PEER_MUTATIONS_IPV6_PARQUET);
        let mut mutations =
            Vec::with_capacity(reader.metadata().file_metadata().num_rows() as usize);
        let mut rng = StdRng::seed_from_u64(seed);

        for row in reader.get_row_iter(None).unwrap() {
            let row = row.unwrap();
            let operation = row.get_string(0).unwrap();
            let Ok(prefix) = row.get_string(1).unwrap().parse::<Ipv6Net>() else {
                continue;
            };

            let mutation = match operation.as_str() {
                "A" => Insn::Insert(prefix, rng.gen::<u32>()),
                "W" => Insn::Remove(prefix),
                op => panic!("unknown mutation operation {op:?}"),
            };
            mutations.push(mutation);
        }
        mutations
    }
}

pub trait BenchMap<P: Prefix + Copy> {
    const NAME: &'static str;
    fn new_empty() -> Self;
    fn insert(&mut self, prefix: P, val: u32);
    fn remove(&mut self, prefix: P) -> Option<u32>;
    fn exact_match(&self, prefix: P) -> Option<u32>;
    fn run(&mut self, insns: &[Insn<P>])
    where
        Self: Sized,
    {
        for insn in insns {
            std::hint::black_box(insn.execute(self));
        }
    }
}

impl<P: Prefix + Copy> BenchMap<P> for PrefixMap<P, u32> {
    const NAME: &'static str = "PrefixMap";

    fn new_empty() -> Self {
        Self::new()
    }

    fn insert(&mut self, prefix: P, val: u32) {
        self.insert(prefix, val);
    }

    fn remove(&mut self, prefix: P) -> Option<u32> {
        self.remove(&prefix)
    }

    fn exact_match(&self, prefix: P) -> Option<u32> {
        self.get(&prefix).copied()
    }
}

impl<P: Prefix + Copy + Hash + Eq> BenchMap<P> for HashMap<P, u32> {
    const NAME: &'static str = "HashMap";

    fn new_empty() -> Self {
        Self::new()
    }

    fn insert(&mut self, prefix: P, val: u32) {
        self.insert(prefix, val);
    }

    fn remove(&mut self, prefix: P) -> Option<u32> {
        self.remove(&prefix)
    }

    fn exact_match(&self, prefix: P) -> Option<u32> {
        self.get(&prefix).copied()
    }
}

impl<P: Prefix + Copy + Ord + Eq> BenchMap<P> for BTreeMap<P, u32> {
    const NAME: &'static str = "BTreeMap";

    fn new_empty() -> Self {
        Self::new()
    }

    fn insert(&mut self, prefix: P, val: u32) {
        self.insert(prefix, val);
    }

    fn remove(&mut self, prefix: P) -> Option<u32> {
        self.remove(&prefix)
    }

    fn exact_match(&self, prefix: P) -> Option<u32> {
        self.get(&prefix).copied()
    }
}

impl BenchMap<Ipv4Net> for IpLookupTable<Ipv4Addr, u32> {
    const NAME: &'static str = "TreeBitMap";

    fn new_empty() -> Self {
        IpLookupTable::new()
    }

    fn insert(&mut self, prefix: Ipv4Net, val: u32) {
        self.insert(prefix.addr(), prefix.prefix_len() as u32, val);
    }

    fn remove(&mut self, prefix: Ipv4Net) -> Option<u32> {
        self.remove(prefix.addr(), prefix.prefix_len() as u32)
    }

    fn exact_match(&self, prefix: Ipv4Net) -> Option<u32> {
        self.exact_match(prefix.addr(), prefix.prefix_len() as u32)
            .copied()
    }
}

impl BenchMap<Ipv6Net> for IpLookupTable<Ipv6Addr, u32> {
    const NAME: &'static str = "TreeBitMap";

    fn new_empty() -> Self {
        IpLookupTable::new()
    }

    fn insert(&mut self, prefix: Ipv6Net, val: u32) {
        self.insert(prefix.addr(), prefix.prefix_len() as u32, val);
    }

    fn remove(&mut self, prefix: Ipv6Net) -> Option<u32> {
        self.remove(prefix.addr(), prefix.prefix_len() as u32)
    }

    fn exact_match(&self, prefix: Ipv6Net) -> Option<u32> {
        self.exact_match(prefix.addr(), prefix.prefix_len() as u32)
            .copied()
    }
}
