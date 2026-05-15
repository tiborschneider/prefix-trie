#![allow(dead_code)]
#![allow(clippy::incompatible_msrv)]

use ip_network_table_deps_treebitmap::IpLookupTable;
use ipnet::Ipv4Net;
use parquet::file::reader::{FileReader, SerializedFileReader};
use parquet::record::RowAccessor;
use prefix_trie::*;
use rand::prelude::*;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs::File;
use std::net::Ipv4Addr;

const PEER_MUTATIONS_PARQUET: &str =
    "benches/data/20260511-mutations-peer-193.0.0.56AS3333.parquet";
const PEER_INITIAL_STATE_PARQUET: &str =
    "benches/data/20260511-initial-state-peer-193.0.0.56AS3333.parquet";

pub enum Insn {
    Insert(Ipv4Addr, u8, u32),
    Remove(Ipv4Addr, u8),
    ExactMatch(Ipv4Addr, u8),
}

pub trait BenchMap: Sized {
    const NAME: &'static str;
    fn new_empty() -> Self;
    fn insert(&mut self, addr: Ipv4Addr, len: u8, val: u32);
    fn remove(&mut self, addr: Ipv4Addr, len: u8);
    fn exact_match(&self, addr: Ipv4Addr, len: u8) -> Option<u32>;
}

impl BenchMap for PrefixMap<Ipv4Net, u32> {
    const NAME: &'static str = "PrefixMap";
    fn new_empty() -> Self {
        PrefixMap::new()
    }
    fn insert(&mut self, addr: Ipv4Addr, len: u8, val: u32) {
        self.insert(Ipv4Net::new(addr, len).unwrap(), val);
    }
    fn remove(&mut self, addr: Ipv4Addr, len: u8) {
        self.remove(&Ipv4Net::new(addr, len).unwrap());
    }
    fn exact_match(&self, addr: Ipv4Addr, len: u8) -> Option<u32> {
        self.get(&Ipv4Net::new(addr, len).unwrap()).copied()
    }
}

impl BenchMap for IpLookupTable<Ipv4Addr, u32> {
    const NAME: &'static str = "TreeBitMap";
    fn new_empty() -> Self {
        IpLookupTable::new()
    }
    fn insert(&mut self, addr: Ipv4Addr, len: u8, val: u32) {
        self.insert(addr, len as u32, val);
    }
    fn remove(&mut self, addr: Ipv4Addr, len: u8) {
        self.remove(addr, len as u32);
    }
    fn exact_match(&self, addr: Ipv4Addr, len: u8) -> Option<u32> {
        self.exact_match(addr, len as u32).copied()
    }
}

impl BenchMap for HashMap<Ipv4Net, u32> {
    const NAME: &'static str = "HashMap";
    fn new_empty() -> Self {
        HashMap::new()
    }
    fn insert(&mut self, addr: Ipv4Addr, len: u8, val: u32) {
        self.insert(Ipv4Net::new(addr, len).unwrap(), val);
    }
    fn remove(&mut self, addr: Ipv4Addr, len: u8) {
        self.remove(&Ipv4Net::new(addr, len).unwrap());
    }
    fn exact_match(&self, addr: Ipv4Addr, len: u8) -> Option<u32> {
        self.get(&Ipv4Net::new(addr, len).unwrap()).copied()
    }
}

impl BenchMap for BTreeMap<Ipv4Net, u32> {
    const NAME: &'static str = "BTreeMap";
    fn new_empty() -> Self {
        BTreeMap::new()
    }
    fn insert(&mut self, addr: Ipv4Addr, len: u8, val: u32) {
        self.insert(Ipv4Net::new(addr, len).unwrap(), val);
    }
    fn remove(&mut self, addr: Ipv4Addr, len: u8) {
        self.remove(&Ipv4Net::new(addr, len).unwrap());
    }
    fn exact_match(&self, addr: Ipv4Addr, len: u8) -> Option<u32> {
        self.get(&Ipv4Net::new(addr, len).unwrap()).copied()
    }
}

pub fn execute<M: BenchMap>(map: &mut M, insns: &[Insn]) {
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
pub fn ris_peer_initial_state(seed: u64) -> Vec<(Ipv4Addr, u8)> {
    let mut rng = StdRng::seed_from_u64(seed);

    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(PEER_INITIAL_STATE_PARQUET);
    let file = File::open(&path).unwrap_or_else(|err| {
        panic!("failed to open {}: {err}", path.display());
    });
    let reader = SerializedFileReader::new(file).unwrap_or_else(|err| {
        panic!("failed to read {}: {err}", path.display());
    });

    let mut prefixes = Vec::with_capacity(reader.metadata().file_metadata().num_rows() as usize);

    for row in reader.get_row_iter(None).unwrap() {
        let row = row.unwrap();
        if let Ok(prefix) = row.get_string(0).unwrap().parse::<Ipv4Net>() {
            prefixes.push((prefix.addr(), prefix.prefix_len()));
        }
    }

    prefixes.shuffle(&mut rng);

    prefixes
}

/// Return all mutations during 24h of a RIS peer
///
/// The data is sorted by time and the data is returned in original order.
pub fn ris_peer_mutations() -> Vec<Insn> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(PEER_MUTATIONS_PARQUET);
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
        let Ok(prefix) = row.get_string(1).unwrap().parse::<Ipv4Net>() else {
            continue;
        };

        let mutation = match operation.as_str() {
            "A" => Insn::Insert(prefix.addr(), prefix.prefix_len(), rng.gen::<u32>()),
            "W" => Insn::Remove(prefix.addr(), prefix.prefix_len()),
            op => panic!("unknown mutation operation {op:?}"),
        };
        mutations.push(mutation);
    }

    mutations
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
            Insn::ExactMatch(*addr, *len)
        })
        .collect()
}
