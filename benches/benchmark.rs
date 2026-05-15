#![allow(dead_code)]
mod common;
use common::*;

const ITERS: usize = 100_000;

use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use ip_network_table_deps_treebitmap::IpLookupTable;
use ipnet::Ipv4Net;
use itertools::Itertools;
use prefix_trie::*;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::net::Ipv4Addr;

macro_rules! bench_one {
    ($group:expr, $t:ty, |$s:ident| $setup:expr, |$r:ident| $run:expr) => {{
        $group.bench_function(<$t as BenchMap>::NAME, |b| {
            b.iter_with_setup(
                || {
                    let mut $s: $t = <$t as BenchMap>::new_empty();
                    $setup;
                    $s
                },
                |mut $r| {
                    $run;
                    $r
                },
            )
        });
    }};
}

macro_rules! bench_all {
    ($group:expr, |$s:ident| $setup:expr, |$r:ident| $run:expr) => {
        bench_one!($group, PrefixMap<Ipv4Net, u32>, |$s| $setup, |$r| $run);
        bench_one!($group, IpLookupTable<Ipv4Addr, u32>, |$s| $setup, |$r| $run);
        bench_one!($group, HashMap<Ipv4Net, u32>, |$s| $setup, |$r| $run);
        bench_one!($group, BTreeMap<Ipv4Net, u32>, |$s| $setup, |$r| $run);
    };
}

pub fn random_mods(c: &mut Criterion) {
    let (insn, _) = generate_random_mods_dense(1, ITERS);

    let mut group = c.benchmark_group("random-mods");
    group.throughput(Throughput::Elements(insn.len() as u64));
    bench_all!(group, |_m| {}, |m| execute(&mut m, &insn));
    group.finish();
}

pub fn random_lookup(c: &mut Criterion) {
    let (mods, addrs) = generate_random_mods_dense(1, ITERS);
    let lookups = generate_random_lookups_dense(2, ITERS, &addrs);

    let mut group = c.benchmark_group("random-lookup");
    group.throughput(Throughput::Elements(lookups.len() as u64));
    bench_all!(group, |m| execute(&mut m, &mods), |m| execute(
        &mut m, &lookups
    ));
    group.finish();
}

pub fn bgp_mods_random(c: &mut Criterion) {
    let addrs = ris_peer_initial_state(0);
    let setup = fill_table(0, &addrs);
    let insn = generate_random_mods_sparse(0, ITERS, &addrs);

    let mut group = c.benchmark_group("bgp-mods-random");
    group.throughput(Throughput::Elements(insn.len() as u64));
    bench_all!(group, |m| execute(&mut m, &setup), |m| execute(
        &mut m, &insn
    ));
    group.finish();
}

pub fn bgp_lookup_random(c: &mut Criterion) {
    let addrs = ris_peer_initial_state(0);
    let mods = fill_table(0, &addrs);
    let lookups = generate_random_lookups_sparse(0, ITERS, &addrs);

    let mut group = c.benchmark_group("bgp-lookup-random");
    group.throughput(Throughput::Elements(lookups.len() as u64));
    bench_all!(group, |m| execute(&mut m, &mods), |m| execute(
        &mut m, &lookups
    ));
    group.finish();
}

pub fn bgp_lookup_ris(c: &mut Criterion) {
    let addrs = ris_peer_initial_state(0);
    let mods = fill_table(0, &addrs);
    let mutations = ris_peer_mutations();
    let lookups = mutations
        .into_iter()
        .map(|x| match x {
            Insn::Insert(addr, len, _) | Insn::Remove(addr, len) | Insn::ExactMatch(addr, len) => {
                Insn::ExactMatch(addr, len)
            }
        })
        .collect::<Vec<_>>();

    let mut group = c.benchmark_group("bgp-lookup-ris");
    group.throughput(Throughput::Elements(lookups.len() as u64));
    bench_all!(group, |m| execute(&mut m, &mods), |m| execute(
        &mut m, &lookups
    ));
    group.finish();
}

pub fn bgp_mods_ris(c: &mut Criterion) {
    let addrs = ris_peer_initial_state(0);
    let initial_table = fill_table(0, &addrs);
    let mutations = ris_peer_mutations();

    let mut group = c.benchmark_group("bgp-mods-ris");
    group.throughput(Throughput::Elements(mutations.len() as u64));
    bench_all!(group, |m| execute(&mut m, &initial_table), |m| execute(
        &mut m, &mutations
    ));
    group.finish();
}

pub fn bgp_create_random(c: &mut Criterion) {
    let addrs = ris_peer_initial_state(0);
    let inserts = fill_table(0, &addrs);

    let mut group = c.benchmark_group("bgp-create-random");
    group.throughput(Throughput::Elements(inserts.len() as u64));
    bench_all!(group, |_m| {}, |m| execute(&mut m, &inserts));
    group.finish();
}

pub fn bgp_create_ordered(c: &mut Criterion) {
    let addrs = ris_peer_initial_state(0);
    let sorted_addrs: Vec<_> = addrs.iter().cloned().sorted().collect();
    let inserts = fill_table(0, &sorted_addrs);

    let mut group = c.benchmark_group("bgp-create-ordered");
    group.throughput(Throughput::Elements(inserts.len() as u64));
    bench_all!(group, |_m| {}, |m| execute(&mut m, &inserts));
    group.finish();
}

#[derive(Default)]
struct MyProfiler {
    active_profiler: Option<pprof::ProfilerGuard<'static>>,
    already_profiled: HashSet<(String, std::path::PathBuf)>,
}

impl criterion::profiler::Profiler for MyProfiler {
    fn start_profiling(&mut self, benchmark_id: &str, benchmark_dir: &std::path::Path) {
        assert!(self.active_profiler.is_none());
        if self
            .already_profiled
            .insert((benchmark_id.to_string(), benchmark_dir.to_path_buf()))
        {
            std::fs::write("/tmp/profiler", benchmark_id.as_bytes()).unwrap();
            self.active_profiler = Some(
                pprof::ProfilerGuardBuilder::default()
                    .frequency(10_000)
                    .build()
                    .unwrap(),
            )
        }
    }

    fn stop_profiling(&mut self, _: &str, benchmark_dir: &std::path::Path) {
        if let Some(profile) = self.active_profiler.take() {
            let report = profile.report().build().unwrap();
            std::fs::create_dir_all(benchmark_dir).unwrap();
            let benchmark_file = benchmark_dir.join("flamegraph.svg");
            let writer = std::fs::File::create(&benchmark_file)
                .unwrap_or_else(|_| panic!("Failed to create file {benchmark_file:?}"));
            report.flamegraph(writer).unwrap();
        }
    }
}

criterion_group!(
    name = benches;
    config = Criterion::default()
        //.sample_size(50)
        // .with_profiler(MyProfiler::default())
        .measurement_time(std::time::Duration::from_secs(10));
    targets =
        // random_mods,
        // random_lookup,
        bgp_mods_random,
        bgp_lookup_random,
        bgp_mods_ris,
        bgp_lookup_ris,
        bgp_create_random,
        bgp_create_ordered,
);
criterion_main!(benches);
