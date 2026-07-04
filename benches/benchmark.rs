#![allow(dead_code)]
mod common;
use common::*;

const ITERS: usize = 100_000;

use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion, Throughput,
};
use ipnet::{Ipv4Net, Ipv6Net};
use prefix_trie::{Prefix, PrefixMap, PrefixSet};
use rand::prelude::*;
use std::borrow::Cow;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::Hash;

trait BenchPrefix
where
    Self: Prefix + Copy + Eq + Ord + Hash + DataSampler,
{
}
impl<P> BenchPrefix for P where Self: Prefix + Copy + Eq + Ord + Hash + DataSampler {}

fn bench_one<P, M>(
    group: &mut BenchmarkGroup<'_, WallTime>,
    setup: &[Insn<P>],
    insn: &[Insn<P>],
    shuffle_insn: bool,
) where
    P: BenchPrefix,
    M: BenchMap<P>,
{
    let mut rng = StdRng::seed_from_u64(0);
    group.bench_function(M::NAME, |b| {
        b.iter_with_setup(
            || {
                let insn = if shuffle_insn {
                    let mut insn = insn.to_vec();
                    insn.shuffle(&mut rng);
                    Cow::Owned(insn)
                } else {
                    Cow::Borrowed(insn)
                };
                let mut map = M::new_empty();
                map.run(setup);
                (map, insn)
            },
            |(mut map, insn)| {
                map.run(&insn);
                map
            },
        )
    });
}

fn bench_all<P>(
    group: &mut BenchmarkGroup<'_, WallTime>,
    setup: &[Insn<P>],
    insn: &[Insn<P>],
    shuffle_insn: bool,
) where
    P: BenchPrefix,
{
    bench_one::<P, PrefixMap<P, u32>>(group, setup, insn, shuffle_insn);
    bench_one::<P, P::IpLookupTable>(group, setup, insn, shuffle_insn);
    bench_one::<P, HashMap<P, u32>>(group, setup, insn, shuffle_insn);
    bench_one::<P, BTreeMap<P, u32>>(group, setup, insn, shuffle_insn);
}

fn bgp_mods_random_for<P>(c: &mut Criterion, group_name: &str, ordering: SortingOrder)
where
    P: BenchPrefix,
{
    let addrs = P::ris_peer_initial_state(0, ordering);
    let setup = fill_table(0, &addrs);
    let insn = P::random_mutations(0, &addrs, ITERS);

    let mut group = c.benchmark_group(group_name);
    group.throughput(Throughput::Elements(insn.len() as u64));
    bench_all(&mut group, &setup, &insn, false);
    group.finish();
}

pub fn bgp_mods_random_ipv4(c: &mut Criterion) {
    bgp_mods_random_for::<Ipv4Net>(c, "bgp-mods-random-ipv4", SortingOrder::Random);
}

pub fn bgp_mods_random_ipv6(c: &mut Criterion) {
    bgp_mods_random_for::<Ipv6Net>(c, "bgp-mods-random-ipv6", SortingOrder::Random);
}

fn bgp_lookup_random_for<P>(c: &mut Criterion, group_name: &str, ordering: SortingOrder)
where
    P: BenchPrefix,
{
    let addrs = P::ris_peer_initial_state(0, ordering);
    let setup = fill_table(0, &addrs);
    let insn = P::random_lookups(0, &addrs, ITERS);

    let mut group = c.benchmark_group(group_name);
    group.throughput(Throughput::Elements(insn.len() as u64));
    bench_all(&mut group, &setup, &insn, false);
    group.finish();
}

pub fn bgp_lookup_random_ipv4(c: &mut Criterion) {
    bgp_lookup_random_for::<Ipv4Net>(c, "bgp-lookup-random-ipv4", SortingOrder::Random);
}

pub fn bgp_lookup_random_ipv6(c: &mut Criterion) {
    bgp_lookup_random_for::<Ipv6Net>(c, "bgp-lookup-random-ipv6", SortingOrder::Random);
}

fn bgp_lookup_ris_for<P>(c: &mut Criterion, group_name: &str, ordering: SortingOrder)
where
    P: BenchPrefix,
{
    let addrs = P::ris_peer_initial_state(0, ordering);
    let setup = fill_table(0, &addrs);
    let insn = P::ris_peer_lookups();

    let mut group = c.benchmark_group(group_name);
    group.throughput(Throughput::Elements(insn.len() as u64));
    bench_all(&mut group, &setup, &insn, false);
    group.finish();
}

pub fn bgp_lookup_ris_ipv4(c: &mut Criterion) {
    bgp_lookup_ris_for::<Ipv4Net>(c, "bgp-lookup-ris-ipv4", SortingOrder::Random);
}

pub fn bgp_lookup_ris_ipv6(c: &mut Criterion) {
    bgp_lookup_ris_for::<Ipv6Net>(c, "bgp-lookup-ris-ipv6", SortingOrder::Random);
}

fn bgp_mods_ris_for<P>(c: &mut Criterion, group_name: &str, ordering: SortingOrder)
where
    P: BenchPrefix,
{
    let addrs = P::ris_peer_initial_state(0, ordering);
    let setup = fill_table(0, &addrs);
    let insn = P::ris_peer_mutations(1);

    let mut group = c.benchmark_group(group_name);
    group.throughput(Throughput::Elements(insn.len() as u64));
    bench_all(&mut group, &setup, &insn, false);
    group.finish();
}

pub fn bgp_mods_ris_ipv4(c: &mut Criterion) {
    bgp_mods_ris_for::<Ipv4Net>(c, "bgp-mods-ris-ipv4", SortingOrder::Random);
}

pub fn bgp_mods_ris_ipv6(c: &mut Criterion) {
    bgp_mods_ris_for::<Ipv6Net>(c, "bgp-mods-ris-ipv6", SortingOrder::Random);
}

fn bgp_create_for<P>(c: &mut Criterion, group_name: &str, ordering: SortingOrder)
where
    P: BenchPrefix,
{
    let addrs = P::ris_peer_initial_state(0, ordering);
    let setup = fill_table(0, &addrs);

    let mut group = c.benchmark_group(group_name);
    group.throughput(Throughput::Elements(setup.len() as u64));
    bench_all(
        &mut group,
        &[],
        &setup,
        matches!(ordering, SortingOrder::Random),
    );
    group.finish();
}

pub fn bgp_create_random_ipv4(c: &mut Criterion) {
    bgp_create_for::<Ipv4Net>(c, "bgp-create-random-ipv4", SortingOrder::Random);
}

pub fn bgp_create_random_ipv6(c: &mut Criterion) {
    bgp_create_for::<Ipv6Net>(c, "bgp-create-random-ipv6", SortingOrder::Random);
}

pub fn bgp_create_ordered_ipv4(c: &mut Criterion) {
    bgp_create_for::<Ipv4Net>(c, "bgp-create-ordered-ipv4", SortingOrder::Lexicographic);
}

pub fn bgp_create_ordered_ipv6(c: &mut Criterion) {
    bgp_create_for::<Ipv6Net>(c, "bgp-create-ordered-ipv6", SortingOrder::Lexicographic);
}

pub fn bgp_create_scattered_ipv4(c: &mut Criterion) {
    bgp_create_for::<Ipv4Net>(c, "bgp-create-scattered-ipv4", SortingOrder::Scattered);
}

pub fn bgp_create_scattered_ipv6(c: &mut Criterion) {
    bgp_create_for::<Ipv6Net>(c, "bgp-create-scattered-ipv6", SortingOrder::Scattered);
}

/// Benchmark aggregating the whole RIS table: `PrefixSet::aggregate` (bitmap-only drop + merge),
/// `PrefixMap::aggregate` (the value-aware ORTC), and `PrefixMap::aggregate_fill_default`. Each
/// prefix gets a next hop in `1..=32` (emulating 32 interfaces), so the ORTC actually merges.
fn aggregate_for<P>(c: &mut Criterion, group_name: &str)
where
    P: BenchPrefix,
{
    let addrs = P::ris_peer_initial_state(0, SortingOrder::Random);

    let set: PrefixSet<P> = addrs.iter().copied().collect();
    let mut rng = StdRng::seed_from_u64(0);
    let mut map: PrefixMap<P, u32> = PrefixMap::new();
    for &p in &addrs {
        map.insert(p, rng.gen_range(1..=32u32));
    }

    let mut group = c.benchmark_group(group_name);
    group.bench_function("set", |b| {
        b.iter_with_setup(
            || set.clone(),
            |mut s| {
                s.aggregate();
                s
            },
        )
    });
    group.bench_function("map", |b| {
        b.iter_with_setup(
            || map.clone(),
            |mut m| {
                m.aggregate();
                m
            },
        )
    });
    group.bench_function("ortc", |b| {
        b.iter_with_setup(
            || map.clone(),
            |mut m| {
                m.aggregate_fill_default();
                m
            },
        )
    });
    group.finish();
}

pub fn aggregate_ipv4(c: &mut Criterion) {
    aggregate_for::<Ipv4Net>(c, "aggregate-ipv4");
}

pub fn aggregate_ipv6(c: &mut Criterion) {
    aggregate_for::<Ipv6Net>(c, "aggregate-ipv6");
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
        .with_profiler(MyProfiler::default())
        .measurement_time(std::time::Duration::from_secs(10));
    targets =
        bgp_mods_random_ipv4,
        bgp_mods_random_ipv6,
        bgp_lookup_random_ipv4,
        bgp_lookup_random_ipv6,
        bgp_mods_ris_ipv4,
        bgp_mods_ris_ipv6,
        bgp_lookup_ris_ipv4,
        bgp_lookup_ris_ipv6,
        bgp_create_random_ipv4,
        bgp_create_random_ipv6,
        bgp_create_ordered_ipv4,
        bgp_create_ordered_ipv6,
        bgp_create_scattered_ipv4,
        bgp_create_scattered_ipv6,
        aggregate_ipv4,
        aggregate_ipv6,
);
criterion_main!(benches);
