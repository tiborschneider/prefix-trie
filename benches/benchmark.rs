#![allow(dead_code)]
mod common;
use common::*;

const ITERS: usize = 100_000;

use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use itertools::Itertools;
use std::collections::HashSet;

macro_rules! bench_one {
    ($group:expr, $family:ty, $map:ty, $setup:expr, $run:expr) => {{
        $group.bench_function(<$map as BenchMap<$family>>::NAME, |b| {
            b.iter_with_setup(
                || {
                    let mut map = <$map as BenchMap<$family>>::new_empty();
                    execute::<$family, _>(&mut map, $setup);
                    map
                },
                |mut map| {
                    execute::<$family, _>(&mut map, $run);
                    map
                },
            )
        });
    }};
}

macro_rules! bench_all {
    ($group:expr, $family:ty, $setup:expr, $run:expr) => {{
        bench_one!(
            $group,
            $family,
            <$family as BenchFamily>::PrefixMapImpl,
            $setup,
            $run
        );
        bench_one!(
            $group,
            $family,
            <$family as BenchFamily>::TreeBitmapImpl,
            $setup,
            $run
        );
        bench_one!(
            $group,
            $family,
            <$family as BenchFamily>::HashMapImpl,
            $setup,
            $run
        );
        bench_one!(
            $group,
            $family,
            <$family as BenchFamily>::BTreeMapImpl,
            $setup,
            $run
        );
    }};
}

pub fn random_mods(c: &mut Criterion) {
    let (insn, _) = generate_random_mods_dense(1, ITERS);

    let mut group = c.benchmark_group("random-mods");
    group.throughput(Throughput::Elements(insn.len() as u64));
    bench_all!(group, Ipv4, &[], &insn);
    group.finish();
}

pub fn random_lookup(c: &mut Criterion) {
    let (mods, addrs) = generate_random_mods_dense(1, ITERS);
    let lookups = generate_random_lookups_dense(2, ITERS, &addrs);

    let mut group = c.benchmark_group("random-lookup");
    group.throughput(Throughput::Elements(lookups.len() as u64));
    bench_all!(group, Ipv4, &mods, &lookups);
    group.finish();
}

fn bgp_mods_random_for<F>(c: &mut Criterion, group_name: &str)
where
    F: BenchFamily,
{
    let addrs = ris_peer_initial_state::<F>(0);
    let setup = fill_table::<F>(0, &addrs);
    let insn = generate_random_mods_sparse::<F>(0, ITERS, &addrs);

    let mut group = c.benchmark_group(group_name);
    group.throughput(Throughput::Elements(insn.len() as u64));
    bench_all!(group, F, &setup, &insn);
    group.finish();
}

pub fn bgp_mods_random(c: &mut Criterion) {
    bgp_mods_random_for::<Ipv4>(c, "bgp-mods-random");
}

pub fn bgp_mods_random_ipv6(c: &mut Criterion) {
    bgp_mods_random_for::<Ipv6>(c, "bgp-mods-random-ipv6");
}

fn bgp_lookup_random_for<F>(c: &mut Criterion, group_name: &str)
where
    F: BenchFamily,
{
    let addrs = ris_peer_initial_state::<F>(0);
    let mods = fill_table::<F>(0, &addrs);
    let lookups = generate_random_lookups_sparse::<F>(0, ITERS, &addrs);

    let mut group = c.benchmark_group(group_name);
    group.throughput(Throughput::Elements(lookups.len() as u64));
    bench_all!(group, F, &mods, &lookups);
    group.finish();
}

pub fn bgp_lookup_random(c: &mut Criterion) {
    bgp_lookup_random_for::<Ipv4>(c, "bgp-lookup-random");
}

pub fn bgp_lookup_random_ipv6(c: &mut Criterion) {
    bgp_lookup_random_for::<Ipv6>(c, "bgp-lookup-random-ipv6");
}

fn bgp_lookup_ris_for<F>(c: &mut Criterion, group_name: &str)
where
    F: BenchFamily,
{
    let addrs = ris_peer_initial_state::<F>(0);
    let mods = fill_table::<F>(0, &addrs);
    let mutations = ris_peer_mutations::<F>();
    let lookups = mutations
        .into_iter()
        .map(|x| match x {
            Insn::Insert(addr, len, _) | Insn::Remove(addr, len) | Insn::ExactMatch(addr, len) => {
                Insn::ExactMatch(addr, len)
            }
        })
        .collect::<Vec<_>>();

    let mut group = c.benchmark_group(group_name);
    group.throughput(Throughput::Elements(lookups.len() as u64));
    bench_all!(group, F, &mods, &lookups);
    group.finish();
}

pub fn bgp_lookup_ris(c: &mut Criterion) {
    bgp_lookup_ris_for::<Ipv4>(c, "bgp-lookup-ris");
}

pub fn bgp_lookup_ris_ipv6(c: &mut Criterion) {
    bgp_lookup_ris_for::<Ipv6>(c, "bgp-lookup-ris-ipv6");
}

fn bgp_mods_ris_for<F>(c: &mut Criterion, group_name: &str)
where
    F: BenchFamily,
{
    let addrs = ris_peer_initial_state::<F>(0);
    let initial_table = fill_table::<F>(0, &addrs);
    let mutations = ris_peer_mutations::<F>();

    let mut group = c.benchmark_group(group_name);
    group.throughput(Throughput::Elements(mutations.len() as u64));
    bench_all!(group, F, &initial_table, &mutations);
    group.finish();
}

pub fn bgp_mods_ris(c: &mut Criterion) {
    bgp_mods_ris_for::<Ipv4>(c, "bgp-mods-ris");
}

pub fn bgp_mods_ris_ipv6(c: &mut Criterion) {
    bgp_mods_ris_for::<Ipv6>(c, "bgp-mods-ris-ipv6");
}

/// Created by random order
///
/// This likely is an adverse case for CPU data pre-fetching because there is no pattern
fn bgp_create_random_for<F>(c: &mut Criterion, group_name: &str)
where
    F: BenchFamily,
{
    let addrs = ris_peer_initial_state::<F>(0);
    let inserts = fill_table::<F>(0, &addrs);

    let mut group = c.benchmark_group(group_name);
    group.throughput(Throughput::Elements(inserts.len() as u64));
    bench_all!(group, F, &[], &inserts);
    group.finish();
}

pub fn bgp_create_random(c: &mut Criterion) {
    bgp_create_random_for::<Ipv4>(c, "bgp-create-random");
}

pub fn bgp_create_random_ipv6(c: &mut Criterion) {
    bgp_create_random_for::<Ipv6>(c, "bgp-create-random-ipv6");
}

/// Created ordered by IP address, followed by prefix length
///
/// (default Ord of the tuple)
fn bgp_create_ordered_lexicographic_for<F>(c: &mut Criterion, group_name: &str)
where
    F: BenchFamily,
{
    let addrs = ris_peer_initial_state::<F>(0);
    let sorted_addrs: Vec<_> = addrs.iter().cloned().sorted().collect();
    let inserts = fill_table::<F>(0, &sorted_addrs);

    let mut group = c.benchmark_group(group_name);
    group.throughput(Throughput::Elements(inserts.len() as u64));
    bench_all!(group, F, &[], &inserts);
    group.finish();
}

pub fn bgp_create_ordered_lexicographic(c: &mut Criterion) {
    bgp_create_ordered_lexicographic_for::<Ipv4>(c, "bgp-create-ordered-lexicographic");
}

pub fn bgp_create_ordered_lexicographic_ipv6(c: &mut Criterion) {
    bgp_create_ordered_lexicographic_for::<Ipv6>(c, "bgp-create-ordered-lexicographic-ipv6");
}

fn bgp_create_ordered_adverse_bit_reversed_for<F>(c: &mut Criterion, group_name: &str)
where
    F: BenchFamily,
{
    let addrs = ris_peer_initial_state::<F>(0);
    let sorted_addrs: Vec<_> = addrs
        .iter()
        .cloned()
        .sorted_unstable_by(adverse_cmp::<F>)
        .collect();
    let inserts = fill_table::<F>(0, &sorted_addrs);

    let mut group = c.benchmark_group(group_name);
    group.throughput(Throughput::Elements(inserts.len() as u64));
    bench_all!(group, F, &[], &inserts);
    group.finish();
}

pub fn bgp_create_ordered_adverse_bit_reversed(c: &mut Criterion) {
    bgp_create_ordered_adverse_bit_reversed_for::<Ipv4>(
        c,
        "bgp-create-ordered-adverse-bit-reversed",
    );
}

pub fn bgp_create_ordered_adverse_bit_reversed_ipv6(c: &mut Criterion) {
    bgp_create_ordered_adverse_bit_reversed_for::<Ipv6>(
        c,
        "bgp-create-ordered-adverse-bit-reversed-ipv6",
    );
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
        bgp_mods_random_ipv6,
        bgp_lookup_random,
        bgp_lookup_random_ipv6,
        bgp_mods_ris,
        bgp_mods_ris_ipv6,
        bgp_lookup_ris,
        bgp_lookup_ris_ipv6,
        bgp_create_random,
        bgp_create_random_ipv6,
        bgp_create_ordered_lexicographic,
        bgp_create_ordered_lexicographic_ipv6,
        bgp_create_ordered_adverse_bit_reversed,
        bgp_create_ordered_adverse_bit_reversed_ipv6,
);
criterion_main!(benches);
