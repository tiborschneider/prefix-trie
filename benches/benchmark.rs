mod common;
use common::*;

const ITERS: usize = 100_000;

use criterion::{criterion_group, criterion_main, Criterion};
use ip_network_table_deps_treebitmap::IpLookupTable;
use prefix_trie::*;
use std::collections::HashSet;

pub fn random_mods(c: &mut Criterion) {
    let mut group = c.benchmark_group("random-mods");

    let (insn, _) = generate_random_mods_dense(1, ITERS);

    group.bench_function("PrefixMap", |b| {
        b.iter(|| {
            let mut map = PrefixMap::new();
            execute_dense_prefix_map(&mut map, &insn);
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

pub fn random_lookup(c: &mut Criterion) {
    let (mods, addrs) = generate_random_mods_dense(1, ITERS);
    let lookups = generate_random_lookups_dense(2, ITERS, &addrs);

    let mut prefix_map = PrefixMap::new();
    let mut treebitmap = IpLookupTable::new();
    execute_prefix_map(&mut prefix_map, &mods);
    execute_treebitmap(&mut treebitmap, &mods);

    let mut group = c.benchmark_group("random-lookups");

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

pub fn bgp_mods(c: &mut Criterion) {
    let mut group = c.benchmark_group("bgp-mods");

    let addrs = bgp_ipv4_prefixes();
    let setup = fill_table(9, &addrs);
    let insn = generate_random_mods_sparse(8, ITERS, &addrs);

    let mut prefix_map = PrefixMap::new();
    let mut treebitmap = IpLookupTable::new();
    execute_prefix_map(&mut prefix_map, &setup);
    execute_treebitmap(&mut treebitmap, &setup);

    group.bench_function("PrefixMap", |b| {
        b.iter(|| {
            execute_prefix_map(&mut prefix_map, &insn);
        })
    });
    group.bench_function("TreeBitMap", |b| {
        b.iter(|| {
            execute_treebitmap(&mut treebitmap, &insn);
        })
    });

    group.finish();
}

pub fn bgp_lookup(c: &mut Criterion) {
    let mut group = c.benchmark_group("bgp-lookups");

    let addrs = bgp_ipv4_prefixes();
    let mods = fill_table(9, &addrs);
    let lookups = generate_random_lookups_sparse(10, ITERS, &addrs);

    let mut prefix_map = PrefixMap::new();
    let mut treebitmap = IpLookupTable::new();
    execute_prefix_map(&mut prefix_map, &mods);
    execute_treebitmap(&mut treebitmap, &mods);

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
        .measurement_time(std::time::Duration::from_secs(10))
        .with_profiler(MyProfiler::default());
    targets = bgp_lookup, bgp_mods, random_lookup, random_mods,
);
criterion_main!(benches);
