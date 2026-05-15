mod common;
use common::*;

use ip_network_table_deps_treebitmap::IpLookupTable;
use ipnet::Ipv4Net;
use prefix_trie::*;
use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicUsize, Ordering};

static ALLOCATED: AtomicUsize = AtomicUsize::new(0);

struct TrackingAllocator;

unsafe impl std::alloc::GlobalAlloc for TrackingAllocator {
    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        ALLOCATED.fetch_add(layout.size(), Ordering::Relaxed);
        unsafe { std::alloc::System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: std::alloc::Layout) {
        ALLOCATED.fetch_sub(layout.size(), Ordering::Relaxed);
        unsafe { std::alloc::System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: TrackingAllocator = TrackingAllocator;

fn measure_alloc<T>(f: impl FnOnce() -> T) -> (T, usize) {
    let before = ALLOCATED.load(Ordering::Relaxed);
    let val = f();
    let after = ALLOCATED.load(Ordering::Relaxed);
    (val, after - before)
}

#[test]
fn dense_memory_usage() {
    let addrs = ris_peer_initial_state(0);
    let mods = fill_table(0, &addrs);

    let (m, prefixmap_mem) = measure_alloc(|| {
        let mut m = PrefixMap::new();
        execute(&mut m, &mods);
        m
    });

    let (_, prefixset_mem) = measure_alloc(|| m.iter().map(|(p, _)| p).collect::<PrefixSet<_>>());

    let (_, treebitmap_mem) = measure_alloc(|| {
        let mut m = IpLookupTable::new();
        execute(&mut m, &mods);
        m
    });

    let (_, hashmap_mem) = measure_alloc(|| {
        let mut m: HashMap<Ipv4Net, u32> = HashMap::new();
        execute(&mut m, &mods);
        m
    });

    let (_, btreemap_mem) = measure_alloc(|| {
        let mut m: BTreeMap<Ipv4Net, u32> = BTreeMap::new();
        execute(&mut m, &mods);
        m
    });

    println!("elements:   {}", addrs.len());
    println!(
        "PrefixSet:  {:.3} mB",
        prefixset_mem as f64 / 1024.0 / 1024.0
    );
    println!(
        "PrefixMap:  {:.3} mB",
        prefixmap_mem as f64 / 1024.0 / 1024.0
    );
    println!(
        "TreeBitMap: {:.3} mB",
        treebitmap_mem as f64 / 1024.0 / 1024.0
    );
    println!("HashMap:    {:.3} mB", hashmap_mem as f64 / 1024.0 / 1024.0);
    println!(
        "BTreeMap:   {:.3} mB",
        btreemap_mem as f64 / 1024.0 / 1024.0
    );
}
