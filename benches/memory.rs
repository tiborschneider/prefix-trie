mod common;
use common::*;

use ipnet::{Ipv4Net, Ipv6Net};
use prefix_trie::*;
use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

static ALLOCATED: AtomicUsize = AtomicUsize::new(0);
static MEASURE_LOCK: Mutex<()> = Mutex::new(());

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

fn memory_usage_for<P>(family: &str)
where
    P: Prefix + Copy + Eq + Ord + std::hash::Hash + DataSampler,
{
    let _guard = MEASURE_LOCK.lock().unwrap();
    let addrs = P::ris_peer_initial_state(0, SortingOrder::Random);
    let insns = fill_table(0, &addrs);

    let (m, prefixmap_mem) = measure_alloc(|| {
        let mut m = PrefixMap::<P, u32>::new();
        m.run(&insns);
        m
    });

    let (_, prefixset_mem) = measure_alloc(|| m.iter().map(|(p, _)| p).collect::<PrefixSet<_>>());

    let (_, treebitmap_mem) = measure_alloc(|| {
        let mut m = P::IpLookupTable::new_empty();
        m.run(&insns);
        m
    });

    let (_, hashmap_mem) = measure_alloc(|| {
        let mut m = HashMap::<P, u32>::new();
        m.run(&insns);
        m
    });

    let (_, btreemap_mem) = measure_alloc(|| {
        let mut m = BTreeMap::<P, u32>::new();
        m.run(&insns);
        m
    });

    let mb = |bytes: usize| bytes as f64 / 1024.0 / 1024.0;
    println!();
    println!("family:     {family}");
    println!("elements:   {}", addrs.len());
    println!("PrefixSet:  {:.3} mB", mb(prefixset_mem));
    println!("PrefixMap:  {:.3} mB", mb(prefixmap_mem));
    println!("TreeBitMap: {:.3} mB", mb(treebitmap_mem));
    println!("HashMap:    {:.3} mB", mb(hashmap_mem));
    println!("BTreeMap:   {:.3} mB", mb(btreemap_mem));
}

#[test]
fn memory_usage() {
    memory_usage_for::<Ipv4Net>("Ipv4");
    memory_usage_for::<Ipv6Net>("Ipv6");
}
