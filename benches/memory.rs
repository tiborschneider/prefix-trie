mod common;
use common::*;

use ip_network_table_deps_treebitmap::IpLookupTable;
use prefix_trie::*;

#[test]
fn dense_memory_usage() {
    let addrs = ris_peer_initial_state();
    let mods = fill_table(9, &addrs);
    let mut prefix_map = PrefixMap::new();
    let mut treebitmap = IpLookupTable::new();
    execute_prefix_map(&mut prefix_map, &mods);
    execute_treebitmap(&mut treebitmap, &mods);

    let prefix_map_with_prefixes: PrefixMap<_, _> =
        prefix_map.iter().map(|(p, v)| (p, (p, *v))).collect();
    let prefix_set: PrefixSet<_> = prefix_map.iter().map(|(p, _)| p).collect();

    println!("elements:       {}", prefix_map_with_prefixes.len());
    println!(
        "PrefixSet:  {:.3} mB",
        prefix_set.mem_size() as f64 / 1024.0 / 1024.0
    );
    println!(
        "PrefixMap:  {:.3} mB",
        prefix_map.mem_size() as f64 / 1024.0 / 1024.0
    );
    println!(
        "PrefixMap+: {:.3} mB (with stored prefixes)",
        prefix_map_with_prefixes.mem_size() as f64 / 1024.0 / 1024.0
    );
    let treebitmap_mem = treebitmap.mem_usage();
    let treebitmap_mem = treebitmap_mem.0 + treebitmap_mem.1;
    println!(
        "TreeBitMap: {:.3} mB",
        treebitmap_mem as f64 / 1024.0 / 1024.0
    );
}
