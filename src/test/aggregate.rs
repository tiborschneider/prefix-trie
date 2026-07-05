#[generic_tests::define]
mod t {
    use super::super::*;

    #[test]
    fn set_aggregate_merges_siblings<P: Prefix + Copy + PartialEq>() {
        let mut set = PrefixSet::<P>::from_iter([ip("10.0.0.0/24"), ip("10.0.1.0/24")]);
        set.aggregate();
        assert_eq!(Vec::from_iter(&set), vec![ip("10.0.0.0/23")]);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn set_aggregate_cascades_four_into_one<P: Prefix + Copy + PartialEq>() {
        let mut set = PrefixSet::<P>::from_iter([
            ip("10.0.0.0/24"),
            ip("10.0.1.0/24"),
            ip("10.0.2.0/24"),
            ip("10.0.3.0/24"),
        ]);
        set.aggregate();
        assert_eq!(Vec::from_iter(&set), vec![ip("10.0.0.0/22")]);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn set_aggregate_drops_covered<P: Prefix + Copy + PartialEq>() {
        let mut set =
            PrefixSet::<P>::from_iter([ip("10.0.0.0/16"), ip("10.0.1.0/24"), ip("10.0.128.0/20")]);
        set.aggregate();
        assert_eq!(Vec::from_iter(&set), vec![ip("10.0.0.0/16")]);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn set_aggregate_merges_across_node_boundary<P: Prefix + Copy + PartialEq>() {
        // /10 and /11 siblings span the K=5 node boundary at depth 10, so the merge must travel
        // up through a child pointer rather than within a single node.
        let mut set = PrefixSet::<P>::from_iter([ip("10.0.0.0/11"), ip("10.32.0.0/11")]);
        set.aggregate();
        assert_eq!(Vec::from_iter(&set), vec![ip("10.0.0.0/10")]);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn set_aggregate_keeps_unmergeable_siblings<P: Prefix + Copy + PartialEq>() {
        // Only one half of each potential parent is present, so nothing merges or drops.
        let original = [ip("10.0.0.0/24"), ip("10.0.2.0/24"), ip("10.1.0.0/16")];
        let mut set = PrefixSet::<P>::from_iter(original);
        set.aggregate();
        assert_eq!(Vec::from_iter(&set), Vec::from(original));
        assert_eq!(set.len(), 3);
    }

    #[test]
    fn set_aggregate_empty_is_noop<P: Prefix + Copy + PartialEq>() {
        let mut set = PrefixSet::<P>::new();
        set.aggregate();
        assert!(set.is_empty());
    }

    #[test]
    fn set_aggregate_collapses_to_default_route<P: Prefix + Copy + PartialEq>() {
        // The two halves of the whole space merge all the way up to the default route.
        let mut set = PrefixSet::<P>::from_iter([ip("0.0.0.0/1"), ip("128.0.0.0/1")]);
        set.aggregate();
        assert_eq!(Vec::from_iter(&set), vec![ip("0.0.0.0/0")]);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn set_aggregate_is_idempotent<P: Prefix + Copy + PartialEq>() {
        let mut set = PrefixSet::<P>::from_iter([
            ip("10.0.0.0/24"),
            ip("10.0.1.0/24"),
            ip("10.0.2.0/23"),
            ip("10.0.4.0/23"),
            ip("10.0.5.0/24"),
        ]);
        set.aggregate();
        let once = Vec::from_iter(&set);
        set.aggregate();
        assert_eq!(Vec::from_iter(&set), once);
    }

    #[test]
    fn set_aggregate_consistent_drops_covered<P: Prefix + Copy + PartialEq>() {
        // A member covered by a less-specific member is redundant and is dropped.
        let mut set = PrefixSet::<P>::from_iter([ip("10.0.0.0/16"), ip("10.0.1.0/24")]);
        set.aggregate_consistent();
        assert_eq!(Vec::from_iter(&set), vec![ip("10.0.0.0/16")]);
        assert_eq!(set.len(), 1);
        assert!(set.0.check_memory_alloc());
    }

    #[test]
    fn set_aggregate_consistent_keeps_siblings<P: Prefix + Copy + PartialEq>() {
        // Unlike `aggregate`, drop-only must NOT merge sibling prefixes.
        let original = [ip("10.0.0.0/24"), ip("10.0.1.0/24")];
        let mut set = PrefixSet::<P>::from_iter(original);
        set.aggregate_consistent();
        assert_eq!(Vec::from_iter(&set), Vec::from(original));
        assert_eq!(set.len(), 2);
        assert!(set.0.check_memory_alloc());
    }

    #[test]
    fn set_aggregate_consistent_drops_chain<P: Prefix + Copy + PartialEq>() {
        let mut set =
            PrefixSet::<P>::from_iter([ip("10.0.0.0/8"), ip("10.0.0.0/16"), ip("10.0.0.0/24")]);
        set.aggregate_consistent();
        assert_eq!(Vec::from_iter(&set), vec![ip("10.0.0.0/8")]);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn set_aggregate_consistent_drops_across_node_boundary<P: Prefix + Copy + PartialEq>() {
        // /8 (a depth-5 node) covers /11 (a depth-10 node): the coverage crosses a node boundary.
        let mut set = PrefixSet::<P>::from_iter([ip("10.0.0.0/8"), ip("10.0.0.0/11")]);
        set.aggregate_consistent();
        assert_eq!(Vec::from_iter(&set), vec![ip("10.0.0.0/8")]);
        assert_eq!(set.len(), 1);
        assert!(set.0.check_memory_alloc());
    }

    #[test]
    fn set_aggregate_consistent_keeps_uncovered<P: Prefix + Copy + PartialEq>() {
        // Nothing covers anything else here; the set is unchanged.
        let original = [ip("10.0.0.0/24"), ip("10.0.2.0/24"), ip("10.1.0.0/16")];
        let mut set = PrefixSet::<P>::from_iter(original);
        set.aggregate_consistent();
        assert_eq!(Vec::from_iter(&set), Vec::from(original));
        assert_eq!(set.len(), 3);
    }

    #[test]
    fn set_aggregate_consistent_empty_is_noop<P: Prefix + Copy + PartialEq>() {
        let mut set = PrefixSet::<P>::new();
        set.aggregate_consistent();
        assert!(set.is_empty());
    }

    #[test]
    fn set_aggregate_consistent_preserves_lpm_presence<P: Prefix + Copy + PartialEq>() {
        let entries = [
            ip("10.0.0.0/8"),
            ip("10.0.0.0/16"),
            ip("10.0.5.0/24"),
            ip("10.0.8.0/23"),
            ip("11.0.0.0/24"),
        ];
        let original = PrefixSet::<P>::from_iter(entries);
        let mut set = original.clone();
        set.aggregate_consistent();
        // `get_lpm` presence (Some/None) must be unchanged for every probed prefix.
        let probes = [
            ip("10.0.0.0/8"),
            ip("10.0.0.0/16"),
            ip("10.0.5.0/24"),
            ip("10.0.5.128/25"),
            ip("10.0.8.0/23"),
            ip("10.0.9.0/24"),
            ip("11.0.0.0/24"),
            ip("9.0.0.0/8"),
            ip("12.0.0.0/8"),
        ];
        for p in probes {
            assert_eq!(
                set.get_lpm(&p).is_some(),
                original.get_lpm(&p).is_some(),
                "lpm presence changed for {p:?}",
            );
        }
        assert!(set.0.check_memory_alloc());
    }

    #[test]
    fn set_aggregate_consistent_is_idempotent<P: Prefix + Copy + PartialEq>() {
        let mut set = PrefixSet::<P>::from_iter([
            ip("10.0.0.0/8"),
            ip("10.0.0.0/16"),
            ip("10.0.1.0/24"),
            ip("10.1.0.0/16"),
        ]);
        set.aggregate_consistent();
        let once = Vec::from_iter(&set);
        set.aggregate_consistent();
        assert_eq!(Vec::from_iter(&set), once);
    }

    #[test]
    fn map_aggregate_consistent_drops_same_value_descendant<P: Prefix + Copy + PartialEq>() {
        // A more specific entry with the same value as its covering entry is redundant.
        let mut map = Map::<P>::from_iter([(ip("10.0.0.0/16"), 1), (ip("10.0.1.0/24"), 1)]);
        map.aggregate_consistent();
        assert_eq!(Vec::from_iter(&map), vec![(ip("10.0.0.0/16"), &1)]);
        assert_eq!(map.len(), 1);
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_consistent_keeps_diff_value_descendant<P: Prefix + Copy + PartialEq>() {
        // A more specific entry with a different value is a real exception and is kept.
        let original = [(ip("10.0.0.0/16"), 1), (ip("10.0.1.0/24"), 2)];
        let mut map = Map::<P>::from_iter(original);
        map.aggregate_consistent();
        assert_eq!(
            Vec::from_iter(&map),
            vec![(ip("10.0.0.0/16"), &1), (ip("10.0.1.0/24"), &2)]
        );
    }

    #[test]
    fn map_aggregate_consistent_keeps_equal_siblings<P: Prefix + Copy + PartialEq>() {
        // Drop-only never merges, even when sibling values are equal.
        let original = [(ip("10.0.0.0/24"), 1), (ip("10.0.1.0/24"), 1)];
        let mut map = Map::<P>::from_iter(original);
        map.aggregate_consistent();
        assert_eq!(
            Vec::from_iter(&map),
            vec![(ip("10.0.0.0/24"), &1), (ip("10.0.1.0/24"), &1)]
        );
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn map_aggregate_consistent_drops_chain<P: Prefix + Copy + PartialEq>() {
        let mut map = Map::<P>::from_iter([
            (ip("10.0.0.0/8"), 1),
            (ip("10.0.0.0/16"), 1),
            (ip("10.0.0.0/24"), 1),
        ]);
        map.aggregate_consistent();
        assert_eq!(Vec::from_iter(&map), vec![(ip("10.0.0.0/8"), &1)]);
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn map_aggregate_consistent_chain_mixed_values<P: Prefix + Copy + PartialEq>() {
        // /16 differs from its covering /8 -> kept. /24 equals its covering /16 -> dropped.
        let mut map = Map::<P>::from_iter([
            (ip("10.0.0.0/8"), 1),
            (ip("10.0.0.0/16"), 2),
            (ip("10.0.0.0/24"), 2),
        ]);
        map.aggregate_consistent();
        assert_eq!(
            Vec::from_iter(&map),
            vec![(ip("10.0.0.0/8"), &1), (ip("10.0.0.0/16"), &2)]
        );
        assert_eq!(map.len(), 2);
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_consistent_across_node_boundary<P: Prefix + Copy + PartialEq>() {
        // /8 (depth-5 node) covers /11 (depth-10 node). Same value -> dropped.
        let mut same = Map::<P>::from_iter([(ip("10.0.0.0/8"), 5), (ip("10.0.0.0/11"), 5)]);
        same.aggregate_consistent();
        assert_eq!(Vec::from_iter(&same), vec![(ip("10.0.0.0/8"), &5)]);
        assert!(same.check_memory_alloc());

        // Different value across the boundary -> both kept.
        let mut diff = Map::<P>::from_iter([(ip("10.0.0.0/8"), 5), (ip("10.0.0.0/11"), 6)]);
        diff.aggregate_consistent();
        assert_eq!(
            Vec::from_iter(&diff),
            vec![(ip("10.0.0.0/8"), &5), (ip("10.0.0.0/11"), &6)]
        );
    }

    #[test]
    fn map_aggregate_consistent_empty_is_noop<P: Prefix + Copy + PartialEq>() {
        let mut map = Map::<P>::new();
        map.aggregate_consistent();
        assert!(map.is_empty());
    }

    #[test]
    fn map_aggregate_consistent_preserves_lpm<P: Prefix + Copy + PartialEq>() {
        let entries = [
            (ip("10.0.0.0/8"), 1),
            (ip("10.0.0.0/16"), 1), // redundant (same as /8)
            (ip("10.0.5.0/24"), 2), // exception
            (ip("10.0.8.0/23"), 1), // redundant (same as /8)
            (ip("11.0.0.0/24"), 3),
        ];
        let original = Map::<P>::from_iter(entries);
        let mut map = original.clone();
        map.aggregate_consistent();

        // `get_lpm` must return the same *value* (and Some/None) for every probed prefix.
        let probes = [
            ip("10.0.0.0/8"),
            ip("10.0.0.0/16"),
            ip("10.0.5.0/24"),
            ip("10.0.5.128/25"),
            ip("10.0.8.0/23"),
            ip("10.0.9.0/24"),
            ip("11.0.0.0/24"),
            ip("10.255.255.255/32"),
            ip("9.0.0.0/32"),
            ip("12.0.0.0/32"),
        ];
        for p in probes {
            assert_eq!(
                map.get_lpm(&p).map(|(_, v)| *v),
                original.get_lpm(&p).map(|(_, v)| *v),
                "lpm value changed for {p:?}",
            );
        }
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_consistent_is_idempotent<P: Prefix + Copy + PartialEq>() {
        let mut map = Map::<P>::from_iter([
            (ip("10.0.0.0/8"), 1),
            (ip("10.0.0.0/16"), 1),
            (ip("10.0.1.0/24"), 2),
            (ip("10.1.0.0/16"), 3),
        ]);
        map.aggregate_consistent();
        let once = Vec::from_iter(map.iter().map(|(p, v)| (p, *v)));
        map.aggregate_consistent();
        assert_eq!(Vec::from_iter(map.iter().map(|(p, v)| (p, *v))), once);
    }

    #[test]
    fn map_aggregate_merges_equal_value_siblings<P: Prefix + Copy + PartialEq>() {
        let mut map = Map::<P>::from_iter([(ip("10.0.0.0/24"), 1u32), (ip("10.0.1.0/24"), 1)]);
        map.aggregate();
        assert_eq!(
            Vec::from_iter(map.iter().map(|(p, v)| (p, *v))),
            vec![(ip("10.0.0.0/23"), 1)]
        );
        assert_eq!(map.len(), 1);
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_keeps_diff_value_siblings<P: Prefix + Copy + PartialEq>() {
        let original = [(ip("10.0.0.0/24"), 1u32), (ip("10.0.1.0/24"), 2)];
        let mut map = Map::<P>::from_iter(original);
        map.aggregate();
        assert_eq!(
            Vec::from_iter(map.iter().map(|(p, v)| (p, *v))),
            vec![(ip("10.0.0.0/23"), 1), (ip("10.0.1.0/24"), 2)]
        );
    }

    #[test]
    fn map_aggregate_keeps_hole<P: Prefix + Copy + PartialEq>() {
        // One sibling is absent (hole). Merging would cover uncovered space, so no merge.
        let mut map = Map::<P>::from_iter([(ip("10.0.0.0/24"), 1u32)]);
        map.aggregate();
        assert_eq!(
            Vec::from_iter(map.iter().map(|(p, v)| (p, *v))),
            vec![(ip("10.0.0.0/24"), 1)]
        );
        // The absent sibling stays uncovered.
        assert_eq!(map.get_lpm(&ip("10.0.1.0/32")), None);
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_drops_covered_same_value<P: Prefix + Copy + PartialEq>() {
        let mut map = Map::<P>::from_iter([(ip("10.0.0.0/8"), 1u32), (ip("10.0.0.0/16"), 1)]);
        map.aggregate();
        assert_eq!(
            Vec::from_iter(map.iter().map(|(p, v)| (p, *v))),
            vec![(ip("10.0.0.0/8"), 1)]
        );
        assert_eq!(map.len(), 1);
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_keeps_diff_value_descendant<P: Prefix + Copy + PartialEq>() {
        let original = [(ip("10.0.0.0/8"), 1u32), (ip("10.0.0.0/16"), 2)];
        let mut map = Map::<P>::from_iter(original);
        map.aggregate();
        assert_eq!(
            Vec::from_iter(map.iter().map(|(p, v)| (p, *v))),
            vec![(ip("10.0.0.0/8"), 1), (ip("10.0.0.0/16"), 2)]
        );
    }

    #[test]
    fn map_aggregate_merges_across_node_boundary<P: Prefix + Copy + PartialEq>() {
        // /11 siblings span the K=5 node boundary at depth 10.
        let mut map = Map::<P>::from_iter([(ip("10.0.0.0/11"), 1u32), (ip("10.32.0.0/11"), 1)]);
        map.aggregate();
        assert_eq!(
            Vec::from_iter(map.iter().map(|(p, v)| (p, *v))),
            vec![(ip("10.0.0.0/10"), 1)]
        );
        assert_eq!(map.len(), 1);
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_cascades<P: Prefix + Copy + PartialEq>() {
        // Four /25 leaves of the same value cascade into /23.
        let mut map = Map::<P>::from_iter([
            (ip("10.0.0.0/25"), 1u32),
            (ip("10.0.0.128/25"), 1),
            (ip("10.0.1.0/25"), 1),
            (ip("10.0.1.128/25"), 1),
        ]);
        map.aggregate();
        assert_eq!(
            Vec::from_iter(map.iter().map(|(p, v)| (p, *v))),
            vec![(ip("10.0.0.0/23"), 1)]
        );
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn map_aggregate_merges_with_exception<P: Prefix + Copy + PartialEq>() {
        // combine({Some(1)}, {Some(1),Some(2)}) = {Some(1)} (non-empty intersection),
        // so ORTC emits /23=1 and keeps only the /25=2 exception.
        let mut map = Map::<P>::from_iter([
            (ip("10.0.0.0/24"), 1u32),
            (ip("10.0.1.0/25"), 1),
            (ip("10.0.1.128/25"), 2),
        ]);
        map.aggregate();
        assert_eq!(
            Vec::from_iter(map.iter().map(|(p, v)| (p, *v))),
            vec![(ip("10.0.0.0/23"), 1), (ip("10.0.1.128/25"), 2)]
        );
        assert_eq!(map.len(), 2);
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_empty_is_noop<P: Prefix + Copy + PartialEq>() {
        let mut map = Map::<P>::new();
        map.aggregate();
        assert!(map.is_empty());
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_preserves_lpm<P: Prefix + Copy + PartialEq>() {
        let entries = [
            (ip("10.0.0.0/8"), 1u32),
            (ip("10.0.0.0/16"), 1),
            (ip("10.0.5.0/24"), 2),
            (ip("10.0.8.0/23"), 1),
            (ip("11.0.0.0/24"), 3),
        ];
        let original = Map::<P>::from_iter(entries);
        let mut map = original.clone();
        map.aggregate();

        let probes = [
            ip("10.0.0.0/8"),
            ip("10.0.0.0/16"),
            ip("10.0.5.0/24"),
            ip("10.0.5.128/25"),
            ip("10.0.8.0/23"),
            ip("11.0.0.0/24"),
            ip("10.255.255.255/32"),
            ip("9.0.0.0/32"),
        ];
        for p in probes {
            assert_eq!(
                map.get_lpm(&p).map(|(_, v)| *v),
                original.get_lpm(&p).map(|(_, v)| *v),
                "lpm changed for {p:?}",
            );
        }
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_is_idempotent<P: Prefix + Copy + PartialEq>() {
        let mut map = Map::<P>::from_iter([
            (ip("10.0.0.0/24"), 1u32),
            (ip("10.0.1.0/24"), 1),
            (ip("10.0.2.0/24"), 2),
            (ip("10.0.3.0/24"), 2),
            (ip("10.1.0.0/16"), 1),
        ]);
        map.aggregate();
        let once = Vec::from_iter(map.iter().map(|(p, v)| (p, *v)));
        map.aggregate();
        assert_eq!(Vec::from_iter(map.iter().map(|(p, v)| (p, *v))), once);
    }

    #[test]
    fn map_aggregate_fill_empty_makes_default_route<P: Prefix + Copy + PartialEq>() {
        // Filling an empty map covers the whole space with the default: one default route.
        let mut map = Map::<P>::new();
        map.aggregate_fill(|| 5);
        assert_eq!(
            Vec::from_iter(map.iter().map(|(p, v)| (p, *v))),
            vec![(ip("0.0.0.0/0"), 5)]
        );
        assert_eq!(map.len(), 1);
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_fill_adds_default_over_covered<P: Prefix + Copy + PartialEq>() {
        // A default value that differs from the covered one adds a default route beside it.
        let mut map = Map::<P>::from_iter([(ip("10.0.0.0/8"), 1u32)]);
        map.aggregate_fill(|| 9);
        assert_eq!(
            Vec::from_iter(map.iter().map(|(p, v)| (p, *v))),
            vec![(ip("0.0.0.0/0"), 9), (ip("10.0.0.0/8"), 1)]
        );
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_fill_collapses_when_default_matches<P: Prefix + Copy + PartialEq>() {
        // The default equals every covered value, so the whole space becomes one default route.
        let mut map = Map::<P>::from_iter([(ip("10.0.0.0/8"), 1u32), (ip("192.168.0.0/16"), 1)]);
        map.aggregate_fill(|| 1);
        assert_eq!(
            Vec::from_iter(map.iter().map(|(p, v)| (p, *v))),
            vec![(ip("0.0.0.0/0"), 1)]
        );
        assert_eq!(map.len(), 1);
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_fill_merge_and_collapse<P: Prefix + Copy + PartialEq>() {
        // Siblings merge into a /23; the gaps and both /16 branches collapse into /0 = 1.
        let mut map = Map::<P>::from_iter([
            (ip("10.0.0.0/16"), 1u32),
            (ip("10.0.0.0/24"), 2),
            (ip("10.0.1.0/24"), 2),
            (ip("10.0.2.0/24"), 1),
            (ip("192.168.0.0/16"), 1),
        ]);
        map.aggregate_fill(|| 1);
        assert_eq!(
            Vec::from_iter(map.iter().map(|(p, v)| (p, *v))),
            vec![(ip("0.0.0.0/0"), 1), (ip("10.0.0.0/23"), 2)]
        );
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_fill_keeps_distinct_values<P: Prefix + Copy + PartialEq>() {
        // Distinct-valued entries survive beside the default route; nothing merges. The /30 has a
        // default-valued sibling, so unlike a /24 (whose sibling is the /24=2) it is not promoted.
        let mut map = Map::<P>::from_iter([
            (ip("10.0.0.0/30"), 1u32),
            (ip("10.0.1.0/24"), 2),
            (ip("10.1.0.0/16"), 3),
        ]);
        map.aggregate_fill_default();
        assert_eq!(
            Vec::from_iter(map.iter().map(|(p, v)| (p, *v))),
            vec![
                (ip("0.0.0.0/0"), 0),
                (ip("10.0.0.0/30"), 1),
                (ip("10.0.1.0/24"), 2),
                (ip("10.1.0.0/16"), 3),
            ]
        );
        assert!(map.check_memory_alloc());
    }

    #[test]
    fn map_aggregate_fill_is_idempotent<P: Prefix + Copy + PartialEq>() {
        let mut map = Map::<P>::from_iter([
            (ip("10.0.0.0/24"), 1u32),
            (ip("10.0.1.0/24"), 2),
            (ip("10.1.0.0/16"), 3),
        ]);
        map.aggregate_fill_default();
        let once = Vec::from_iter(map.iter().map(|(p, v)| (p, *v)));
        map.aggregate_fill_default();
        assert_eq!(Vec::from_iter(map.iter().map(|(p, v)| (p, *v))), once);
    }

    #[test]
    fn map_aggregate_fill_default_uses_zero<P: Prefix + Copy + PartialEq>() {
        // `aggregate_fill_default` fills with `T::default()`, i.e. `0` for `u32`.
        let mut map = Map::<P>::from_iter([(ip("10.0.0.0/8"), 1u32)]);
        map.aggregate_fill_default();
        assert_eq!(
            Vec::from_iter(map.iter().map(|(p, v)| (p, *v))),
            vec![(ip("0.0.0.0/0"), 0), (ip("10.0.0.0/8"), 1)]
        );
        assert!(map.check_memory_alloc());
    }

    #[instantiate_tests(<(u32, u8)>)]
    mod raw32 {}

    #[instantiate_tests(<(u64, u8)>)]
    mod raw64 {}

    #[instantiate_tests(<(u128, u8)>)]
    mod raw128 {}

    #[cfg(feature = "ipnet")]
    #[instantiate_tests(<ipnet::Ipv4Net>)]
    mod ipv4net {}

    #[cfg(feature = "ipnet")]
    #[instantiate_tests(<ipnet::Ipv6Net>)]
    mod ipv6net {}

    #[cfg(feature = "ipnetwork")]
    #[instantiate_tests(<ipnetwork::Ipv4Network>)]
    mod ipv4network {}

    #[cfg(feature = "ipnetwork")]
    #[instantiate_tests(<ipnetwork::Ipv6Network>)]
    mod ipv6network {}

    #[cfg(feature = "cidr")]
    #[instantiate_tests(<cidr::Ipv4Cidr>)]
    mod ipv4cidr {}

    #[cfg(feature = "cidr")]
    #[instantiate_tests(<cidr::Ipv6Cidr>)]
    mod ipv6cidr {}

    #[cfg(feature = "cidr")]
    #[instantiate_tests(<cidr::Ipv4Inet>)]
    mod ipv4inet {}

    #[cfg(feature = "cidr")]
    #[instantiate_tests(<cidr::Ipv6Inet>)]
    mod ipv6inet {}
}
