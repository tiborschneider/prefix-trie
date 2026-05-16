#[path = "../common.rs"]
mod common;

use common::{adverse_cmp, Ipv4, Ipv6};
use std::cmp::Ordering;
use std::net::Ipv4Addr;

#[test]
fn adverse_cmp_orders_ipv4_by_reversed_address_bits_after_prefix_length() {
    assert_eq!(
        adverse_cmp::<Ipv4>(
            &(Ipv4Addr::new(127, 0, 0, 1), 8),
            &(Ipv4Addr::new(127, 0, 0, 255), 8)
        ),
        Ordering::Less
    );
}

#[test]
fn adverse_cmp_orders_ipv4_by_prefix_length_first() {
    assert_eq!(
        adverse_cmp::<Ipv4>(
            &(Ipv4Addr::new(127, 0, 0, 1), 24),
            &(Ipv4Addr::new(127, 0, 0, 1), 8)
        ),
        Ordering::Greater
    );
}

#[test]
fn adverse_cmp_orders_ipv6_by_reversed_address_bits_after_prefix_length() {
    assert_eq!(
        adverse_cmp::<Ipv6>(
            &("2001:db8::1".parse().unwrap(), 32),
            &("2001:db8::ff".parse().unwrap(), 32)
        ),
        Ordering::Less
    );
}

#[test]
fn adverse_cmp_orders_ipv6_by_prefix_length_first() {
    assert_eq!(
        adverse_cmp::<Ipv6>(
            &("2001:db8::1".parse().unwrap(), 48),
            &("2001:db8::1".parse().unwrap(), 32)
        ),
        Ordering::Greater
    );
}
