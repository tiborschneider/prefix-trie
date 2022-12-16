use criterion::{criterion_group, criterion_main, Criterion};
use ipnet::Ipv4Net;
use prefixmap::*;
use rand::prelude::*;

fn do_random_inserts() {
    let mut pm = PrefixMap::<Ipv4Net, u32>::new();

    let mut rng = thread_rng();

    for _ in 0..1_000 {
        let addr: u32 = (rng.gen::<u32>()) & 0xfff00000;
        let prefix = Ipv4Net::new(addr.into(), rng.gen_range(1..=12)).unwrap();
        let prefix = Ipv4Net::new(prefix.mask().into(), prefix.prefix_len()).unwrap();

        let value: u32 = rng.gen::<u8>() as u32;
        pm.insert(prefix, value);
    }
}

pub fn random_inserts(c: &mut Criterion) {
    c.bench_function("randomized inserts", |b| b.iter(do_random_inserts));
}

criterion_group!(benches, random_inserts);
criterion_main!(benches);
