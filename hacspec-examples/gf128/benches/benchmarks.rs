#[macro_use]
extern crate criterion;
use criterion::{BatchSize, Criterion};

use hacspec_dev::rand::random_byte_vec;
use hacspec_gf128::*;
use hacspec_lib::prelude::*;

fn benchmark(c: &mut Criterion) {
    c.bench_function("GCM", |b| {
        b.iter_batched(
            || {
                let key = Gf128Key::from_public_slice(&random_byte_vec(16));
                let data = ByteSeq::from_public_slice(&random_byte_vec(1_000));
                (data, key)
            },
            |(data, key)| {
                let _tag = gmac(&data, key);
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
