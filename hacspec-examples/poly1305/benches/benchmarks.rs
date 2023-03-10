#[macro_use]
extern crate criterion;
use criterion::{BatchSize, Criterion};

use hacspec_dev::rand::random_byte_vec;
use hacspec_lib::prelude::*;
use hacspec_poly1305::*;

fn benchmark(c: &mut Criterion) {
    c.bench_function("Poly1305", |b| {
        b.iter_batched(
            || {
                let key = PolyKey::from_public_slice(&random_byte_vec(32));
                let data = Seq::<U8>::from_public_slice(&random_byte_vec(1_000));
                (data, key)
            },
            |(data, key)| {
                let _tag = poly1305(&data, key);
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
