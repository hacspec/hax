#[macro_use]
extern crate criterion;
use criterion::{BatchSize, Criterion};

use hacspec_curve25519::*;
use hacspec_dev::rand::random_byte_vec;

fn benchmark(c: &mut Criterion) {
    c.bench_function("x25519", |b| {
        b.iter_batched(
            || {
                let s = X25519SerializedScalar::from_public_slice(&random_byte_vec(32));
                let u = X25519SerializedPoint::from_public_slice(&random_byte_vec(32));
                (s, u)
            },
            |(s, u)| {
                let _r = x25519_scalarmult(s, u);
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
