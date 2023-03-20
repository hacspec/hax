#[macro_use]
extern crate criterion;
use criterion::{BatchSize, Criterion};

use hacspec_chacha20::*;
use hacspec_dev::rand::random_byte_vec;
use hacspec_lib::prelude::*;

fn benchmark(c: &mut Criterion) {
    c.bench_function("ChaCha20", |b| {
        b.iter_batched(
            || {
                let key = ChaChaKey::from_public_slice(&random_byte_vec(32));
                let nonce = ChaChaIV::from_public_slice(&random_byte_vec(12));
                let data = ByteSeq::from_public_slice(&random_byte_vec(10_000));
                (data, nonce, key)
            },
            |(data, nonce, key)| {
                let _c = chacha20(key, nonce, 0, &data);
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
