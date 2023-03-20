#[macro_use]
extern crate criterion;
use criterion::{BatchSize, Criterion};

use hacspec_aes::*;
use hacspec_dev::rand::random_byte_vec;
use hacspec_lib::prelude::*;

fn benchmark(c: &mut Criterion) {
    c.bench_function("AES 128 encrypt", |b| {
        b.iter_batched(
            || {
                let key = Key128::from_public_slice(&random_byte_vec(16));
                let nonce = AesNonce::from_public_slice(&random_byte_vec(12));
                let data = ByteSeq::from_public_slice(&random_byte_vec(10_000));
                (data, nonce, key)
            },
            |(data, nonce, key)| {
                let _c = aes128_encrypt(key, nonce, U32(0), &data);
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("AES 128 decrypt", |b| {
        b.iter_batched(
            || {
                let key = Key128::from_public_slice(&random_byte_vec(16));
                let nonce = AesNonce::from_public_slice(&random_byte_vec(12));
                let data = ByteSeq::from_public_slice(&random_byte_vec(10_000));
                let ctxt = aes128_encrypt(key, nonce, U32(0), &data);
                (ctxt, nonce, key)
            },
            |(ctxt, nonce, key)| {
                let _m = aes128_decrypt(key, nonce, U32(0), &ctxt);
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
