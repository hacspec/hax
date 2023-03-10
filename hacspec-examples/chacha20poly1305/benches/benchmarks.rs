#[macro_use]
extern crate criterion;
use criterion::{BatchSize, Criterion};

use hacspec_chacha20::*;
use hacspec_chacha20poly1305::*;
use hacspec_dev::rand::random_byte_vec;
use hacspec_lib::prelude::*;

fn benchmark(c: &mut Criterion) {
    c.bench_function("ChaCha20Poly1305 encrypt", |b| {
        b.iter_batched(
            || {
                let key = ChaChaKey::from_public_slice(&random_byte_vec(32));
                let nonce = ChaChaIV::from_public_slice(&random_byte_vec(12));
                let data = ByteSeq::from_public_slice(&random_byte_vec(10_000));
                let aad = ByteSeq::from_public_slice(&random_byte_vec(1_000));
                (data, nonce, aad, key)
            },
            |(data, nonce, aad, key)| {
                let (_cipher, _tag) = chacha20_poly1305_encrypt(key, nonce, &aad, &data);
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("ChaCha20Poly1305 decrypt", |b| {
        b.iter_batched(
            || {
                let key = ChaChaKey::from_public_slice(&random_byte_vec(32));
                let nonce = ChaChaIV::from_public_slice(&random_byte_vec(12));
                let data = ByteSeq::from_public_slice(&random_byte_vec(10_000));
                let aad = ByteSeq::from_public_slice(&random_byte_vec(1_000));
                let (cipher, tag) = chacha20_poly1305_encrypt(key, nonce, &aad, &data);
                (nonce, aad, key, cipher, tag)
            },
            |(nonce, aad, key, cipher, tag)| {
                let _msg = chacha20_poly1305_decrypt(key, nonce, &aad, &cipher, tag);
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
