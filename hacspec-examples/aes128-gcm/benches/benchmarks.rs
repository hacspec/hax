#[macro_use]
extern crate criterion;
use criterion::{BatchSize, Criterion};

use hacspec_aes::*;
use hacspec_aes128_gcm::*;
use hacspec_dev::rand::random_byte_vec;
use hacspec_lib::prelude::*;

fn benchmark(c: &mut Criterion) {
    c.bench_function("AES GCM 128 encrypt", |b| {
        b.iter_batched(
            || {
                let key = Key128::from_public_slice(&random_byte_vec(16));
                let nonce = AesNonce::from_public_slice(&random_byte_vec(12));
                let data = Seq::<U8>::from_public_slice(&random_byte_vec(1_000));
                let aad = Seq::<U8>::from_public_slice(&random_byte_vec(1_000));
                (data, nonce, aad, key)
            },
            |(data, nonce, aad, key)| {
                let (_cipher, _tag) = encrypt_aes128(key, nonce, &aad, &data);
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("AES GCM 128 decrypt", |b| {
        b.iter_batched(
            || {
                let key = Key128::from_public_slice(&random_byte_vec(16));
                let nonce = AesNonce::from_public_slice(&random_byte_vec(12));
                let data = Seq::<U8>::from_public_slice(&random_byte_vec(1_000));
                let aad = Seq::<U8>::from_public_slice(&random_byte_vec(1_000));
                let (cipher, tag) = encrypt_aes128(key, nonce, &aad, &data);
                (cipher, tag, nonce, aad, key)
            },
            |(cipher, tag, nonce, aad, key)| {
                let _decrypted_msg = decrypt_aes128(key, nonce, &aad, &cipher, tag);
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
