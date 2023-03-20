#[macro_use]
extern crate criterion;
use criterion::{BatchSize, Criterion};

use hacspec_p256::*;

fn benchmark(c: &mut Criterion) {
    // TODO: allow key generation and make these random
    c.bench_function("P256 ECDH", |b| {
        b.iter_batched(
            || {
                let k = P256Scalar::from_hex(
                    "0612465c89a023ab17855b0a6bcebfd3febb53aef84138647b5352e02c10c346",
                );
                let p = (
                    P256FieldElement::from_hex(
                        "62d5bd3372af75fe85a040715d0f502428e07046868b0bfdfa61d731afe44f26",
                    ),
                    P256FieldElement::from_hex(
                        "ac333a93a9e70a81cd5a95b5bf8d13990eb741c8c38872b4a07d275a014e30cf",
                    ),
                );
                (k, p)
            },
            |(k, p)| {
                let _r = p256_point_mul(k, p);
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
