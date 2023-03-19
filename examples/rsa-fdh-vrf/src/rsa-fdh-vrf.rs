// This crate implements RSA-FDH-VRF based on section 4 of https://datatracker.ietf.org/doc/draft-irtf-cfrg-vrf/
// The ciphersuite is RSA-FDH-VRF-SHA256, suite string can be changed if other hash function is desired
// The step comments refer to the corresponding steps in the IETF pseudocode for comparison with hacspec

use hacspec_lib::*;
use hacspec_sha256::*;
use hacspec_rsa_pkcs1::*;

bytes!(IntByte, 1);

#[rustfmt::skip]
const ONE: IntByte = IntByte(secret_array!(U8,  [0x01u8]));
#[rustfmt::skip]
const TWO: IntByte = IntByte(secret_array!(U8,  [0x02u8]));

const SUITE_STRING: IntByte = ONE;

// Helper function used by prove and verify to compute mgf1 of alpha
// mgf_salt currently part of cipher suite, could be optional input
fn vrf_mgf1(n: RSAInt, alpha: &ByteSeq) -> ByteSeqResult {
    let mgf_salt1 = i2osp(RSAInt::from_literal(BYTE_SIZE as u128), 4u32)?;
    let mgf_salt2 = i2osp(n, BYTE_SIZE)?;
    let mgf_salt = mgf_salt1.concat(&mgf_salt2);

    let mgf_string = SUITE_STRING
        .concat(&ONE)
        .concat(&mgf_salt)
        .concat(alpha);
    let mgf = mgf1(&mgf_string, BYTE_SIZE as usize - 1usize)?;
    ByteSeqResult::Ok(mgf)
}

// Based on section 4.1 of https://datatracker.ietf.org/doc/draft-irtf-cfrg-vrf/
pub fn prove(sk: SK, alpha: &ByteSeq) -> ByteSeqResult {
    let (n, _d) = sk.clone();

    // STEP 1 and 2
    let em = vrf_mgf1(n, alpha)?;

    // STEP 3
    let m = os2ip(&em);

    // STEP 4
    let s = rsasp1(sk, m)?;

    // STEP 5 and 6
    i2osp(s, BYTE_SIZE)
}

// Based on section 4.2 of https://datatracker.ietf.org/doc/draft-irtf-cfrg-vrf/
pub fn proof_to_hash(pi_string: &ByteSeq) -> ByteSeqResult {
    // STEP 1 and 2
    let hash_string = SUITE_STRING.concat(&TWO.concat(pi_string));

    // STEP 3
    ByteSeqResult::Ok(sha256(&hash_string).slice(0,32))
}

// Based on section 4.3 of https://datatracker.ietf.org/doc/draft-irtf-cfrg-vrf/
pub fn verify(pk: PK, alpha: &ByteSeq, pi_string: &ByteSeq) -> ByteSeqResult {
    let (n, _e) = pk.clone();

    // STEP 1
    let s = os2ip(pi_string);

    // STEP 2
    let m = rsavp1(pk, s)?;

    // STEP 3 and 4
    let em_prime = vrf_mgf1(n, alpha)?;

    // STEP 5
    let m_prime = os2ip(&em_prime);

    // STEP 6
    if m == m_prime {
        proof_to_hash(pi_string)
    } else {
        ByteSeqResult::Err(Error::VerificationFailed)
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt,Sign};
    use glass_pumpkin::prime;
    use quickcheck::*;

    // RSA key generation
    // Taken from https://asecuritysite.com/rust/rsa01/ 
    fn modinv(a0: BigInt, m0: BigInt) -> BigInt {
        if m0 == one() { return one() }
        let (mut a, mut m, mut x0, mut inv) = 
            (a0, m0.clone(), zero(), one());
        while a > one() {
            inv -= (&a / &m) * &x0;
            a = &a % &m;
            std::mem::swap(&mut a, &mut m);
            std::mem::swap(&mut x0, &mut inv)
        }
        if inv < zero() { inv += m0 }
        inv
    }

    fn rsa_key_gen() -> Keyp {
        let p = BigInt::from_biguint(Sign::Plus,
            prime::new((BIT_SIZE / 2) as usize).unwrap());
        let q = BigInt::from_biguint(Sign::Plus,
            prime::new((BIT_SIZE / 2) as usize).unwrap());

        let n = RSAInt::from(p.clone()* q.clone());

        let e = BigInt::parse_bytes(b"65537", 10).unwrap();
        let totient = (p - BigInt::one()) * (q - BigInt::one());
        let d = modinv(e.clone(), totient.clone());
        
        Keyp { n, d: RSAInt::from(d), e: RSAInt::from(e) }
    }

    // quickcheck generation
    #[derive(Clone, Copy, Debug)]
    struct Keyp {n: RSAInt, d: RSAInt, e: RSAInt}
    #[derive(Clone, Copy, Debug)]
    struct Wrapper(RSAInt);

    impl Arbitrary for Wrapper {
        fn arbitrary(g: &mut Gen) -> Wrapper {
            const NUM_BYTES: u32 = 127;
            let mut a: [u8; NUM_BYTES as usize] = [0; NUM_BYTES as usize];
            for i in 0..NUM_BYTES as usize {
                a[i] = u8::arbitrary(g);
            }
            Wrapper(RSAInt::from_byte_seq_be(&Seq::<U8>::from_public_slice(&a)))
        }
    }

    impl Arbitrary for Keyp {
        fn arbitrary(_g: &mut Gen) -> Keyp {
            rsa_key_gen()
        }
    }

    // quickcheck tests
    const NUM_TESTS: u64 = 5;
    #[test]
    fn test_rsafdhvrf() {
        fn rsafdhvrf(kp: Keyp, alpha: Wrapper) -> bool {
            let alpha = i2osp(alpha.0, BYTE_SIZE).unwrap();
            let pi = prove((kp.n, kp.d), &alpha).unwrap();
            let beta = proof_to_hash(&pi).unwrap();
            let beta_prime = verify((kp.n, kp.e), &alpha, &pi).unwrap();
            beta_prime == beta
        }
        QuickCheck::new().tests(NUM_TESTS)
            .quickcheck(rsafdhvrf as fn(Keyp, Wrapper) -> bool);
    }
    
    #[test]
    fn test_neg_rsafdhvrf() {
        fn neg_rsafdhvrf(kp: Keyp, fake: Keyp, alpha: Wrapper) -> bool {
            let alpha = i2osp(alpha.0, BYTE_SIZE).unwrap();
            let pi = prove((kp.n, kp.d), &alpha).unwrap();
            match verify((fake.n, fake.e), &alpha, &pi) {
                Ok(_beta_prime) => false,
                Err(e) => matches!(e, Error::VerificationFailed
                                    | Error::MessageTooLarge),
            }
        }
        QuickCheck::new().tests(NUM_TESTS)
            .quickcheck(neg_rsafdhvrf as fn(Keyp, Keyp, Wrapper) -> bool);
    }

    #[test]
    fn test_neg_alpha_rsafdhvrf() {
        fn neg_alpha_rsafdhvrf(
            kp: Keyp, alpha: Wrapper, fake_alpha: Wrapper
        ) -> bool {
            let alpha = i2osp(alpha.0, BYTE_SIZE).unwrap();
            let fake_alpha = i2osp(fake_alpha.0, BYTE_SIZE).unwrap();
            let pi = prove((kp.n, kp.d), &fake_alpha).unwrap();
            match verify((kp.n, kp.e), &alpha, &pi) {
                Ok(_beta_prime) => false,
                Err(e) => matches!(e, Error::VerificationFailed
                                    | Error::MessageTooLarge),
            }
        }
        QuickCheck::new().tests(NUM_TESTS)
            .quickcheck(neg_alpha_rsafdhvrf as
                fn(Keyp, Wrapper, Wrapper) -> bool);
    }

    // Test vector generation
    // Strings should be given in hexadecimal
    fn generate_test_vector(
        alpha: &str, kp: Keyp
    ) -> Result<(String, String), Error> {
        let alpha = ByteSeq::from_hex(&alpha);
        let pi = prove((kp.n, kp.d), &alpha).unwrap();
        let beta = proof_to_hash(&pi).unwrap();
        let beta_prime = verify((kp.n, kp.e), &alpha, &pi).unwrap();

        assert_eq!(beta_prime, beta);

        let n = i2osp(kp.n, BYTE_SIZE)?;
        let d = i2osp(kp.d, BYTE_SIZE)?;
        let e = i2osp(kp.e, BYTE_SIZE)?;

        println!("n:\n{}", ByteSeq::to_hex(&n));
        println!("d:\n{}", ByteSeq::to_hex(&d));
        println!("e:\n{}", ByteSeq::to_hex(&e));

        println!("alpha:\n{}", ByteSeq::to_hex(&alpha));
        println!("pi:\n{}", ByteSeq::to_hex(&pi));
        println!("beta:\n{}", ByteSeq::to_hex(&beta));

        Result::Ok((ByteSeq::to_hex(&pi), ByteSeq::to_hex(&beta)))
    }

    // Run with cargo test test_vector -- --ignored --nocapture in this crate
    #[test]
    #[ignore]
    fn test_vector() {
        // Pass alpha in hexadecimal
        let kp = rsa_key_gen();
        // let kp = get_test_key();
        assert!(!generate_test_vector("af82", kp).is_err());
    }

    fn get_test_key() -> Keyp {
        let n = RSAInt::from_hex("64f70acdc41c0ee7cb4961760368e34889c058ad3c7e578e8e72ed0d2fd1c7cfbb8beffd107204d544919db9d2470669c969e178d4deb8393daec4584ca9f162805c9ba46e617d89d4ab6480b0873b1cb92cf7232c88f013931ffe30f8ddf2cddbff4402bcb721985d2bb2eee5382dd09210b5d1da6b6b8207fe3e526de54efb55b56cd52d97cd77df6315569d5b59823c85ad99c57ad2959ec7d12cdf0c3e66cc57eaa1e644da9b0ca69b0df43945b0bd88ac66903ec98fe0e770b683ca7a332e69cba9229115a5295273aeeb4af2662063a312cbb4b871323f71888fd39557a5f4610ea7a590b021d43e5a89b69de68c728ce147f2743e0b97a5b3eb0d6ab1");
        let d = RSAInt::from_hex("39134e9033a488e8900ad3859b37d804519ae2864c04400ade8c2965a2fabc31ba9bc8f70e2ce67e895ca8053bd1dad6427e106ff626518e4a4859c670d0411ca5e3b438a80d84a23e0f05a99a2158514c7d16d8537cb5fadad8e3215c0e5c0bf3a9c210aa0dfc77dd73ae9b4e090c1d33f52e538b5dde508ba43626f2e906546773ba7401aa6b68ab1151da528336ddafc9a6f2995d89ec282bc555fe41e776216576c0aafb66ef00b718e6c62afd51faf82e7b5a1d430591465b2188fa286ce778eb6a1b346b58331c7820b4142fb808e59ec910aa9b6d340dea673ae7be2d9e1fa91494e40372bcfb92da5fe236dc93b30b0a59b20af8edf3a10e3ea6dfe1");
        let e = RSAInt::from_hex("010001");
        Keyp {n, d, e}
    }

    // Note that the test vectors have been generated using this code
    #[test]
    fn test_empty() {
        let kp = get_test_key();
        let alpha = ByteSeq::from_hex("");
        let pi = ByteSeq::from_hex("406581e350c601d6d7518ac928f6753929c56a7480a4a3d011ed65e5f61ca033accd45c03cac2dddcd61b909cedd0df517a1bba4705c9d04a2a8c7d735d24bc3e59b263cc8c18d5f6e2712747d809df7868ac720f90ffd3d7c7b78f3d75f14a9755ea8138804806f4739429d1a313b3abaaf89ce97fbdf10bc01d66723b0b38ad5dc51c87e5f852e2c8fc923cf0f9c86bb7bf8ae808532fcb8a981338d5b13278e66e19915e41c6fbd09f1fce3300da422fbf46f706d1c79f298c740926e14069f83dae52a25bad684e420ad5fc8af3b02e0cf3f79782fb6e7e65abe5e1f6b4fe41f20339b2986fe39f7ce4ceb9c2490d5229e9bfda93150d6800880c411daae");
        let beta = ByteSeq::from_hex("d065ca3be8716236e99f64139adf481090f0a0c839f86ffda3c4fad948166af0");

        let pi_prime = prove((kp.n, kp.d), &alpha).unwrap();
        assert_eq!(pi_prime, pi);

        let beta_prime = proof_to_hash(&pi).unwrap();
        assert_eq!(beta_prime, beta);

        let beta_prime = verify((kp.n, kp.e), &alpha, &pi).unwrap();
        assert_eq!(beta_prime, beta);
    }

    #[test]
    fn test_72() {
        let kp = get_test_key();
        let alpha = ByteSeq::from_hex("72");
        let pi = ByteSeq::from_hex("3d396dc417bee1975ff63c4e8b43b9417be03a91d5eb47309790d74100271342d6dc11511333ec4bc42aea3e02640dc870665044e85085c3dea43eedeb266d9b2de3824aca18b8de3e4d198bde808d80a2a10f0f4bd73fbc7cc36da44cb68af3161b2264e737dcd2d669252abb29f275c971ff6b8234876b7d1ff3d4d05197fe563d6ae92685dccbbbb689b4837da42fe47433019d9bfc50001b11708bf9f656532febf674119c0d67e27714195722fd977e0fc35d7325b5fb3ecb54df53986e01a809d0e5ec442fdacc3d271e7ab5480b8eb18f25cd3baf6a47abc6bf027e8dedef911f2bec367fa5d65e106f314b64cc1d9534d4f26fa034035a43852be66a");
        let beta = ByteSeq::from_hex("a229210b84f0bb43b296075f226dee433cf2727cd6c2e4871afdeb77414f6a47");

        let pi_prime = prove((kp.n, kp.d), &alpha).unwrap();
        assert_eq!(pi_prime, pi);

        let beta_prime = proof_to_hash(&pi).unwrap();
        assert_eq!(beta_prime, beta);

        let beta_prime = verify((kp.n, kp.e), &alpha, &pi).unwrap();
        assert_eq!(beta_prime, beta);
    }

    #[test]
    fn test_af82() {
        let kp = get_test_key();
        let alpha = ByteSeq::from_hex("af82");
        let pi = ByteSeq::from_hex("57b07056abc6851330b21ae890fd43ea53b4435319748cf8dba82148ee381c11d21a8660a8714aa59abaac2b7d0141ac4e85b1113b144328eb11461a7f26086896036fc49579a58a2516cecd274946f8dd82fef31652dfe2e2b495966cd6193a1bd197ef6e3472f30bfe14827dd968ea3bf8310dc002a765a0d54b12c3c9627309800b74701a3f7d07a02db0a6ca3a639e60726059727313818a6b671bebe18f078713ced33e50acbfd1e661ec89c5e82b8e1e07f6293f45474aa57d084da46a2437932491d92a87b3393bb0ec62254a3eca19e1004756867839671f84f7a2378097f334832f4aa0442fc5f8637fb2220bb3f2dca247927f0d49ae1c1b2e7455");
        let beta = ByteSeq::from_hex("ebc5582b6aaf23c424ec1c74e1b8250327c957967fa37566284dac8400e62032");

        let pi_prime = prove((kp.n, kp.d), &alpha).unwrap();
        assert_eq!(pi_prime, pi);

        let beta_prime = proof_to_hash(&pi).unwrap();
        assert_eq!(beta_prime, beta);

        let beta_prime = verify((kp.n, kp.e), &alpha, &pi).unwrap();
        assert_eq!(beta_prime, beta);
    }
    
}
