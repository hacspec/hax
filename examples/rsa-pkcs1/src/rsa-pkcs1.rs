// This crate implements RSA primitives from PKCS #1 v2.2, as specified in RFC8017: https://datatracker.ietf.org/doc/html/rfc8017
// Secret keys are represented in the representation described in section 3.2 of https://datatracker.ietf.org/doc/html/rfc8017#section-3.2
// Note that the RSA primitives return a MessageTooLarge error if the message is larger than the RSA modulus n
use hacspec_lib::*;
use hacspec_sha256::*;

pub const BIT_SIZE: u32  = 2048u32;
pub const BYTE_SIZE: u32 = 2048u32 / 8u32;
const HLEN: usize = 32usize; // sha256 / 8 = 32

unsigned_public_integer!(RSAInt, 2048);

#[derive(Debug, PartialEq)]
pub enum Error {
    InvalidLength,
    MessageTooLarge,
    DecryptionFailed,
    VerificationFailed,
}

pub type PK = (RSAInt, RSAInt);
pub type SK = (RSAInt, RSAInt);
pub type KeyPair = (PK, SK);
pub type ByteSeqResult = Result<ByteSeq, Error>;
pub type RSAIntResult = Result<RSAInt, Error>;

// Encryption primitive, see section 5.1.1 of https://datatracker.ietf.org/doc/html/rfc8017#section-5.1.1
pub fn rsaep(pk: PK, m: RSAInt) -> RSAIntResult {
    let (n, e) = pk;
    if m > n - RSAInt::ONE() {
        RSAIntResult::Err(Error::MessageTooLarge)
    } else {
        RSAIntResult::Ok(m.pow_mod(e, n))
    }
}

// Decryption primitive, see section 5.1.2 of https://datatracker.ietf.org/doc/html/rfc8017#section-5.1.2
pub fn rsadp(sk: SK, c: RSAInt) -> RSAIntResult {
    let (n, d) = sk;
    if c > n - RSAInt::ONE() {
        RSAIntResult::Err(Error::MessageTooLarge)
    } else {
        RSAIntResult::Ok(c.pow_mod(d, n))
    }
}

// Signature primitive, see section 5.2.1 of https://datatracker.ietf.org/doc/html/rfc8017#section-5.2.1
pub fn rsasp1(sk: SK, m: RSAInt) -> RSAIntResult {
    let (n, d) = sk;
    if m > n - RSAInt::ONE() {
        RSAIntResult::Err(Error::MessageTooLarge)
    } else {
        RSAIntResult::Ok(m.pow_mod(d, n))
    }
}

// Verification primitive, see section 5.2.2 of https://datatracker.ietf.org/doc/html/rfc8017#section-5.2.2
pub fn rsavp1(pk: PK, s: RSAInt) -> RSAIntResult {
    let (n, e) = pk;
    if s > n - RSAInt::ONE() {
        RSAIntResult::Err(Error::MessageTooLarge)
    } else {
        RSAIntResult::Ok(s.pow_mod(e, n))
    }
}

// RSA integer to octet string primitive, as described in section 4.1 of https://datatracker.ietf.org/doc/html/rfc8017#section-4.1
pub fn i2osp(x: RSAInt, x_len: u32) -> ByteSeqResult {
    if x >= (RSAInt::exp(RSAInt::from_literal(256u128), x_len)) 
            && x_len != BYTE_SIZE {
        ByteSeqResult::Err(Error::InvalidLength)
    } else {
        ByteSeqResult::Ok(RSAInt::to_byte_seq_be(x)
            .slice((BYTE_SIZE - x_len) as usize, x_len as usize))
    }
}

// Octet string to RSA integer primitive, as described in section 4.2 of https://datatracker.ietf.org/doc/html/rfc8017#section-4.2
pub fn os2ip(x: &ByteSeq) -> RSAInt {
    RSAInt::from_byte_seq_be(x)
}

// Mask generation function from appendix B.2.1, see https://datatracker.ietf.org/doc/html/rfc8017#appendix-B.2.1
pub fn mgf1(mgf_seed: &ByteSeq, mask_len: usize) -> ByteSeqResult {
    let mut result = ByteSeqResult::Err(Error::InvalidLength);
    if mask_len < 2usize^32usize * HLEN {
        let mut t = ByteSeq::new(0);
        for i in 0..((mask_len + 32) / 32) {
            let x = i2osp(RSAInt::from_literal(i as u128), 4u32)?;
            t = t.concat(&sha256(&mgf_seed.concat(&x)));
        }
        result = ByteSeqResult::Ok(t.slice(0, mask_len))
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt,Sign};
    use glass_pumpkin::prime;
    use quickcheck::*;
    use quickcheck_macros::quickcheck;
 
    // RSA key generation
    // Taken from https://asecuritysite.com/rust/rsa01/ 
    fn modinv(a0: BigInt, m0: BigInt) -> BigInt {
        if m0 == one() {return one()}
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

    fn rsa_key_gen() -> KeyPair {
        let p = BigInt::from_biguint(Sign::Plus,
            prime::new((BIT_SIZE / 2) as usize).unwrap());
        let q = BigInt::from_biguint(Sign::Plus,
            prime::new((BIT_SIZE / 2) as usize).unwrap());

        let n = RSAInt::from(p.clone()* q.clone());

        let e = BigInt::parse_bytes(b"65537", 10).unwrap();
        let totient = (p - BigInt::one()) * (q - BigInt::one());
        let d = modinv(e.clone(), totient.clone());
        
        ((n, RSAInt::from(e)), (n, RSAInt::from(d)))
    }

    // quickcheck generation
    #[derive(Clone, Copy, Debug)]
    struct Keyp {n: RSAInt, d: RSAInt, e: RSAInt}

    impl Arbitrary for RSAInt {
        fn arbitrary(g: &mut Gen) -> RSAInt {
            const NUM_BYTES: u32 = 255;
            let mut a: [u8; NUM_BYTES as usize] = [0; NUM_BYTES as usize];
            for i in 0..NUM_BYTES as usize {
                a[i] = u8::arbitrary(g);
            }
            RSAInt::from_byte_seq_be(&Seq::<U8>::from_public_slice(&a))
        }
    }

    impl Arbitrary for Keyp {
        fn arbitrary(_g: &mut Gen) -> Keyp {
            let ((n, e), (_n, d)) = rsa_key_gen();
            Keyp {n,d,e}
        }
    }


    // quickcheck tests
    const NUM_TESTS: u64 = 10;
    #[quickcheck]
    fn i2os2i(x: RSAInt) -> bool {
        let s = i2osp(x, BYTE_SIZE).unwrap();
        let x_prime = os2ip(&s);
        x_prime == x
    }

    #[test]
    fn test_rsaepdp() {
        fn rsaepdp(x: RSAInt, kp: Keyp) -> bool {
            let c = rsaep((kp.n, kp.e), x).unwrap();
            let x_prime =  rsadp((kp.n, kp.d), c).unwrap();
            x_prime == x
        }
        QuickCheck::new().tests(NUM_TESTS)
            .quickcheck(rsaepdp as fn(RSAInt, Keyp) -> bool);
    }

    #[test]
    fn test_rsasp1vp1() {
        fn rsasp1vp1(x: RSAInt, kp: Keyp) -> bool {
            let s = rsasp1((kp.n, kp.d), x).unwrap();
            let x_prime = rsavp1((kp.n, kp.e), s).unwrap();
            x_prime == x
        }
        QuickCheck::new().tests(NUM_TESTS)
            .quickcheck(rsasp1vp1 as fn(RSAInt, Keyp) -> bool);
    }

    #[test]
    fn test_neg_rsaepdp() {
        fn neg_rsaepdp(x: RSAInt, y: RSAInt, kp: Keyp) -> bool {
            let x_prime = rsadp((kp.n, kp.d), y).unwrap();
            x_prime != x
        }
        QuickCheck::new().tests(NUM_TESTS)
            .quickcheck(neg_rsaepdp as fn(RSAInt, RSAInt, Keyp) -> bool);
    }

    #[test]
    fn test_neg_rsasp1vp1() {
        fn neg_rsasp1vp1(x: RSAInt, y: RSAInt, kp: Keyp) -> bool {
            let x_prime = rsavp1((kp.n, kp.e), y).unwrap();
            x_prime != x
        }
        QuickCheck::new().tests(NUM_TESTS)
            .quickcheck(neg_rsasp1vp1 as fn(RSAInt, RSAInt, Keyp) -> bool);
    }

    #[test]
    fn test_negkey_rsaepdp() {
        fn negkey_rsaepdp(x: RSAInt, kp: Keyp, fake: Keyp) -> bool {
            let c = rsaep((kp.n, kp.e), x).unwrap();
            let x_prime = rsadp((fake.n, fake.d), c).unwrap_or_default();
            x != x_prime
        }
        QuickCheck::new().tests(NUM_TESTS)
            .quickcheck(negkey_rsaepdp as fn(RSAInt, Keyp, Keyp) -> bool);
    }

    #[test]
    fn test_negkey_rsasp1vp1() {
        fn negkey_rsasp1vp1(x: RSAInt, kp: Keyp, fake: Keyp) -> bool {
            let s = rsasp1((kp.n, kp.d), x).unwrap();
            let x_prime = rsavp1((fake.n, fake.e), s).unwrap_or_default();
            x != x_prime
        }
        QuickCheck::new().tests(NUM_TESTS)
            .quickcheck(negkey_rsasp1vp1 as fn(RSAInt, Keyp, Keyp) -> bool)
    }

    // tests using test vectors from wycheproof: https://github.com/google/wycheproof/blob/master/testvectors/rsa_pkcs1_2048_test.json
    // tests use RSAES-PKCS1-v1_5 padding
    fn get_test_ed_key() -> Keyp {
        let n = RSAInt::from_hex("00b3510a2bcd4ce644c5b594ae5059e12b2f054b658d5da5959a2fdf1871b808bc3df3e628d2792e51aad5c124b43bda453dca5cde4bcf28e7bd4effba0cb4b742bbb6d5a013cb63d1aa3a89e02627ef5398b52c0cfd97d208abeb8d7c9bce0bbeb019a86ddb589beb29a5b74bf861075c677c81d430f030c265247af9d3c9140ccb65309d07e0adc1efd15cf17e7b055d7da3868e4648cc3a180f0ee7f8e1e7b18098a3391b4ce7161e98d57af8a947e201a463e2d6bbca8059e5706e9dfed8f4856465ffa712ed1aa18e888d12dc6aa09ce95ecfca83cc5b0b15db09c8647f5d524c0f2e7620a3416b9623cadc0f097af573261c98c8400aa12af38e43cad84d");
        let d = RSAInt::from_hex("1a502d0eea6c7b69e21d5839101f705456ed0ef852fb47fe21071f54c5f33c8ceb066c62d727e32d26c58137329f89d3195325b795264c195d85472f7507dbd0961d2951f935a26b34f0ac24d15490e1128a9b7138915bc7dbfa8fe396357131c543ae9c98507368d9ceb08c1c6198a3eda7aea185a0e976cd42c22d00f003d9f19d96ea4c9afcbfe1441ccc802cfb0689f59d804c6a4e4f404c15174745ed6cb8bc88ef0b33ba0d2a80e35e43bc90f350052e72016e75b00d357a381c9c0d467069ca660887c987766349fcc43460b4aa516bce079edd87ba164307b752c277ed9528ad3ba0bf1877349ed3b7966a6c240110409bf4d0fade0c68fdadd847fd");
        let e = RSAInt::from_hex("010001");
        Keyp {n, d, e}
    }

    #[test]
    // tcId1
    fn test_ed_empty() {
        let k = get_test_ed_key();
        // 0x00 || 0x02 || PS || 0x00
        let ps = ByteSeq::from_hex("00020cd093f602b702dab3162f1853fb22978f2af910e27edb53ad3e88db7ed999619dab0ef87eea68cd45ca64c9b2897af1b85d7be82a6f25bc3f27b3edce366892936616d0174c116656908ac607f2c2571c08b751d883b34bc27e2f2e1bb78325a2169a258f515cc23ede74e5b56650871b28a770293ff1caa6be279c83c20ebf77b6d2e548c205765c87c61a993a33b48c397efc0b0d0cd8323b6c74420da031d794626370abc0fa2b79a6c33c040aec566848524a59b182da2cd23afb61d3bb60550b381b21d1a55e328b6fba58da8fdb3ee5e1a49ea117e41158fee136fd01d3c5cd089f649a6a96132076a37c78da07bb7e032d708f123ab8e2b49e00");
        let ms = ByteSeq::from_hex("");
        let cs = ByteSeq::from_hex("5999ccb0cfdd584a3fd9daf247b9cd7314323f8bba4864258f98c6bafc068fe672641bab25ef5b1a7a2b88f67f12af3ca4fe3c493b2062bbb11ad3b1ba0640025c814326ff50ed52b176bd7f606ea9e209bcdcc67c0a0c4b8ed30b9959c57e90fd1efdf99895e2608095f92caff9070dec900fb96d5ce5efd2b2e66b80cff27d482d242b307cb813e7dc818fce31b67ac9a94501b5bc4621b547ba9d81808dd297d600dfc1a7deeb061570cde8894e398453328740adfd77cf76075a109d41ad296651ac817382424a4907d5a342d06cf19c09d5b37a147dd69045bf7d378e19dbbbbfb25282e3d9a4dc9793c8c32ab5a45c0b43dba4daca367b6eb5f4432a62");

        let m = os2ip(&ps.concat(&ms));
        let c = os2ip(&cs);
        
        let c_prime = rsaep((k.n, k.e), m);
        assert_eq!(RSAIntResult::Ok(c), c_prime);

        let m_prime = rsadp((k.n, k.d), c);
        assert_eq!(RSAIntResult::Ok(m), m_prime)
    }

    #[test]
    // tcId3
    fn test_ed_54657374() {
        let k = get_test_ed_key();
        // 0x00 || 0x02 || PS || 0x00
        let ps = ByteSeq::from_hex("0002709714b048c369732269a3d8f92302508770a44368014b3a5cb185c0c91d972c27458dc89b8dfbf02b243fc223be8caa0fafc049b9aeb7d6496945fe9609ebf57e099f67ffe2106e0ea73c261f8d716b763e94f58070980120f4c5519dadbdd28c9102caea032c500e545f9a6099a7ef907b3d9eb30dd3d096c3bd013982df7f864adcb13583eabc9344cb7bf84e46fef0bdde7e88507e1c17c37facdaff20379e83c2071768cfbbeb530150d16b4bb5433d41839a6113ca8a5fcbad5e2ffff71a0155e45c8c21696977fe310c05cb0ac76a9410f0d024ea4d9093ea30dd43259872faa7823c241b3d09dcf4b1b5f35f117cd17e6b7575b92100");
        let ms = ByteSeq::from_hex("54657374");
        let cs = ByteSeq::from_hex("4501b4d669e01b9ef2dc800aa1b06d49196f5a09fe8fbcd037323c60eaf027bfb98432be4e4a26c567ffec718bcbea977dd26812fa071c33808b4d5ebb742d9879806094b6fbeea63d25ea3141733b60e31c6912106e1b758a7fe0014f075193faa8b4622bfd5d3013f0a32190a95de61a3604711bc62945f95a6522bd4dfed0a994ef185b28c281f7b5e4c8ed41176d12d9fc1b837e6a0111d0132d08a6d6f0580de0c9eed8ed105531799482d1e466c68c23b0c222af7fc12ac279bc4ff57e7b4586d209371b38c4c1035edd418dc5f960441cb21ea2bedbfea86de0d7861e81021b650a1de51002c315f1e7c12debe4dcebf790caaa54a2f26b149cf9e77d");

        let m = os2ip(&ps.concat(&ms));
        let c = os2ip(&cs);

        let c_prime = rsaep((k.n, k.e), m);
        assert_eq!(RSAIntResult::Ok(c), c_prime);

        let m_prime = rsadp((k.n, k.d), c);
        assert_eq!(RSAIntResult::Ok(m), m_prime)
    }

    #[test]
    // tcId 5
    fn test_ed_4d657373616765() {
        let k = get_test_ed_key();
        // 0x00 || 0x02 || PS || 0x00
        let ps = ByteSeq::from_hex("000272de8d1ab401e00fd5db485f9a27c50490b0b4aa46a79dc1b28bbfbde9a52ac1219072d6e5c8f90952c03bdbea2bb993c420faf885931a95e0bea2cdeee3505262c1fa85d61c57c9c4f8aa498f9d1a0372e9fe8f2e469fb5aee3b897d06c12e4702c5490b56c5d0a8bb3bc4624c4455582a79c069e45275231e12697d28b39e3db9723c489b4867cfa6da1c76d1bfc8c0811c1991acd1570dbeafd9a9d9748beafa35d0b429fa933280fd5ebcf5fe838405ae9159fb03bdf2eeee3a692e6dabf4bced04c169f070cf2bcb572034037bad3949a685a798ef8ffee456c4de5639bc2521db8f2738c100d2b4b42e6d6d9953940cc6cd78a00");
        let ms = ByteSeq::from_hex("4d657373616765");
        let cs = ByteSeq::from_hex("1cf861ef8b6c29474666605d3ddb663a259a9ae838417abcc7f7dd42d471d5f3812cdf90e3041c4c5bfd38ac1e4d95fd71661bddac45f5f8e3e89629a335bbf2eff116030f1c5ace8336cf7e94c2e8bf5a1d6116e54ec42b9da5fc651a41ac8fd38194e5029489cfde1f7fc850c0dfb3dc00021f74ae3847327c69afdb1355c7587bb93d5f4d2cfb35a7f70bcabd43eb32300585b6ee32f14a68c2a08434e923adb76dfcdf3ea5133edffa5ca20425083b28ecb045e69562b44286d320d87285e7a2e3bedded083c010401ae22c8f278b080112c4264a3cad3ed9fa31cf19e052aabbda9f8ecef1d64786258202bb61128b3140a355d65b982b0239764d77d24");

        let m = os2ip(&ps.concat(&ms));
        let c = os2ip(&cs);

        let c_prime = rsaep((k.n, k.e), m);
        assert_eq!(RSAIntResult::Ok(c), c_prime);

        let m_prime = rsadp((k.n, k.d), c);
        assert_eq!(RSAIntResult::Ok(m), m_prime)
    }
    
    #[test]
    // tcId 8
    fn test_ed_longest() {
        let k = get_test_ed_key();
        // 0x00 || 0x02 || PS || 0x00
        let ps = ByteSeq::from_hex("00021fe7713cc938261d00");
        let ms = ByteSeq::from_hex("7878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878");
        let cs = ByteSeq::from_hex("7e151b7b34e3b4abe045cf708640e61501c50fdca629aeca10259d45d15eeec6a2008b6336f57021ac6fdad9a6b29d65f098abff76f93722a8e23fb5e153db075005575dad6adccb7c020cd741c3419946b82d369a07fad5b0d55d51774f8991bd65e9e828d8f5a989c866a024a4a78434e9affd0af2c72f9185d450b627008a8a0968fc6373ca340410306a58921cce1207bb6f6c14e3d1f214304f9f6bb9199909e1610322e834b0ce9f55b1835d7623b82ef548545f984ea51466250159344dde902a0f021ba4baf26b16d8c6a42003f4d5dcae531187dc7e3f87c9e04470599eb623e04fca266e86f98cabb6866004e7fc80b36c3977456e51eb64f4b65f");

        let m = os2ip(&ps.concat(&ms));
        let c = os2ip(&cs);
            
        let c_prime = rsaep((k.n, k.e), m);
        assert_eq!(RSAIntResult::Ok(c), c_prime);

        let m_prime = rsadp((k.n, k.d), c);
        assert_eq!(RSAIntResult::Ok(m), m_prime)
    }

    // tests using test vectors from wycheproof: https://github.com/google/wycheproof/blob/master/testvectors/rsa_sig_gen_misc_test.json
    // tests use RSASSA-PKCS1-v1_5
    fn get_test_sv_key() -> Keyp {
        let n = RSAInt::from_hex("00a2b451a07d0aa5f96e455671513550514a8a5b462ebef717094fa1fee82224e637f9746d3f7cafd31878d80325b6ef5a1700f65903b469429e89d6eac8845097b5ab393189db92512ed8a7711a1253facd20f79c15e8247f3d3e42e46e48c98e254a2fe9765313a03eff8f17e1a029397a1fa26a8dce26f490ed81299615d9814c22da610428e09c7d9658594266f5c021d0fceca08d945a12be82de4d1ece6b4c03145b5d3495d4ed5411eb878daf05fd7afc3e09ada0f1126422f590975a1969816f48698bcbba1b4d9cae79d460d8f9f85e7975005d9bc22c4e5ac0f7c1a45d12569a62807d3b9a02e5a530e773066f453d1f5b4c2e9cf7820283f742b9d5");
        let d = RSAInt::from_hex("7627eef3567b2a27268e52053ecd31c3a7172ccb9ddcee819b306a5b3c66b7573ca4fa88efc6f3c4a00bfa0ae7139f64543a4dac3d05823f6ff477cfcec84fe2ac7a68b17204b390232e110310c4e899c4e7c10967db4acde042dbbf19dbe00b4b4741de1020aaaaffb5054c797c9f136f7d93ac3fc8caff6654242d7821ebee517bf537f44366a0fdd45ae05b9909c2e6cc1ed9281eff4399f76c96b96233ec29ae0bbf0d752b234fc197389f51050aa1acd01c074c3ac8fbdb9ea8b651a95995e8db4ad5c43b6c8673e5a126e7ee94b8dff4c5afc01259bc8da76950bae6f8bae715f50985b0d6f66d04c6fef3b700720eecdcdf171bb7b1ecbe7289c467c1");
        let e = RSAInt::from_hex("010001");
        Keyp {n, d, e}
    }

    #[test]
    // tcId81
    fn test_sv_empty() {
        let k = get_test_sv_key();
        // 0x00 || 0x01 || PS || 0x00
        let ps = ByteSeq::from_hex("0001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00");
        let der = ByteSeq::from_hex("3031300d060960864801650304020105000420"); // SHA-256
        let ms = ByteSeq::from_hex("");
        let ss = ByteSeq::from_hex("840f5dac53106dd1f9c57219224cf51289290c42f20466875ba8e830ac5690e541536fcc8ab03b731f82bf66d83f194e7e180b3963ec7a2f3f7904a7ce49aed47da4d4b79421eaf937d301b3e696169297b797c32c076a12be4de0b58e003c5123051a84a10c62f8dac2f42a8640008eb3c7cccd6760ff5b51b689763922582845f048fb8150e5a7a6ca2eccc7bdc85349ad5b26c52137a79fa3fe5c29ab5cd7615013219c1941b6708e9c3c23feff5febaf0c8ebca5750b54e3e6e99a3e876b396f27860b7f3ec4e9191703c6332d944f6f69751167680c79c4f6b57f1cc8755d24b6ec158ccdbacdb23107a33cb6b332516c13274d1f9dccc21dced869e486");
        let digest = sha256(&ms);

        let m = os2ip(&ps.concat(&der).concat(&digest));
        let s = os2ip(&ss);
        
        let s_prime = rsasp1((k.n, k.d), m);
        assert_eq!(RSAIntResult::Ok(s), s_prime);

        let m_prime = rsavp1((k.n, k.e), s);
        assert_eq!(RSAIntResult::Ok(m), m_prime)
    }

    #[test]
    // tcId83
    fn test_sv_54657374() {
        let k = get_test_sv_key();
        // 0x00 || 0x01 || PS || 0x00
        let ps = ByteSeq::from_hex("0001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00");
        let der = ByteSeq::from_hex("3031300d060960864801650304020105000420"); // SHA-256
        let ms = ByteSeq::from_hex("54657374");
        let ss = ByteSeq::from_hex("264491e844c119f14e425c03282139a558dcdaeb82a4628173cd407fd319f9076eaebc0dd87a1c22e4d17839096886d58a9d5b7f7aeb63efec56c45ac7bead4203b6886e1faa90e028ec0ae094d46bf3f97efdd19045cfbc25a1abda2432639f9876405c0d68f8edbf047c12a454f7681d5d5a2b54bd3723d193dbad4338baad753264006e2d08931c4b8bb79aa1c9cad10eb6605f87c5831f6e2b08e002f9c6f21141f5841d92727dd3e1d99c36bc560da3c9067df99fcaf818941f72588be33032bad22caf6704223bb114d575b6d02d9d222b580005d930e8f40cce9f672eebb634a20177d84351627964b83f2053d736a84ab1a005f63bd5ba943de6205c");
        let digest = sha256(&ms);

        let m = os2ip(&ps.concat(&der).concat(&digest));
        let s = os2ip(&ss);
        
        let s_prime = rsasp1((k.n, k.d), m);
        assert_eq!(RSAIntResult::Ok(s), s_prime);

        let m_prime = rsavp1((k.n, k.e), s);
        assert_eq!(RSAIntResult::Ok(m), m_prime)
    }

    #[test]
    // tcId88
    fn test_sv_long() {
        let k = get_test_sv_key();
        // 0x00 || 0x01 || PS || 0x00
        let ps = ByteSeq::from_hex("0001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00");
        let der = ByteSeq::from_hex("3031300d060960864801650304020105000420"); // SHA-256
        let ms = ByteSeq::from_hex("0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff000102030405060708090a0b0c0d0e0f1011121314151617");
        let ss = ByteSeq::from_hex("7aad44a36610ac147835efc623e3aeec0d5d8acbd7f469f92142592c7b843c9326e2015c4bf3843678d2e183ec9ed568e5dd8d535ea77a6d7fe804222e6208d0160bd6cf2744cdb56bce0ed7269cc5f2bcc25d3474c0fb5bc7d20ebf3664bad858dc6e86dabfa5f39a70e23344ab4f8d5edc6397d9d1b54fda4216e0b93d37b906384f82d36666d526939e0f917344208aadf05416c656a11a307ce2101912763728cfc0bd237017d36b8566c6c366b13f142c93edde181146ec63e49a57335b5d9295b85aa4c00d49cae7930653a5651c21371a4b3ec8a6e0f371d005e8b4f1631f7466b767b4789e75e1d2bc63ce4c46e5e7baf0b801ef785fd07ae79bbeef");
        let digest = sha256(&ms);

        let m = os2ip(&ps.concat(&der).concat(&digest));
        let s = os2ip(&ss);
        
        let s_prime = rsasp1((k.n, k.d), m);
        assert_eq!(RSAIntResult::Ok(s), s_prime);

        let m_prime = rsavp1((k.n, k.e), s);
        assert_eq!(RSAIntResult::Ok(m), m_prime)
    }
}
