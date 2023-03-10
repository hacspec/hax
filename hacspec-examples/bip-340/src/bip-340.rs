//! This crate is an INSECURE prototype implementation of BIP-340 (<https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki>).
//! It is vulnerable against timing attacks.

use hacspec_lib::*;
use hacspec_sha256::*;

#[derive(Debug, PartialEq)]
pub enum Error {
    InvalidSecretKey,
    InvalidNonceGenerated,
    InvalidPublicKey,
    InvalidXCoordinate,
    InvalidSignature,
}

public_nat_mod!(
    type_name: FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"
);

public_nat_mod!(
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256,
    modulo_value: "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"
);

unsigned_public_integer!(BigInteger, 256);

pub type AffinePoint = (FieldElement, FieldElement);

public_bytes!(PBytes32, 32);

#[derive(Debug, Copy, Clone)]
pub enum Point {
    Affine(AffinePoint),
    AtInfinity,
}

pub fn finite(p: Point) -> Option<AffinePoint> {
    match p {
        Point::Affine(p) => Some(p),
        Point::AtInfinity => Option::<AffinePoint>::None,
    }
}

pub fn x(p: AffinePoint) -> FieldElement {
    let (x, _) = p;
    x
}

pub fn y(p: AffinePoint) -> FieldElement {
    let (_, y) = p;
    y
}

pub fn has_even_y(p: AffinePoint) -> bool {
    y(p) % FieldElement::TWO() == FieldElement::ZERO()
}

fn sqrt(y: FieldElement) -> Option<FieldElement> {
    // This is the field element equal to (p+1)/4.
    #[rustfmt::skip]
    let p1_4 = FieldElement::from_public_byte_seq_be(PBytes32([
        0x3Fu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8,
        0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8,
        0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8,
        0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xBFu8, 0xFFu8, 0xFFu8, 0x0Cu8
    ]));
    let x = y.pow_self(p1_4);
    if x.pow_self(FieldElement::TWO()) == y {
        Some(x)
    } else {
        Option::<FieldElement>::None
    }
}

pub fn lift_x(x: FieldElement) -> Result<AffinePoint, Error> {
    let one = FieldElement::ONE();
    let two = FieldElement::TWO();
    let three = FieldElement::from_literal(3u128);
    let seven = FieldElement::from_literal(7u128);
    let y_sq = x.pow_self(three) + seven;
    let mut y = sqrt(y_sq).ok_or(Error::InvalidXCoordinate)?;
    if y % two == one {
        y = FieldElement::ZERO() - y;
    }
    Result::<AffinePoint, Error>::Ok((x, y))
}

fn compute_lam(p1_: AffinePoint, p2_: AffinePoint) -> FieldElement {
    let three = FieldElement::from_literal(3u128);
    if p1_ != p2_ {
        (y(p2_) - y(p1_)) * (x(p2_) - x(p1_)).pow_self(FieldElement::ZERO() - FieldElement::TWO())
    } else {
        three
            * x(p1_)
            * x(p1_)
            * (FieldElement::TWO() * y(p1_)).pow_self(FieldElement::ZERO() - FieldElement::TWO())
    }
}

pub fn point_add(p1: Point, p2: Point) -> Point {
    let mut result = Point::AtInfinity;
    if finite(p1).is_none() {
        result = p2
    } else {
        if finite(p2).is_none() {
            result = p1
        } else {
            let p1_ = finite(p1).unwrap();
            let p2_ = finite(p2).unwrap();
            if !((x(p1_) == x(p2_)) && (y(p1_) != y(p2_))) {
                let lam = compute_lam(p1_, p2_);
                let x3 = lam * lam - x(p1_) - x(p2_);
                result = Point::Affine((x3, (lam * (x(p1_) - x3) - y(p1_))));
            }
        }
    }
    result
}

pub fn point_mul(s: Scalar, p: Point) -> Point {
    let mut p = p;
    let mut q = Point::AtInfinity;
    for i in 0..256 {
        if s.bit(i) {
            q = point_add(q, p);
        }
        p = point_add(p, p);
    }
    q
}

pub fn point_mul_base(s: Scalar) -> Point {
    #[rustfmt::skip]
    let gx = PBytes32([
        0x79u8, 0xBEu8, 0x66u8, 0x7Eu8, 0xF9u8, 0xDCu8, 0xBBu8, 0xACu8,
        0x55u8, 0xA0u8, 0x62u8, 0x95u8, 0xCEu8, 0x87u8, 0x0Bu8, 0x07u8,
        0x02u8, 0x9Bu8, 0xFCu8, 0xDBu8, 0x2Du8, 0xCEu8, 0x28u8, 0xD9u8,
        0x59u8, 0xF2u8, 0x81u8, 0x5Bu8, 0x16u8, 0xF8u8, 0x17u8, 0x98u8
    ]);
    #[rustfmt::skip]
    let gy = PBytes32([
        0x48u8, 0x3Au8, 0xDAu8, 0x77u8, 0x26u8, 0xA3u8, 0xC4u8, 0x65u8,
        0x5Du8, 0xA4u8, 0xFBu8, 0xFCu8, 0x0Eu8, 0x11u8, 0x08u8, 0xA8u8,
        0xFDu8, 0x17u8, 0xB4u8, 0x48u8, 0xA6u8, 0x85u8, 0x54u8, 0x19u8,
        0x9Cu8, 0x47u8, 0xD0u8, 0x8Fu8, 0xFBu8, 0x10u8, 0xD4u8, 0xB8u8
    ]);
    let g = Point::Affine((
        FieldElement::from_public_byte_seq_be(gx),
        FieldElement::from_public_byte_seq_be(gy),
    ));
    point_mul(s, g)
}

bytes!(Bytes32, 32);
pub type SecretKey = Bytes32;
pub type PublicKey = Bytes32;
pub type Message = Bytes32;
pub type AuxRand = Bytes32;
bytes!(Signature, 64);

pub fn tagged_hash(tag: &PublicByteSeq, msg: &ByteSeq) -> Bytes32 {
    let tag_hash = sha256(&ByteSeq::from_public_seq(tag)).to_be_bytes();
    let hash = sha256(&tag_hash.concat(&tag_hash).concat(msg));
    Bytes32::from_seq(&hash)
}

public_bytes!(TaggedHashAuxPrefix, 11);
// string "BIP0340/aux"
const BIP0340_AUX: TaggedHashAuxPrefix = TaggedHashAuxPrefix([
    0x42u8, 0x49u8, 0x50u8, 0x30u8, 0x33u8, 0x34u8, 0x30u8, 0x2fu8, 0x61u8, 0x75u8, 0x78u8,
]);
pub fn hash_aux(aux_rand: AuxRand) -> Bytes32 {
    tagged_hash(
        &PublicByteSeq::from_seq(&BIP0340_AUX),
        &ByteSeq::from_seq(&aux_rand),
    )
}

public_bytes!(TaggedHashNoncePrefix, 13);
// string "BIP0340/nonce"
const BIP0340_NONCE: TaggedHashNoncePrefix = TaggedHashNoncePrefix([
    0x42u8, 0x49u8, 0x50u8, 0x30u8, 0x33u8, 0x34u8, 0x30u8, 0x2fu8, 0x6eu8, 0x6fu8, 0x6eu8, 0x63u8,
    0x65u8,
]);
pub fn hash_nonce(rand: Bytes32, pubkey: Bytes32, msg: Message) -> Bytes32 {
    let c: ByteSeq = ByteSeq::from_seq(&rand).concat(&pubkey).concat(&msg);
    tagged_hash(&PublicByteSeq::from_seq(&BIP0340_NONCE), &c)
}

public_bytes!(TaggedHashChallengePrefix, 17);
// string "BIP0340/challenge"
const BIP0340_CHALLENGE: TaggedHashChallengePrefix = TaggedHashChallengePrefix([
    0x42u8, 0x49u8, 0x50u8, 0x30u8, 0x33u8, 0x34u8, 0x30u8, 0x2fu8, 0x63u8, 0x68u8, 0x61u8, 0x6cu8,
    0x6cu8, 0x65u8, 0x6eu8, 0x67u8, 0x65u8,
]);
pub fn hash_challenge(rx: Bytes32, pubkey: Bytes32, msg: Bytes32) -> Bytes32 {
    let c: ByteSeq = ByteSeq::from_seq(&rx).concat(&pubkey).concat(&msg);
    tagged_hash(&PublicByteSeq::from_seq(&BIP0340_CHALLENGE), &c)
}

pub fn bytes_from_point(p: AffinePoint) -> Bytes32 {
    let (x, _) = p;
    Bytes32::from_seq(&x.to_byte_seq_be())
}

pub fn bytes_from_scalar(x: Scalar) -> Bytes32 {
    Bytes32::from_seq(&x.to_byte_seq_be())
}

pub fn scalar_from_bytes(b: Bytes32) -> Scalar {
    Scalar::from_byte_seq_be(&b)
}

pub fn scalar_from_bytes_strict(b: Bytes32) -> Option<Scalar> {
    let s = BigInteger::from_byte_seq_be(&b);
    let max_scalar = BigInteger::from_byte_seq_be(&Scalar::max_val().to_byte_seq_be());
    if s > max_scalar {
        Option::<Scalar>::None
    } else {
        Option::<Scalar>::Some(Scalar::from_byte_seq_be(&b))
    }
}

pub fn seckey_scalar_from_bytes(b: Bytes32) -> Option<Scalar> {
    let s = scalar_from_bytes_strict(b)?;
    if s == Scalar::ZERO() {
        Option::<Scalar>::None
    } else {
        Option::<Scalar>::Some(s)
    }
}

pub fn fieldelem_from_bytes(b: PublicKey) -> Option<FieldElement> {
    let s = BigInteger::from_byte_seq_be(&b);
    let max_fe = BigInteger::from_byte_seq_be(&FieldElement::max_val().to_byte_seq_be());
    if s > max_fe {
        Option::<FieldElement>::None
    } else {
        Option::<FieldElement>::Some(FieldElement::from_byte_seq_be(&b))
    }
}

fn xor_bytes(b0: Bytes32, b1: Bytes32) -> Bytes32 {
    let mut b = ByteSeq::new(b0.len());
    for i in 0..b0.len() {
        b[i] = b0[i] ^ b1[i];
    }
    Bytes32::from_seq(&b)
}

pub type PubkeyGenResult = Result<PublicKey, Error>;
pub fn pubkey_gen(seckey: SecretKey) -> PubkeyGenResult {
    let d0 = seckey_scalar_from_bytes(seckey).ok_or(Error::InvalidSecretKey)?;
    let p = finite(point_mul_base(d0)).unwrap();
    PubkeyGenResult::Ok(bytes_from_point(p))
}

pub type SignResult = Result<Signature, Error>;
pub fn sign(msg: Message, seckey: SecretKey, aux_rand: AuxRand) -> SignResult {
    let d0 = seckey_scalar_from_bytes(seckey).ok_or(Error::InvalidSecretKey)?;
    let p = finite(point_mul_base(d0)).unwrap();
    let d = if has_even_y(p) {
        d0
    } else {
        Scalar::ZERO() - d0
    };
    let t = xor_bytes(bytes_from_scalar(d), hash_aux(aux_rand));
    let k0 = scalar_from_bytes(hash_nonce(t, bytes_from_point(p), msg));
    if k0 == Scalar::ZERO() {
        // This happens only with negligible probability
        SignResult::Err(Error::InvalidNonceGenerated)?;
    }
    let r = finite(point_mul_base(k0)).unwrap();
    let k = if has_even_y(r) {
        k0
    } else {
        Scalar::ZERO() - k0
    };
    let e = scalar_from_bytes(hash_challenge(
        bytes_from_point(r),
        bytes_from_point(p),
        msg,
    ));
    let sig = Signature::new()
        .update(0, &bytes_from_point(r))
        .update(32, &bytes_from_scalar(k + e * d));
    verify(msg, bytes_from_point(p), sig)?;
    SignResult::Ok(sig)
}

pub type VerificationResult = Result<(), Error>;
pub fn verify(msg: Message, pubkey: PublicKey, sig: Signature) -> VerificationResult {
    let p_x = fieldelem_from_bytes(pubkey).ok_or(Error::InvalidPublicKey)?;
    let p = lift_x(p_x)?;
    let r =
        fieldelem_from_bytes(Bytes32::from_slice(&sig, 0, 32)).ok_or(Error::InvalidSignature)?;
    let s = scalar_from_bytes_strict(Bytes32::from_slice(&sig, 32, 32))
        .ok_or(Error::InvalidSignature)?;

    let e = scalar_from_bytes(hash_challenge(
        Bytes32::from_slice(&sig, 0, 32),
        bytes_from_point(p),
        msg,
    ));
    let r_p = finite(point_add(
        point_mul_base(s),
        point_mul(Scalar::ZERO() - e, Point::Affine(p)),
    ))
    .ok_or(Error::InvalidSignature)?;
    if !has_even_y(r_p) || (x(r_p) != r) {
        VerificationResult::Err(Error::InvalidSignature)
    } else {
        VerificationResult::Ok(())
    }
}
