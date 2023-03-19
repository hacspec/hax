use hacspec_lib::*;
use hacspec_sha512::*;

public_nat_mod!(
    type_name: Ed25519FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"
);
public_nat_mod!(
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256,
    modulo_value: "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed"
);
public_nat_mod!(
    type_name: BigScalar,
    type_of_canvas: BigScalarCanvas,
    bit_size_of_field: 512,
    modulo_value: "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed"
);
public_nat_mod!(
    type_name: BigInteger,
    type_of_canvas: BigIntegerCanvas,
    bit_size_of_field: 256,
    modulo_value: "8000000000000000000000000000000080000000000000000000000000000000"
);

pub type EdPoint = (
    Ed25519FieldElement,
    Ed25519FieldElement,
    Ed25519FieldElement,
    Ed25519FieldElement,
);

bytes!(CompressedEdPoint, 32);
bytes!(SerializedScalar, 32);
bytes!(Signature, 64);

pub type PublicKey = CompressedEdPoint;
pub type SecretKey = SerializedScalar;

#[derive(Debug)]
pub enum Error {
    InvalidPublickey,
    InvalidSignature,
    InvalidS,
    InvalidR,
    SmallOrderPoint,
    NotEnoughRandomness,
}

pub type VerifyResult = Result<(), Error>;

#[rustfmt::skip]
pub const BASE: CompressedEdPoint = CompressedEdPoint(secret_array!(
    U8, 
    [
        0x58u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8,
        0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8,
        0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8,
        0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8 
    ]
));

#[rustfmt::skip]
const CONSTANT_P: SerializedScalar = SerializedScalar(secret_array!(
    U8, 
    [
        0xedu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0x7fu8 
    ]
));

#[rustfmt::skip]
const CONSTANT_L: SerializedScalar = SerializedScalar(secret_array!(
    U8, 
    [
        0xedu8, 0xd3u8, 0xf5u8, 0x5cu8, 0x1au8, 0x63u8, 0x12u8, 0x58u8,
        0xd6u8, 0x9cu8, 0xf7u8, 0xa2u8, 0xdeu8, 0xf9u8, 0xdeu8, 0x14u8,
        0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 
        0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x10u8 
    ]
));

#[rustfmt::skip]
const CONSTANT_P3_8: SerializedScalar = SerializedScalar(secret_array!(
    U8, 
    [
        0xfeu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0x0fu8 
    ]
));

#[rustfmt::skip]
const CONSTANT_P1_4: SerializedScalar = SerializedScalar(secret_array!(
    U8, 
    [
        0xfbu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0x1fu8 
    ]
));

#[rustfmt::skip]
const CONSTANT_D: SerializedScalar = SerializedScalar(secret_array!(
    U8, 
    [
        0xa3u8, 0x78u8, 0x59u8, 0x13u8, 0xcau8, 0x4du8, 0xebu8, 0x75u8, 
        0xabu8, 0xd8u8, 0x41u8, 0x41u8, 0x4du8, 0x0au8, 0x70u8, 0x00u8, 
        0x98u8, 0xe8u8, 0x79u8, 0x77u8, 0x79u8, 0x40u8, 0xc7u8, 0x8cu8, 
        0x73u8, 0xfeu8, 0x6fu8, 0x2bu8, 0xeeu8, 0x6cu8, 0x03u8, 0x52u8 
    ]
));

fn is_negative(x: Ed25519FieldElement) -> U8 {
    if x.bit(0) {
        U8(1u8)
    } else {
        U8(0u8)
    }
}

pub fn compress(p: EdPoint) -> CompressedEdPoint {
    let (x, y, z, _) = p;
    let z_inv = z.inv();
    let x = x * z_inv;
    let y = y * z_inv;
    let mut s: ByteSeq = y.to_byte_seq_le();
    s[31] = s[31] ^ (is_negative(x) << 7); // setting top bit
    CompressedEdPoint::from_slice(&s, 0, 32)
}

pub fn sqrt(a: Ed25519FieldElement) -> Option<Ed25519FieldElement> {
    let p3_8 = Ed25519FieldElement::from_byte_seq_le(CONSTANT_P3_8);
    let p1_4 = Ed25519FieldElement::from_byte_seq_le(CONSTANT_P1_4);

    let x_c = a.pow_self(p3_8);
    let mut result: Option<Ed25519FieldElement> = Option::<Ed25519FieldElement>::None;
    if x_c * x_c == a {
        result = Some(x_c);
    };
    if x_c * x_c == Ed25519FieldElement::ZERO() - a {
        let x = Ed25519FieldElement::TWO().pow_self(p1_4) * x_c;
        result = Some(x);
    }
    result
}

fn check_canonical_point(mut x: CompressedEdPoint) -> bool {
    x[31] = x[31] & U8(127u8);
    let x = BigInteger::from_byte_seq_le(x);
    x < BigInteger::from_byte_seq_le(CONSTANT_P)
}

pub fn decompress(q: CompressedEdPoint) -> Option<EdPoint> {
    let d = Ed25519FieldElement::from_byte_seq_le(CONSTANT_D);

    let x_s = (q[31usize] & U8(128u8)) >> 7;
    let mut y_s = q;
    y_s[31] = y_s[31] & U8(127u8);
    if !check_canonical_point(y_s) {
        Option::<EdPoint>::None?;
    }
    let y = Ed25519FieldElement::from_byte_seq_le(y_s);
    let z = Ed25519FieldElement::ONE();
    let yy = y * y;
    let u = yy - z;
    let v = d * yy + z;
    let xx = u * v.inv();
    let mut x = sqrt(xx)?;
    let x_r = is_negative(x);
    if x == Ed25519FieldElement::ZERO() && x_s.declassify() == 1u8 {
        Option::<EdPoint>::None?;
    }
    if x_r.declassify() != x_s.declassify() {
        x = Ed25519FieldElement::ZERO() - x;
    }
    Some((x, y, z, x * y))
}

// Allows decompression of non-canonical points
pub fn decompress_non_canonical(p: CompressedEdPoint) -> Option<EdPoint> {
    let d = Ed25519FieldElement::from_byte_seq_le(CONSTANT_D);

    let x_s = (p[31usize] & U8(128u8)) >> 7;
    let mut y_s = p;
    y_s[31] = y_s[31] & U8(127u8);
    let y = Ed25519FieldElement::from_byte_seq_le(y_s);
    let z = Ed25519FieldElement::ONE();
    let yy = y * y;
    let u = yy - z;
    let v = d * yy + z;
    let xx = u * v.inv();
    let mut x = sqrt(xx)?;
    let x_r = is_negative(x);
    if x_r.declassify() != x_s.declassify() {
        x = Ed25519FieldElement::ZERO() - x;
    }
    Some((x, y, z, x * y))
}

pub fn encode(p: EdPoint) -> ByteSeq {
    let (x, y, z, _) = p;
    let z_inv = z.inv();
    let x = x * z_inv;
    let y = y * z_inv;
    let mut s: ByteSeq = y.to_byte_seq_le();
    s[31] = s[31] ^ (is_negative(x) << 7); // setting top bit
    s
}

pub fn decode(q_s: ByteSeq) -> Option<EdPoint> {
    let q = CompressedEdPoint::from_slice(&q_s, 0, 32);
    decompress(q)
}

pub fn point_add(p: EdPoint, q: EdPoint) -> EdPoint {
    let d_c = Ed25519FieldElement::from_byte_seq_le(CONSTANT_D);
    let two = Ed25519FieldElement::TWO();

    let (x1, y1, z1, t1) = p;
    let (x2, y2, z2, t2) = q;
    let a = (y1 - x1) * (y2 - x2);
    let b = (y1 + x1) * (y2 + x2);
    let c = t1 * two * d_c * t2;
    let d = z1 * two * z2;
    let e = b - a;
    let f = d - c;
    let g = d + c;
    let h = b + a;
    let x3 = e * f;
    let y3 = g * h;
    let t3 = e * h;
    let z3 = f * g;
    (x3, y3, z3, t3)
}

pub fn point_identity() -> EdPoint {
    (
        Ed25519FieldElement::ZERO(),
        Ed25519FieldElement::ONE(),
        Ed25519FieldElement::ONE(),
        Ed25519FieldElement::ZERO(),
    )
}

pub fn point_mul(s: Scalar, p: EdPoint) -> EdPoint {
    let mut p = p;
    let mut q = point_identity();
    for i in 0..256 {
        if s.bit(i) {
            q = point_add(q, p);
        }
        p = point_add(p, p);
    }
    q
}

pub fn point_mul_by_cofactor(p: EdPoint) -> EdPoint {
    let p2 = point_add(p, p);
    let p4 = point_add(p2, p2);
    let p8 = point_add(p4, p4);
    p8
}

pub fn point_neg(p: EdPoint) -> EdPoint {
    let (x, y, z, t) = p;
    (
        Ed25519FieldElement::ZERO() - x,
        y,
        z,
        Ed25519FieldElement::ZERO() - t,
    )
}

pub fn point_eq(p: EdPoint, q: EdPoint) -> bool {
    let (x1, y1, z1, _) = p;
    let (x2, y2, z2, _) = q;
    x1 * z2 == x2 * z1 && y1 * z2 == y2 * z1
}

pub fn point_normalize(q: EdPoint) -> EdPoint {
    let (qx, qy, qz, _) = q;
    let px = qx * qz.inv();
    let py = qy * qz.inv();
    let pz = Ed25519FieldElement::ONE();
    let pt = px * py;
    (px, py, pz, pt)
}

pub fn secret_expand(sk: SecretKey) -> (SerializedScalar, SerializedScalar) {
    let h = sha512(&ByteSeq::from_slice(&sk, 0, 32));
    let h_d = SerializedScalar::from_slice(&h, 32, 32);
    let mut s = SerializedScalar::from_slice(&h, 0, 32);
    s[0] = s[0] & U8(248u8);
    s[31] = s[31] & U8(127u8);
    s[31] = s[31] | U8(64u8);
    (s, h_d)
}

pub fn secret_to_public(sk: SecretKey) -> PublicKey {
    let (s, _) = secret_expand(sk);
    let base = decompress(BASE).unwrap();
    let ss = Scalar::from_byte_seq_le(s);
    let a = point_mul(ss, base);
    compress(a)
}

pub fn check_canonical_scalar(s: SerializedScalar) -> bool {
    if (s[31usize] & U8(224u8)).declassify() != 0u8 {
        false
    } else {
        BigInteger::from_byte_seq_le(s) < BigInteger::from_byte_seq_le(CONSTANT_L)
    }
}
