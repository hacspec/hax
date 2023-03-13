use hacspec_lib::*;

public_nat_mod!(
    type_name: X25519FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"
);
public_nat_mod!(
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256,
    modulo_value: "8000000000000000000000000000000000000000000000000000000000000000"
);

type Point = (X25519FieldElement, X25519FieldElement);

bytes!(X25519SerializedPoint, 32);
bytes!(X25519SerializedScalar, 32);

fn mask_scalar(s: X25519SerializedScalar) -> X25519SerializedScalar {
    let mut k = s;
    k[0] = k[0] & U8(248u8);
    k[31] = k[31] & U8(127u8);
    k[31] = k[31] | U8(64u8);
    k
}

fn decode_scalar(s: X25519SerializedScalar) -> Scalar {
    let k = mask_scalar(s);
    Scalar::from_byte_seq_le(k)
}

fn decode_point(u: X25519SerializedPoint) -> Point {
    let mut u_ = u;
    u_[31] = u_[31] & U8(127u8);
    (
        X25519FieldElement::from_byte_seq_le(u_),
        X25519FieldElement::from_literal(1u128),
    )
}

fn encode_point(p: Point) -> X25519SerializedPoint {
    let (x, y) = p;
    let b = x * y.inv();
    X25519SerializedPoint::new().update_start(&b.to_byte_seq_le())
}

fn point_add_and_double(q: Point, np: (Point, Point)) -> (Point, Point) {
    let (nq, nqp1) = np;
    let (x_1, _z_1) = q;
    let (x_2, z_2) = nq;
    let (x_3, z_3) = nqp1;
    let a = x_2 + z_2;
    let aa = a.pow(2u128);
    let b = x_2 - z_2;
    let bb = b * b;
    let e = aa - bb;
    let c = x_3 + z_3;
    let d = x_3 - z_3;
    let da = d * a;
    let cb = c * b;

    let x_3 = (da + cb).pow(2u128);
    let z_3 = x_1 * ((da - cb).pow(2u128));
    let x_2 = aa * bb;
    let e121665 = X25519FieldElement::from_literal(121_665u128);
    let z_2 = e * (aa + (e121665 * e));
    ((x_2, z_2), (x_3, z_3))
}

fn swap(x: (Point, Point)) -> (Point, Point) {
    let (x0, x1) = x;
    (x1, x0)
}

fn montgomery_ladder(k: Scalar, init: Point) -> Point {
    let inf = (
        X25519FieldElement::from_literal(1u128),
        X25519FieldElement::from_literal(0u128),
    );
    let mut acc: (Point, Point) = (inf, init);
    for i in 0..256 {
        if k.bit(255 - i) {
            acc = swap(acc);
            acc = point_add_and_double(init, acc);
            acc = swap(acc);
        } else {
            acc = point_add_and_double(init, acc);
        }
    }
    let (out, _) = acc;
    out
}

pub fn x25519_scalarmult(
    s: X25519SerializedScalar,
    p: X25519SerializedPoint,
) -> X25519SerializedPoint {
    let s_ = decode_scalar(s);
    let p_ = decode_point(p);
    let r = montgomery_ladder(s_, p_);
    encode_point(r)
}

pub fn x25519_secret_to_public(s: X25519SerializedScalar) -> X25519SerializedPoint {
    let mut base = X25519SerializedPoint::new();
    base[0] = U8(0x09u8);
    x25519_scalarmult(s, base)
}
