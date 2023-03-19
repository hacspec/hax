use hacspec_lib::*;

#[derive(Debug)]
pub enum Error {
    InvalidAddition,
}

const BITS: usize = 256;

public_nat_mod!(
    type_name: P256FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256, // XXX: Unfortunately we can't use constants here.
    modulo_value: "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"
);

public_nat_mod!(
    type_name: P256Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256, // XXX: Unfortunately we can't use constants here.
    modulo_value: "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"
);

pub type Affine = (P256FieldElement, P256FieldElement);
pub type AffineResult = Result<Affine, Error>;
type P256Jacobian = (P256FieldElement, P256FieldElement, P256FieldElement);
type JacobianResult = Result<P256Jacobian, Error>;

bytes!(Element, 32);

fn jacobian_to_affine(p: P256Jacobian) -> Affine {
    let (x, y, z) = p;
    let z2 = z.exp(2u32);
    let z2i = z2.inv();
    let z3 = z * z2;
    let z3i = z3.inv();
    let x = x * z2i;
    let y = y * z3i;
    (x, y)
}

fn affine_to_jacobian(p: Affine) -> P256Jacobian {
    let (x, y) = p;
    (x, y, P256FieldElement::from_literal(1u128))
}

fn point_double(p: P256Jacobian) -> P256Jacobian {
    let (x1, y1, z1) = p;
    let delta = z1.exp(2u32);
    let gamma = y1.exp(2u32);

    let beta = x1 * gamma;

    let alpha_1 = x1 - delta;
    let alpha_2 = x1 + delta;
    let alpha = P256FieldElement::from_literal(3u128) * (alpha_1 * alpha_2);

    let x3 = alpha.exp(2u32) - (P256FieldElement::from_literal(8u128) * beta);

    let z3_ = (y1 + z1).exp(2u32);
    let z3 = z3_ - (gamma + delta);

    let y3_1 = (P256FieldElement::from_literal(4u128) * beta) - x3;
    let y3_2 = P256FieldElement::from_literal(8u128) * (gamma * gamma);
    let y3 = (alpha * y3_1) - y3_2;
    (x3, y3, z3)
}

fn is_point_at_infinity(p: P256Jacobian) -> bool {
    let (_x, _y, z) = p;
    z.equal(P256FieldElement::from_literal(0u128))
}

fn s1_equal_s2(s1: P256FieldElement, s2: P256FieldElement) -> JacobianResult {
    if s1.equal(s2) {
        JacobianResult::Err(Error::InvalidAddition)
    } else {
        JacobianResult::Ok((
            P256FieldElement::from_literal(0u128),
            P256FieldElement::from_literal(1u128),
            P256FieldElement::from_literal(0u128),
        ))
    }
}

fn point_add_jacob(p: P256Jacobian, q: P256Jacobian) -> JacobianResult {
    let mut result = JacobianResult::Ok(q);
    if !is_point_at_infinity(p) {
        if is_point_at_infinity(q) {
            result = JacobianResult::Ok(p);
        } else {
            let (x1, y1, z1) = p;
            let (x2, y2, z2) = q;
            let z1z1 = z1.exp(2u32);
            let z2z2 = z2.exp(2u32);
            let u1 = x1 * z2z2;
            let u2 = x2 * z1z1;
            let s1 = (y1 * z2) * z2z2;
            let s2 = (y2 * z1) * z1z1;

            if u1.equal(u2) {
                result = s1_equal_s2(s1, s2);
            } else {
                let h = u2 - u1;
                let i = (P256FieldElement::from_literal(2u128) * h).exp(2u32);
                let j = h * i;
                let r = P256FieldElement::from_literal(2u128) * (s2 - s1);
                let v = u1 * i;

                let x3_1 = P256FieldElement::from_literal(2u128) * v;
                let x3_2 = r.exp(2u32) - j;
                let x3 = x3_2 - x3_1;

                let y3_1 = (P256FieldElement::from_literal(2u128) * s1) * j;
                let y3_2 = r * (v - x3);
                let y3 = y3_2 - y3_1;

                let z3_ = (z1 + z2).exp(2u32);
                let z3 = (z3_ - (z1z1 + z2z2)) * h;
                result = JacobianResult::Ok((x3, y3, z3));
            }
        }
    };
    result
}

fn ltr_mul(k: P256Scalar, p: P256Jacobian) -> JacobianResult {
    let mut q = (
        P256FieldElement::from_literal(0u128),
        P256FieldElement::from_literal(1u128),
        P256FieldElement::from_literal(0u128),
    );
    for i in 0..BITS {
        q = point_double(q);
        if k.get_bit(BITS - 1 - i).equal(P256Scalar::ONE()) {
            q = point_add_jacob(q, p)?;
        }
    }
    JacobianResult::Ok(q)
}

pub fn p256_point_mul(k: P256Scalar, p: Affine) -> AffineResult {
    let jac = ltr_mul(k, affine_to_jacobian(p))?;
    AffineResult::Ok(jacobian_to_affine(jac))
}

pub fn p256_point_mul_base(k: P256Scalar) -> AffineResult {
    let base_point = (
        P256FieldElement::from_byte_seq_be(&Element(secret_bytes!([
            0x6Bu8, 0x17u8, 0xD1u8, 0xF2u8, 0xE1u8, 0x2Cu8, 0x42u8, 0x47u8, 0xF8u8, 0xBCu8, 0xE6u8,
            0xE5u8, 0x63u8, 0xA4u8, 0x40u8, 0xF2u8, 0x77u8, 0x03u8, 0x7Du8, 0x81u8, 0x2Du8, 0xEBu8,
            0x33u8, 0xA0u8, 0xF4u8, 0xA1u8, 0x39u8, 0x45u8, 0xD8u8, 0x98u8, 0xC2u8, 0x96u8
        ]))),
        P256FieldElement::from_byte_seq_be(&Element(secret_bytes!([
            0x4Fu8, 0xE3u8, 0x42u8, 0xE2u8, 0xFEu8, 0x1Au8, 0x7Fu8, 0x9Bu8, 0x8Eu8, 0xE7u8, 0xEBu8,
            0x4Au8, 0x7Cu8, 0x0Fu8, 0x9Eu8, 0x16u8, 0x2Bu8, 0xCEu8, 0x33u8, 0x57u8, 0x6Bu8, 0x31u8,
            0x5Eu8, 0xCEu8, 0xCBu8, 0xB6u8, 0x40u8, 0x68u8, 0x37u8, 0xBFu8, 0x51u8, 0xF5u8
        ]))),
    );
    p256_point_mul(k, base_point)
}

fn point_add_distinct(p: Affine, q: Affine) -> AffineResult {
    let r = point_add_jacob(affine_to_jacobian(p), affine_to_jacobian(q))?;
    AffineResult::Ok(jacobian_to_affine(r))
}

#[allow(unused_assignments)]
pub fn point_add(p: Affine, q: Affine) -> AffineResult {
    if p != q {
        point_add_distinct(p, q)
    } else {
        AffineResult::Ok(jacobian_to_affine(point_double(affine_to_jacobian(p))))
    }
}

/// Verify that k != 0 && k < ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
pub fn p256_validate_private_key(k: &ByteSeq) -> bool {
    let mut valid = true;
    // XXX: This should fail.
    let k_element = P256Scalar::from_byte_seq_be(k);
    let k_element_bytes = k_element.to_byte_seq_be();
    let mut all_zero = true;
    for i in 0..k.len() {
        if !k[i].equal(U8(0u8)) {
            all_zero = false;
        }
        if !k_element_bytes[i].equal(k[i]) {
            valid = false;
        }
    }
    valid && !all_zero
}

/// Verify that the point `p` is a valid public key.
pub fn p256_validate_public_key(p: Affine) -> bool {
    let b = P256FieldElement::from_byte_seq_be(&byte_seq!(
        0x5au8, 0xc6u8, 0x35u8, 0xd8u8, 0xaau8, 0x3au8, 0x93u8, 0xe7u8, 0xb3u8, 0xebu8, 0xbdu8,
        0x55u8, 0x76u8, 0x98u8, 0x86u8, 0xbcu8, 0x65u8, 0x1du8, 0x06u8, 0xb0u8, 0xccu8, 0x53u8,
        0xb0u8, 0xf6u8, 0x3bu8, 0xceu8, 0x3cu8, 0x3eu8, 0x27u8, 0xd2u8, 0x60u8, 0x4bu8
    ));
    let point_at_infinity = is_point_at_infinity(affine_to_jacobian(p));
    let (x, y) = p;
    let on_curve = y * y == x * x * x - P256FieldElement::from_literal(3u128) * x + b;

    !point_at_infinity && on_curve
}

// Calculate w, which is -y or +y, from x. See RFC 6090, Appendix C.
pub fn p256_calculate_w(x: P256FieldElement) -> P256FieldElement {
    let b = P256FieldElement::from_byte_seq_be(&byte_seq!(
        0x5au8, 0xc6u8, 0x35u8, 0xd8u8, 0xaau8, 0x3au8, 0x93u8, 0xe7u8, 0xb3u8, 0xebu8, 0xbdu8,
        0x55u8, 0x76u8, 0x98u8, 0x86u8, 0xbcu8, 0x65u8, 0x1du8, 0x06u8, 0xb0u8, 0xccu8, 0x53u8,
        0xb0u8, 0xf6u8, 0x3bu8, 0xceu8, 0x3cu8, 0x3eu8, 0x27u8, 0xd2u8, 0x60u8, 0x4bu8
    ));
    // (p+1)/4 calculated offline
    let exp = P256FieldElement::from_byte_seq_be(&byte_seq!(
        0x3fu8, 0xffu8, 0xffu8, 0xffu8, 0xc0u8, 0x00u8, 0x00u8, 0x00u8, 0x40u8, 0x00u8, 0x00u8,
        0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x40u8, 0x00u8,
        0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8
    ));
    // w = (x^3 + a*x + b)^((p+1)/4) (mod p). [RFC6090, Appendix C]
    let z = x * x * x - P256FieldElement::from_literal(3u128) * x + b;
    // z to power of exp
    let w = z.pow_felem(exp);
    w
}
