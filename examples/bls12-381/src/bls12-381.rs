// BLS: y^2 = x^3 + 4

use hacspec_lib::*;

public_nat_mod!( //Custom Macro - defining a newtype with some functions - well defined macro's have library functions built in
    type_name: Fp,
    type_of_canvas: FpCanvas,
    bit_size_of_field: 384, //381 with 3 extra bits
    modulo_value: "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab" //0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
);

bytes!(SerializedFp, 48); //Represent points as arrays for easier testing
array!(ArrayFp, 6, U64);

public_nat_mod!( //Custom Macro - defining a new type with some functions - well defined macro's have library functions built in
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256,
    modulo_value: "8000000000000000000000000000000000000000000000000000000000000000" //0x8000000000000000000000000000000000000000000000000000000000000000
);

//bool is "isPointAtInfinity"
pub type G1 = (Fp, Fp, bool);
pub type Fp2 = (Fp, Fp); //(10, 8) = (10+8u) : u² = -1
pub type G2 = (Fp2, Fp2, bool);
pub type Fp6 = (Fp2, Fp2, Fp2); //v³ = u + 1
pub type Fp12 = (Fp6, Fp6); //w² = v

/* Arithmetic for FP2 elements */
pub fn fp2fromfp(n: Fp) -> Fp2 {
    (n, Fp::ZERO())
}

pub fn fp2zero() -> Fp2 {
    fp2fromfp(Fp::ZERO())
}

pub fn fp2neg(n: Fp2) -> Fp2 {
    let (n1, n2) = n;
    (Fp::ZERO() - n1, Fp::ZERO() - n2)
}

pub fn fp2add(n: Fp2, m: Fp2) -> Fp2 {
    //Coordinate wise
    let (n1, n2) = n;
    let (m1, m2) = m;
    (n1 + m1, n2 + m2)
}

pub fn fp2sub(n: Fp2, m: Fp2) -> Fp2 {
    fp2add(n, fp2neg(m))
}

pub fn fp2mul(n: Fp2, m: Fp2) -> Fp2 {
    //(a+bu)*(c+du) = ac + adu + bcu + bdu^2 = ac - bd + (ad + bc)u
    let (n1, n2) = n;
    let (m1, m2) = m;
    let x1 = (n1 * m1) - (n2 * m2);
    let x2 = (n1 * m2) + (n2 * m1);
    (x1, x2)
}

pub fn fp2inv(n: Fp2) -> Fp2 {
    let (n1, n2) = n;
    let t0 = n1 * n1 + (n2 * n2);
    let t1 = t0.inv();
    let x1 = n1 * t1;
    let x2 = Fp::ZERO() - (n2 * t1);
    (x1, x2)
}

pub fn fp2conjugate(n: Fp2) -> Fp2 {
    let (n1, n2) = n;
    (n1, Fp::ZERO() - n2)
}

/* Arithmetic for Fp6 elements */
//Algorithms from: https://eprint.iacr.org/2010/354.pdf
fn fp6fromfp2(n: Fp2) -> Fp6 {
    (n, fp2zero(), fp2zero())
}

fn fp6zero() -> Fp6 {
    fp6fromfp2(fp2zero())
}

fn fp6neg(n: Fp6) -> Fp6 {
    let (n1, n2, n3) = n;
    (
        fp2sub(fp2zero(), n1),
        fp2sub(fp2zero(), n2),
        fp2sub(fp2zero(), n3),
    )
}

fn fp6add(n: Fp6, m: Fp6) -> Fp6 {
    let (n1, n2, n3) = n;
    let (m1, m2, m3) = m;
    (fp2add(n1, m1), fp2add(n2, m2), fp2add(n3, m3))
}

fn fp6sub(n: Fp6, m: Fp6) -> Fp6 {
    fp6add(n, fp6neg(m))
}

fn fp6mul(n: Fp6, m: Fp6) -> Fp6 {
    let (n1, n2, n3) = n;
    let (m1, m2, m3) = m;
    let eps = (Fp::ONE(), Fp::ONE()); //1 + u
    let t1 = fp2mul(n1, m1);
    let t2 = fp2mul(n2, m2);
    let t3 = fp2mul(n3, m3);
    let t4 = fp2mul(fp2add(n2, n3), fp2add(m2, m3)); // (n2 + n3) * (m2 + m3)
    let t5 = fp2sub(fp2sub(t4, t2), t3); //t4 - t2 - t3
    let x = fp2add(fp2mul(t5, eps), t1); // t5 * eps + t1

    let t4 = fp2mul(fp2add(n1, n2), fp2add(m1, m2)); //(n1 + n2) * (m1 + m2)
    let t5 = fp2sub(fp2sub(t4, t1), t2); //t4 - t1 - t2
    let y = fp2add(t5, fp2mul(eps, t3)); //t5 + (eps * t3)

    let t4 = fp2mul(fp2add(n1, n3), fp2add(m1, m3)); //(n1 + n3) * (m1 + m3)
    let t5 = fp2sub(fp2sub(t4, t1), t3); //t4 - t1 - t3
    let z = fp2add(t5, t2); //t5 + t2
    (x, y, z)
}

fn fp6inv(n: Fp6) -> Fp6 {
    let (n1, n2, n3) = n;
    let eps = (Fp::ONE(), Fp::ONE()); //1 + u
    let t1 = fp2mul(n1, n1); //n1^2
    let t2 = fp2mul(n2, n2); //n2^2
    let t3 = fp2mul(n3, n3); //n3^2
    let t4 = fp2mul(n1, n2); //n1 * n2
    let t5 = fp2mul(n1, n3); //n1 * n3
    let t6 = fp2mul(n2, n3); //n2 * n3
    let x0 = fp2sub(t1, fp2mul(eps, t6)); //t1 - (eps * t6)
    let y0 = fp2sub(fp2mul(eps, t3), t4); //(eps * t3) - t4
    let z0 = fp2sub(t2, t5); //t2 - t5
    let t0 = fp2mul(n1, x0); //n1 * x0
    let t0 = fp2add(t0, fp2mul(eps, fp2mul(n3, y0))); //t0 + (eps * n3 * y0)
    let t0 = fp2add(t0, fp2mul(eps, fp2mul(n2, z0))); //t0 + (eps * n2 * z0)
    let t0 = fp2inv(t0); //t0^-1
    let x = fp2mul(x0, t0); //x0 * t0
    let y = fp2mul(y0, t0); // y0 * t0
    let z = fp2mul(z0, t0); // z0 * t0
    (x, y, z)
}

/* Arithmetic for Fp12 elements */
// Algorithms from: https://eprint.iacr.org/2010/354.pdf
pub fn fp12fromfp6(n: Fp6) -> Fp12 {
    (n, fp6zero())
}

pub fn fp12neg(n: Fp12) -> Fp12 {
    let (n1, n2) = n;
    (fp6sub(fp6zero(), n1), fp6sub(fp6zero(), n2))
}

pub fn fp12add(n: Fp12, m: Fp12) -> Fp12 {
    let (n1, n2) = n;
    let (m1, m2) = m;
    (fp6add(n1, m1), fp6add(n2, m2))
}

pub fn fp12sub(n: Fp12, m: Fp12) -> Fp12 {
    fp12add(n, fp12neg(m))
}

pub fn fp12mul(n: Fp12, m: Fp12) -> Fp12 {
    let (n1, n2) = n;
    let (m1, m2) = m;
    let gamma = (fp2zero(), fp2fromfp(Fp::ONE()), fp2zero()); //0 + v + 0 (c0, c1v, c2v^2)

    let t1 = fp6mul(n1, m1); //n1 * n2
    let t2 = fp6mul(n2, m2); //n2 * m2
    let x = fp6add(t1, fp6mul(t2, gamma)); //t1 + (t2 * gamma)
    let y = fp6mul(fp6add(n1, n2), fp6add(m1, m2)); //(n1 + n2) * (m1 + m2)
    let y = fp6sub(fp6sub(y, t1), t2); //y - t1 - t2
    (x, y)
}

pub fn fp12inv(n: Fp12) -> Fp12 {
    let (n1, n2) = n;
    let gamma = (fp2zero(), fp2fromfp(Fp::ONE()), fp2zero()); //0 + v + 0 (c0, c1v, c2v^2)

    let t1 = fp6mul(n1, n1); //n1^2
    let t2 = fp6mul(n2, n2); //n2^2
    let t1 = fp6sub(t1, fp6mul(gamma, t2)); //t1 - (gamma * t2)
    let t2 = fp6inv(t1); //t1^-1
    let x = fp6mul(n1, t2); //n1 * t2
    let y = fp6neg(fp6mul(n2, t2)); //-(n2 * t2)
    (x, y)
}

pub fn fp12exp(n: Fp12, k: Scalar) -> Fp12 {
    let mut c = fp12fromfp6(fp6fromfp2(fp2fromfp(Fp::ONE())));
    for i in 0..256 {
        //starting from second most significant bit
        c = fp12mul(c, c);
        if k.bit(255 - i) {
            c = fp12mul(c, n);
        }
    }
    c
}

pub fn fp12conjugate(n: Fp12) -> Fp12 {
    let (n1, n2) = n;
    (n1, fp6neg(n2))
}

pub fn fp12zero() -> Fp12 {
    fp12fromfp6(fp6zero())
}

/* Arithmetic in G1 */

//g1 add with no Point at Infinity
fn g1add_a(p: G1, q: G1) -> G1 {
    let (x1, y1, _) = p;
    let (x2, y2, _) = q;

    let x_diff = x2 - x1;
    let y_diff = y2 - y1;
    let xovery = y_diff * x_diff.inv(); //  x / y = x * y^-1
    let x3 = xovery.exp(2u32) - x1 - x2;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3, false)
}

//g1 double with no Point at Infinity
fn g1double_a(p: G1) -> G1 {
    let (x1, y1, _) = p;

    let x12 = x1.exp(2u32);
    let xovery = (Fp::from_literal(3u128) * x12) * (Fp::TWO() * y1).inv();
    let x3 = xovery.exp(2u32) - Fp::TWO() * x1;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3, false)
}
/* Wrapper functions with Point of Infinity */
pub fn g1double(p: G1) -> G1 {
    let (_x1, y1, inf1) = p;
    if y1 != Fp::ZERO() && !inf1 {
        g1double_a(p)
    } else {
        (Fp::ZERO(), Fp::ZERO(), true)
    }
}

pub fn g1add(p: G1, q: G1) -> G1 {
    let (x1, y1, inf1) = p;
    let (x2, y2, inf2) = q;

    if inf1 {
        q
    } else {
        if inf2 {
            p
        } else {
            if p == q {
                g1double(p)
            } else {
                if !(x1 == x2 && y1 == Fp::ZERO() - y2) {
                    g1add_a(p, q)
                } else {
                    (Fp::ZERO(), Fp::ZERO(), true)
                }
            }
        }
    }
}

pub fn g1mul(m: Scalar, p: G1) -> G1 {
    let mut t = (Fp::ZERO(), Fp::ZERO(), true);
    for i in 0..256 {
        //starting from second most significant bit
        t = g1double(t);
        if m.bit(255 - i) {
            t = g1add(t, p);
        }
    }
    t
}

pub fn g1neg(p: G1) -> G1 {
    let (x, y, inf) = p;
    (x, Fp::ZERO() - y, inf)
}

/* Arithmetic in G2 */
//g2 add without dealing with Point at Infinity
fn g2add_a(p: G2, q: G2) -> G2 {
    let (x1, y1, _) = p;
    let (x2, y2, _) = q;

    let x_diff = fp2sub(x2, x1);
    let y_diff = fp2sub(y2, y1);
    let xovery = fp2mul(y_diff, fp2inv(x_diff)); //  x / y = x * y^-1
    let t1 = fp2mul(xovery, xovery);
    let t2 = fp2sub(t1, x1);
    let x3 = fp2sub(t2, x2);
    let t1 = fp2sub(x1, x3);
    let t2 = fp2mul(xovery, t1);
    let y3 = fp2sub(t2, y1);
    (x3, y3, false)
}
//g2 double without dealing with Point at Infinity
fn g2double_a(p: G2) -> G2 {
    let (x1, y1, _) = p;

    let x12 = fp2mul(x1, x1);
    let t1 = fp2mul(fp2fromfp(Fp::from_literal(3u128)), x12);
    let t2 = fp2inv(fp2mul(fp2fromfp(Fp::TWO()), y1));
    let xovery = fp2mul(t1, t2);
    let t1 = fp2mul(xovery, xovery);
    let t2 = fp2mul(fp2fromfp(Fp::TWO()), x1);
    let x3 = fp2sub(t1, t2);
    let t1 = fp2sub(x1, x3);
    let t2 = fp2mul(xovery, t1);
    let y3 = fp2sub(t2, y1);
    (x3, y3, false)
}

/* Wrapper functions with Point at Infinity */
pub fn g2double(p: G2) -> G2 {
    let (_x1, y1, inf1) = p;
    if y1 != fp2zero() && !inf1 {
        g2double_a(p)
    } else {
        (fp2zero(), fp2zero(), true)
    }
}

pub fn g2add(p: G2, q: G2) -> G2 {
    let (x1, y1, inf1) = p;
    let (x2, y2, inf2) = q;

    if inf1 {
        q
    } else {
        if inf2 {
            p
        } else {
            if p == q {
                g2double(p)
            } else {
                if !(x1 == x2 && y1 == fp2neg(y2)) {
                    g2add_a(p, q)
                } else {
                    (fp2zero(), fp2zero(), true)
                }
            }
        }
    }
}

pub fn g2mul(m: Scalar, p: G2) -> G2 {
    let mut t = (fp2zero(), fp2zero(), true);
    for i in 0..256 {
        //starting from second most significant bit
        t = g2double(t);
        if m.bit(255 - i) {
            t = g2add(t, p);
        }
    }
    t
}

pub fn g2neg(p: G2) -> G2 {
    let (x, y, inf) = p;
    (x, fp2neg(y), inf)
}

//Curve twist, allowing us to work over Fp and Fp2, instead of Fp12
fn twist(p: G1) -> (Fp12, Fp12) {
    let (p0, p1, _) = p;
    let x = ((fp2zero(), fp2fromfp(p0), fp2zero()), fp6zero());
    let y = (fp6zero(), (fp2zero(), fp2fromfp(p1), fp2zero()));
    (x, y)
}

//Line double used in ate-pairing
fn line_double_p(r: G2, p: G1) -> Fp12 {
    let (r0, r1, _) = r;
    let a = fp2mul(fp2fromfp(Fp::from_literal(3u128)), fp2mul(r0, r0));
    let a = fp2mul(a, fp2inv(fp2mul(fp2fromfp(Fp::TWO()), r1)));
    let b = fp2sub(r1, fp2mul(a, r0));
    let a = fp12fromfp6(fp6fromfp2(a));
    let b = fp12fromfp6(fp6fromfp2(b));
    let (x, y) = twist(p);
    fp12neg(fp12sub(fp12sub(y, fp12mul(a, x)), b)) //y - ax - b
}

//Line addition, used in ate-pairing
fn line_add_p(r: G2, q: G2, p: G1) -> Fp12 {
    let (r0, r1, _) = r;
    let (q0, q1, _) = q;
    let a = fp2mul(fp2sub(q1, r1), fp2inv(fp2sub(q0, r0)));
    let b = fp2sub(r1, fp2mul(a, r0));
    let a = fp12fromfp6(fp6fromfp2(a));
    let b = fp12fromfp6(fp6fromfp2(b));
    let (x, y) = twist(p);
    fp12neg(fp12sub(fp12sub(y, fp12mul(a, x)), b)) //y - ax - b
}

//From https://eprint.iacr.org/2010/354.pdf
fn frobenius(f: Fp12) -> Fp12 {
    let ((g0, g1, g2), (h0, h1, h2)) = f;
    let t1 = fp2conjugate(g0);
    let t2 = fp2conjugate(h0);
    let t3 = fp2conjugate(g1);
    let t4 = fp2conjugate(h1);
    let t5 = fp2conjugate(g2);
    let t6 = fp2conjugate(h2);

    /* Funky way of storing gamma11 */

    //1904D3BF02BB0667 C231BEB4202C0D1F 0FD603FD3CBD5F4F 7B2443D784BAB9C4 F67EA53D63E7813D 8D0775ED92235FB8
    let c1 = ArrayFp(secret_array!(
        U64,
        [
            0x8D0775ED92235FB8u64,
            0xF67EA53D63E7813Du64,
            0x7B2443D784BAB9C4u64,
            0x0FD603FD3CBD5F4Fu64,
            0xC231BEB4202C0D1Fu64,
            0x1904D3BF02BB0667u64
        ]
    ));
    let c1 = ArrayFp::to_le_bytes(&c1);
    let c1 = Fp::from_byte_seq_le(c1);

    //00FC3E2B36C4E032 88E9E902231F9FB8 54A14787B6C7B36F EC0C8EC971F63C5F 282D5AC14D6C7EC2 2CF78A126DDC4AF3
    let c2 = ArrayFp(secret_array!(
        U64,
        [
            0x2CF78A126DDC4AF3u64,
            0x282D5AC14D6C7EC2u64,
            0xEC0C8EC971F63C5Fu64,
            0x54A14787B6C7B36Fu64,
            0x88E9E902231F9FB8u64,
            0x00FC3E2B36C4E032u64
        ]
    ));
    let c2 = ArrayFp::to_le_bytes(&c2);
    let c2 = Fp::from_byte_seq_le(c2);

    // gamma11 = (1+u)^((p-1) / 6)
    let gamma11 = (c1, c2);
    let gamma12 = fp2mul(gamma11, gamma11);
    let gamma13 = fp2mul(gamma12, gamma11);
    let gamma14 = fp2mul(gamma13, gamma11);
    let gamma15 = fp2mul(gamma14, gamma11);

    let t2 = fp2mul(t2, gamma11);
    let t3 = fp2mul(t3, gamma12);
    let t4 = fp2mul(t4, gamma13);
    let t5 = fp2mul(t5, gamma14);
    let t6 = fp2mul(t6, gamma15);

    ((t1, t3, t5), (t2, t4, t6))
}

fn final_exponentiation(f: Fp12) -> Fp12 {
    let fp6 = fp12conjugate(f); // f^p⁶
    let finv = fp12inv(f); //f^-1
    let fp6_1 = fp12mul(fp6, finv); //f^(p⁶-1)
    let fp8 = frobenius(frobenius(fp6_1)); //f^((p⁶-1)p²)
    let f = fp12mul(fp8, fp6_1); // f = f^((p⁶-1)(p²+1))

    let u = Scalar::from_literal(0xd201000000010000u128); //-u
    let u_half = Scalar::from_literal(0x6900800000008000u128); //u/2

    //Algorithm 2 from https://eprint.iacr.org/2016/130.pdf
    //Conjugations whenever u is used, since u is actually negative - and conjugation is enough (no inversion needed)
    let t0 = fp12mul(f, f); //f²
    let t1 = fp12exp(t0, u);
    let t1 = fp12conjugate(t1); //t0^u
    let t2 = fp12exp(t1, u_half);
    let t2 = fp12conjugate(t2); //t1^(u/2)
    let t3 = fp12conjugate(f); //f^-1
    let t1 = fp12mul(t3, t1); //t3t1

    let t1 = fp12conjugate(t1); //t1^-1
    let t1 = fp12mul(t1, t2); //t1t2

    let t2 = fp12exp(t1, u);
    let t2 = fp12conjugate(t2); //t1^u

    let t3 = fp12exp(t2, u);
    let t3 = fp12conjugate(t3); //t2^u
    let t1 = fp12conjugate(t1); //t1^-1
    let t3 = fp12mul(t1, t3); //t1t3

    let t1 = fp12conjugate(t1); //t1^-1
    let t1 = frobenius(frobenius(frobenius(t1))); //t1^p³
    let t2 = frobenius(frobenius(t2)); //t2^p²
    let t1 = fp12mul(t1, t2); //t1t2

    let t2 = fp12exp(t3, u);
    let t2 = fp12conjugate(t2); //t3^u
    let t2 = fp12mul(t2, t0); //t2t0
    let t2 = fp12mul(t2, f); //t2f

    let t1 = fp12mul(t1, t2); //t1t2
    let t2 = frobenius(t3); //t3^p
    let t1 = fp12mul(t1, t2); //t1t2
    t1
}
//ate-pairing used for BLS
pub fn pairing(p: G1, q: G2) -> Fp12 {
    let t = Scalar::from_literal(0xd201000000010000u128);
    let mut r = q;
    let mut f = fp12fromfp6(fp6fromfp2(fp2fromfp(Fp::ONE())));
    for i in 1..64 {
        let lrr = line_double_p(r, p);
        r = g2double(r);
        f = fp12mul(fp12mul(f, f), lrr);
        if t.bit(64 - i - 1) {
            let lrq = line_add_p(r, q, p);
            r = g2add(r, q);
            f = fp12mul(f, lrq);
        }
    }
    final_exponentiation(fp12conjugate(f)) //conjugation since t is actually negative
}

//###########################################################################
//Tests - type checker ignores #[cfg(test)] parts
#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
use quickcheck::*;

//Arbitrary implementation is needed to randomly generate arbitrary elements of the specified type. Used in Property based testing to generate random tests

/* Arbitrary Implementation used for Property Based Tests */
#[cfg(test)]
impl Arbitrary for Fp {
    fn arbitrary(g: &mut Gen) -> Fp {
        let mut a: [u64; 6] = [0; 6];
        for i in 0..6 {
            a[i] = u64::arbitrary(g);
        }
        let mut b: [u8; 48] = [0; 48];
        for i in 0..6 {
            let val: u64 = a[i];
            b[(i * 8)..((i + 1) * 8)].copy_from_slice(&(val.to_le_bytes()));
        }
        Fp::from_byte_seq_le(Seq::<U8>::from_public_slice(&b))
    }
}

/* Arbitrary Implementation used for Property Based Tests */
#[cfg(test)]
impl Arbitrary for Scalar {
    fn arbitrary(g: &mut Gen) -> Scalar {
        let mut a: [u64; 4] = [0; 4];
        for i in 0..4 {
            a[i] = u64::arbitrary(g);
        }
        let mut b: [u8; 32] = [0; 32];
        for i in 0..4 {
            let val: u64 = a[i];
            b[(i * 8)..((i + 1) * 8)].copy_from_slice(&(val.to_le_bytes()));
        }
        Scalar::from_byte_seq_le(Seq::<U8>::from_public_slice(&b))
    }
}

#[cfg(test)]
#[cfg(proof)]
#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements.
fn test_fp2_prop_add_neg(a: Fp2) -> bool {
    let b = fp2neg(a);
    fp2fromfp(Fp::ZERO()) == fp2add(a, b)
}

//Generating random numbers, taking inverse and multiplying - checking that random element times inverse gives one
#[cfg(test)]
#[cfg(proof)]
#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements.
fn test_fp2_prop_mul_inv(a: Fp2) -> bool {
    let b = fp2inv(a);
    fp2fromfp(Fp::ONE()) == fp2mul(a, b)
}

#[cfg(test)]
#[cfg(proof)]
#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements.
fn test_extraction_issue() -> bool {
    let b = fp2inv((Fp::ONE(), Fp::ONE()));
    fp2fromfp(Fp::ONE()) == fp2mul((Fp::ONE(), Fp::ONE()), b)
}

//Fp6 tests
#[cfg(test)]
#[cfg(proof)]
#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements.
fn test_fp6_prop_mul_inv(a: Fp6) -> bool {
    let b = fp6inv(a);
    fp6fromfp2(fp2fromfp(Fp::ONE())) == fp6mul(a, b)
}

#[cfg(test)]
#[cfg(proof)]
#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements.
fn test_fp6_prop_add_neg(a: Fp6) -> bool {
    let b = fp6neg(a);
    fp6fromfp2(fp2fromfp(Fp::ZERO())) == fp6add(a, b)
}

//Fp12 tests
#[cfg(test)]
#[cfg(proof)]
#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements.
fn test_fp12_prop_add_neg(a: Fp12) -> bool {
    let b = fp12neg(a);
    fp12fromfp6(fp6fromfp2(fp2fromfp(Fp::ZERO()))) == fp12add(a, b)
}

#[cfg(test)]
#[cfg(proof)]
#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements.
fn test_fp12_prop_mul_inv(a: Fp12) -> bool {
    let b = fp12inv(a);
    fp12fromfp6(fp6fromfp2(fp2fromfp(Fp::ONE()))) == fp12mul(a, b)
}

#[cfg(test)]
#[test]
fn test_fp12_exp_zero() {
    fn test_fp12_exp(a: Fp12) -> bool {
        fp12fromfp6(fp6fromfp2(fp2fromfp(Fp::ONE()))) == fp12exp(a, Scalar::ZERO())
    }
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_fp12_exp as fn(Fp12) -> bool);
}

#[cfg(test)]
#[test]
fn test_fp12_prop_exp() {
    fn test_fp12_exp(a: Fp12) -> bool {
        let m = Scalar::from_literal(3u128);
        let n = Scalar::from_literal(4u128);
        let k = Scalar::from_literal(12u128);
        fp12exp(fp12exp(a, m), n) == fp12exp(a, k)
    }
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_fp12_exp as fn(Fp12) -> bool);
}

/* G1 tests */
#[cfg(test)]
#[test]
fn test_g1_arithmetic() {
    let g = g1();

    let g2 = g1double(g);
    let g4a = g1double(g2);
    let g3 = g1add(g2, g);
    let g4b = g1add(g3, g);
    assert_eq!(g4a, g4b);
}

#[cfg(test)]
#[test]
fn test_g1_mul_standard()
{
    let g = g1();
    let m = Scalar::ONE();
    assert_eq!(g, g1mul(m, g));
    let m = Scalar::from_literal(2u128);
    let g2 = g1double(g);
    assert_eq!(g2, g1mul(m, g));
    let m = Scalar::from_literal(3u128);
    let g3 = g1add(g, g2);
    assert_eq!(g3, g1mul(m, g));
}

#[cfg(test)]
#[test]
fn test_g1_mul_zero()
{
    let g = g1();
    let m = Scalar::ZERO();
    let h = g1mul(m, g);
    assert!(h.2);
} 

#[cfg(test)]
#[test]
fn test_g1_mul_prop() {
    fn test_g1_mul(a: Scalar) -> bool {
        let g = g1mul(a, g1());
        let r =
            Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r
        let h = g1mul(r, g);
        h.2
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g1_mul as fn(Scalar) -> bool);
}

#[cfg(test)]
#[test]
fn test_g1_add_double_equiv() {
    fn test_g1_mul(a: Scalar) -> bool {
        let g = g1mul(a, g1());
        g1add(g, g) == g1double(g)
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g1_mul as fn(Scalar) -> bool);
}

#[cfg(test)]
#[test]
fn test_g1_add_double_special_case() {
    let g = (Fp::TWO(), Fp::ZERO(), false);
    assert_eq!(g1add(g, g), g1double(g));
}

//G2 tests
#[cfg(test)]
#[test]
fn test_g2_arithmetic() {
    let g = g2();

    let g2 = g2double(g);
    let g4a = g2double(g2);
    let g3 = g2add(g2, g);
    let g4b = g2add(g3, g);
    assert_eq!(g4a, g4b);
}

#[cfg(test)]
#[test]
fn test_g2_mul_standard()
{
    let g = g2();
    let m = Scalar::ONE();
    assert_eq!(g, g2mul(m, g));
    let m = Scalar::from_literal(2u128);
    let g2 = g2double(g);
    assert_eq!(g2, g2mul(m, g));
    let m = Scalar::from_literal(3u128);
    let g3 = g2add(g, g2);
    assert_eq!(g3, g2mul(m, g));
}

#[cfg(test)]
#[test]
fn test_g2_mul_zero()
{
    let g = g2();
    let m = Scalar::ZERO();
    let h = g2mul(m, g);
    assert!(h.2);
} 

#[cfg(test)]
#[test]
fn test_g2_mul_prop() {
    fn test_g2_mul(a: Scalar) -> bool {
        let g = g2mul(a, g2());
        let r =
            Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r
        let h = g2mul(r, g);
        h.2
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g2_mul as fn(Scalar) -> bool);
}

#[cfg(test)]
#[test]
fn test_g2_add_double_equiv() {
    fn test_g2_mul(a: Scalar) -> bool {
        let g = g2mul(a, g2());
        g2add(g, g) == g2double(g)
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g2_mul as fn(Scalar) -> bool);
}

#[cfg(test)]
#[test]
fn test_g2_add_double_special_case() {
    let g = (fp2fromfp(Fp::TWO()), fp2zero(), false);
    assert_eq!(g2add(g, g), g2double(g));
}

//Generators taken from:
//https://tools.ietf.org/id/draft-yonezawa-pairing-friendly-curves-02.html#rfc.section.4.2.2

//THIS IS A CORRECT G1 GENERATOR :)
#[cfg(test)]
fn g1() -> G1 {
    (Fp::from_hex("17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"),
     Fp::from_hex("08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1"), false)
}

//THIS IS A CORRECT G2 GENERATOR :)
#[cfg(test)]
fn g2() -> G2 {
    ((Fp::from_hex("24aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8"),
      Fp::from_hex("13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e")),
     (Fp::from_hex("0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801"),
      Fp::from_hex("0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be")), false)
}

//Testing the cofactor multiplication and integer times group element
#[cfg(test)]
#[test]
fn test_g1_generator() {
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r

    let aa = g1();
    let dd = g1mul(r, aa);
    assert!(dd.2);
}

#[cfg(test)]
#[test]
fn test_g2_generator() {
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r

    let a = g2();
    let b = g2mul(r, a);
    assert!(b.2);
}

#[cfg(test)]
#[quickcheck] //To Do: Property Quick-test
fn test_frob(a: Fp12) -> bool {
    let b = frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(
        frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(a)))))),
    ))))));
    let c = frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(a))))));
    a == b && a == fp12conjugate(c)
}

#[cfg(test)]
#[test]
fn test_pairing_bilinearity() {
    let a = Scalar::from_literal(9483274923u128);
    let b = Scalar::from_literal(124959043234u128);
    let c = a * b;

    let p = pairing(g1mul(a, g1()), g2mul(b, g2()));
    //e(a*g1, b*g2) = e(c*g1, g2) = e(g1, g1)*c with c = a * b
    assert_eq!(p, pairing(g1mul(c, g1()), g2()));
    //e(a*g1, b*g2) = e(g1, g2)^(a*b)
    assert_eq!(p, fp12exp(pairing(g1(), g2()), c));
}

#[cfg(test)]
#[test]
fn test_pairing_unitary() {
    let p = fp12conjugate(pairing(g1(), g2()));
    let q = pairing(g1(), g2neg(g2()));
    let r = pairing(g1neg(g1()), g2());
    assert_eq!(p, q);
    assert_eq!(q, r);
}

#[cfg(test)]
//Just a valid Fp12 point... Nothing special
fn fp12point() -> Fp12 {
    (((Fp::from_hex("12afbc6d6c71900c6228f0ec4a5ae91aa7747a0ddf39cde0062f71e950e716a8ae27ad686e700608f35e3f6c0fe0cf11"),
       Fp::from_hex("1660f8efaccc7a77268d7e17a31926b2d58879922f0d430c39c891867c64bc5baa8ed0f8350626ffb592eefa8248e536")),
      (Fp::from_hex("13792df9b2c7e814fc6308f1ae6d641d7ae658d99725318b86104868ea3cbf8b94b0c2d4393c86a9d36641d22d0464e8"),
       Fp::from_hex("16544b2b2595abd69b014bb2974cbc110787f2c4752b82c5460aaf9030eea1bce7ca11ebea791ba3622feb024b198431")),
      (Fp::from_hex("12236e4849c69ecded8037549af297183f7be830f54e417e7970dd014027bc7aafc6485397113e65cc3079d1cf6fb1ba"),
       Fp::from_hex("0934eeb51f85c8f0f34cb411a049ed9fe6215f775bebea5d757fb589dbd1821b2eb7c026f779ea0705b984764bbc3e22"))),
     ((Fp::from_hex("149f6bdeb04b4be589c319b54a03b43960dd59a9f1a27c575caa5bc95614db83fc2ac87b521c7a37573e85ae9cc11284"),
       Fp::from_hex("10bea874008cbcdf99d6f7e3dd03ee47106f2cf83597795795a30c2cc5a818af7ae2e6d0b00f0a0cd563c3d592332a7a")),
      (Fp::from_hex("0edda465a41e2be599242c5e78280ced388f4d7fb5d77c8b87bcc2665f024ede6c29cbaff8b710391d0fcde8d02618e1"),
       Fp::from_hex("0e8edc9ff2b93b5af140ff42e1b2998fd15dcb07d1af0e3b6a844c8b521c7885886ede9bff112cb5a35b4d9898ef65f9")),
      (Fp::from_hex("0b362f9cb09944d3f759991bfc72aafd9930f719cf5390164b32d859b4090cc251b8117255a8358ed19ba3026e45c5c0"),
       Fp::from_hex("005ffbaef16f69b249e9f9c81a913a9f1cc1c96154cfb89d00f769efcad52ef81aba95e1e3de33912e7a0f97b83972e5"))))
}

//  (f^((p^12-1)/r))^r = f^(p^12-1) = f^p^12*f^-1 = f*f^-1 = 1
#[cfg(test)]
#[test]
fn test_final_exponentiation_rth_root() {
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r
    let one = fp12fromfp6(fp6fromfp2(fp2fromfp(Fp::ONE())));
    let f = fp12point();
    let ffinal = final_exponentiation(f);
    let fr = fp12exp(ffinal, r);
    assert_eq!(fr, one);
}
