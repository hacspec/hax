// Import hacspec and all needed definitions.
use hacspec_lib::*;

fn build_irreducible(p: usize) -> Seq<i128> {
    let mut irr = Seq::<i128>::new(p + 1);
    irr[0] = -1i128;
    irr[1] = -1i128;
    irr[p] = 1i128;
    irr
}

/// First transform each coefficients to a value between −(q−1)/2 and (q−1)/2
/// then round it to the nearest multiple of 3
pub fn round_to_3(poly: &Seq<i128>, q: i128) -> Seq<i128> {
    let mut result = poly.clone();
    let q_12 = (q - 1i128) / 2i128;
    for i in 0..poly.len() {
        if poly[i] > q_12 {
            result[i] = poly[i] - q;
        }
    }
    for i in 0..result.len() {
        if result[i] % 3i128 != 0i128 {
            result[i] = result[i] - 1i128;
            if result[i] % 3i128 != 0i128 {
                result[i] = result[i] + 2i128;
            }
        }
    }
    result
}

/// r is the plaintext, h is the public key
fn encrypt(r: &Seq<i128>, h: &Seq<i128>, q: i128, irreducible: &Seq<i128>) -> Seq<i128> {
    let pre = mul_poly_irr(r, h, irreducible, q);
    round_to_3(&pre, q)
}

/// NTRU Prime 653 basic encryption
pub fn ntru_prime_653_encrypt(r: &Seq<i128>, h: &Seq<i128>) -> Seq<i128> {
    let p = 653;
    let q = 4621_i128;
    let _w = 288;
    let irreducible = build_irreducible(p);

    encrypt(r, h, q, &irreducible)
}

/// NTRU Prime 653 basic decryption
pub fn ntru_prime_653_decrypt(
    c: &Seq<i128>,
    key_f: &Seq<i128>,
    key_v: &Seq<i128>,
) -> (Seq<i128>, bool) {
    let p = 653;
    let q = 4621_i128;
    let _w = 288;
    let irreducible = build_irreducible(p);

    // calculate 3*f and 3*f*c
    let f_c = mul_poly_irr(key_f, c, &irreducible, q);
    let f_3_c_and_decryption_ok = poly_to_ring(
        &irreducible,
        &add_poly(&f_c, &add_poly(&f_c, &f_c, q), q),
        q,
    );
    let (f_3_c, ok_decrypt) = f_3_c_and_decryption_ok;
    let mut f_3_c = f_3_c;

    // view coefficients as values between -(q-1/2) and (q-1/2)
    let q_12 = (q - 1i128) / 2i128;
    for i in 0..f_3_c.len() {
        if f_3_c[i] > q_12 {
            f_3_c[i] = f_3_c[i] - q;
        }
    }

    // lift f_3_c to R_3
    let mut e = Seq::<i128>::new(f_3_c.len());
    for i in 0..e.len() {
        e[i] = f_3_c[i] % 3i128;
    }
    e = make_positive(&e, 3i128);

    // calculate e * v in R
    let mut r = mul_poly_irr(&e, key_v, &irreducible, 3i128);

    // to R_short
    for i in 0..r.len() {
        if r[i] == 2i128 {
            r[i] = -1i128;
        }
    }
    (r, ok_decrypt)
}
