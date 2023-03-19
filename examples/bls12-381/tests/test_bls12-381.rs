/* TO DO: Property Tests with associativity and distributive law */
use hacspec_bls12_381::*;

//Generators taken from:
//https://tools.ietf.org/id/draft-yonezawa-pairing-friendly-curves-02.html#rfc.section.4.2.2

//THIS IS A CORRECT G1 GENERATOR :)
fn g1() -> G1 {
    (Fp::from_hex("17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"),
    Fp::from_hex("08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1"), false)
}

//THIS IS A CORRECT G2 GENERATOR :)
fn g2() -> G2 {
    ((Fp::from_hex("24aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8"),
    Fp::from_hex("13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e")), 
    (Fp::from_hex("0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801"), 
    Fp::from_hex("0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be")), false)
}

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

#[test]
fn test_pairing_unitary() {
    let p = fp12conjugate(pairing(g1(), g2()));
    let q = pairing(g1(), g2neg(g2()));
    let r = pairing(g1neg(g1()), g2());
    assert_eq!(p, q);
    assert_eq!(q, r);
}
