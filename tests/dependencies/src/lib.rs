use zeroize::Zeroize;

// XXX: Fails with &mut failures. The code from the derive macro should be ignored.
#[derive(Zeroize)]
pub struct Secret {
    s: [u8; 32],
}
