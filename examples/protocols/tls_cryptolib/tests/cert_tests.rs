use std::{
    fs::File,
    io::{BufReader, Read},
};

use hacspec_lib::*;
use tls_cryptolib::*;

const GOOGLE_COM_DER_FILE: &'static str = "tests/google-com.der";
const GOOGLE_COM_ECDSA_PK: &'static str = "27adafecc3e0e56a9af70fe47bcca23f5b250ba0b9238a2c38c77617b4a9f2fc09f302aec2a36c98888cf34fc4fa3bb85742b2c5bb4e2d76a1f75e42f78dbc31";

fn read_google_cert() -> Vec<u8> {
    let cert_file = File::open(GOOGLE_COM_DER_FILE).expect("Error opening cert file");
    let mut reader = BufReader::new(cert_file);
    let mut cert_buffer = Vec::new();
    reader
        .read_to_end(&mut cert_buffer)
        .expect("Error reading cert file");
    cert_buffer
}

#[test]
fn test_ecdsa_pk() {
    let cert_buffer = read_google_cert();
    let cert_bytes = ByteSeq::from_public_slice(&cert_buffer);
    let pk = verification_key_from_cert(&cert_bytes).expect("Error parsing ECDSA Google cert");
    assert_eq!(GOOGLE_COM_ECDSA_PK, pk.to_hex());
}
