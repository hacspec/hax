
// Import hacspec and all needed definitions.
use hacspec_lib::*;

use crate::*;
use noise_crypto::*;
use noise_lib::*;

pub struct HandshakeStateI0 {
    st:SymmetricState,
    psk:Seq<U8>,
    s:KeyPair,
    e:KeyPair,
    rs:Seq<U8>,
}

pub struct HandshakeStateI1 {
    st:SymmetricState,
    s:KeyPair,
    e:KeyPair
}

pub struct HandshakeStateR0 {
    st:SymmetricState,
    psk:Seq<U8>,
    s:KeyPair,
    e:KeyPair,
    rs:Seq<U8>,
}

pub struct HandshakeStateR1 {
    st:SymmetricState,
    e:KeyPair,
    rs:Seq<U8>,
    re:Seq<U8>
}

pub struct Transport {
    send: CipherState,
    recv: CipherState,
    handshake_hash: Seq<U8>
}

#[allow(non_upper_case_globals)]
const Noise_KKpsk0_25519_ChaChaPoly_SHA256: ProtocolName = ProtocolName(secret_bytes!([
                78u8, 111u8, 105u8, 115u8, 101u8,
                95u8, 75u8, 75u8, 112u8, 115u8,
                107u8, 48u8, 95u8, 50u8, 53u8, 53u8,
                49u8, 57u8, 95u8, 67u8, 104u8, 97u8,
                67u8, 104u8, 97u8, 80u8, 111u8,
                108u8, 121u8, 95u8, 83u8, 72u8, 65u8,
                50u8, 53u8, 54u8]));
              
///  KKpsk0:
///    -> s
///    <- s
///    ...
pub fn initialize_initiator(prologue:&Seq<U8>, psk:Seq<U8>, s: KeyPair, e:KeyPair, rs: &Seq<U8>) -> HandshakeStateI0 {
    let st = initialize_symmetric(&Seq::from_seq(&Noise_KKpsk0_25519_ChaChaPoly_SHA256));
    let st = mix_hash(st,prologue);
    let st = mix_hash(st,&Seq::from_seq(&s.public_key));
    let st = mix_hash(st,rs);
    HandshakeStateI0 {psk,st,s,e,rs:rs.clone()}
}

pub fn initialize_responder(prologue:&Seq<U8>, psk:Seq<U8>, s: KeyPair, e:KeyPair, rs: &Seq<U8>) -> HandshakeStateR0 {
    let st = initialize_symmetric(&Seq::from_seq(&Noise_KKpsk0_25519_ChaChaPoly_SHA256));
    let st = mix_hash(st,prologue);
    let st = mix_hash(st,rs);
    let st = mix_hash(st,&Seq::from_seq(&s.public_key));
    HandshakeStateR0 {st,psk,s,e,rs:rs.clone()}
}

///  KKpsk0:
///    ...
///    -> psk, e, es, ss
pub fn write_message1(hs:HandshakeStateI0,payload:&Seq<U8>) -> Result<(HandshakeStateI1,Seq<U8>),Error> {
    let HandshakeStateI0 {st,psk,s,e,rs} = hs;
    let st = mix_key_and_hash(st,&psk);
    let st = mix_hash(st,&e.public_key);
    let st = mix_key(st,&e.public_key);
    let es = dh(&e,&rs);
    let st = mix_key(st,&es);
    let ss = dh(&s,&rs);
    let st = mix_key(st,&ss);
    let (st,ciphertext) = encrypt_and_hash(st,payload)?;
    let hs = HandshakeStateI1 {st,s,e};
    Ok((hs,ciphertext))
}

pub fn read_message1(hs:HandshakeStateR0,ciphertext:&Seq<U8>) -> Result<(HandshakeStateR1,Seq<U8>),Error> {
    let HandshakeStateR0 {st,psk,s,e,rs} = hs;
    let re = ciphertext.slice(0,DHLEN);
    let ciphertext = ciphertext.slice(DHLEN,ciphertext.len()-DHLEN);
    let st = mix_key_and_hash(st,&psk);
    let st = mix_hash(st,&re);
    let st = mix_key(st,&re);
    let es = dh(&s,&re);
    let st = mix_key(st,&es);
    let ss = dh(&s,&rs);
    let st = mix_key(st,&ss);
    let (st,plaintext) = decrypt_and_hash(st,&ciphertext)?;
    let hs = HandshakeStateR1 {st,e,rs,re};
    Ok((hs,plaintext))
}

///  KKpsk0:
///    ...
///     <- e, ee, se
pub fn write_message2(hs:HandshakeStateR1,payload:&Seq<U8>) -> Result<(Transport,Seq<U8>),Error> {
    let HandshakeStateR1 {st,e,rs,re} = hs;
    let st = mix_hash(st,&e.public_key);
    let st = mix_key(st,&e.public_key);
    let ee = dh(&e,&re);
    let st = mix_key(st,&ee);
    let se = dh(&e,&rs);
    let st = mix_key(st,&se);
    let (st,ciphertext) = encrypt_and_hash(st,payload)?;
    let (c1,c2,h) = split(st);
    let tx = Transport {send:c2, recv:c1, handshake_hash:h};
    Ok((tx,ciphertext))
}

pub fn read_message2(hs:HandshakeStateI1,ciphertext:&Seq<U8>) -> Result<(Transport,Seq<U8>),Error> {
    let HandshakeStateI1 {st,s,e} = hs;
    let re = ciphertext.slice(0,DHLEN);
    let ciphertext = ciphertext.slice(DHLEN,ciphertext.len()-DHLEN);
    let st = mix_hash(st,&re);
    let st = mix_key(st,&re);
    let ee = dh(&e,&re);
    let st = mix_key(st,&ee);
    let se = dh(&s,&re);
    let st = mix_key(st,&se);
    let (st,plaintext) = decrypt_and_hash(st,&ciphertext)?;
    let (c1,c2,h) = split(st);
    let tx = Transport {send:c1, recv:c2, handshake_hash:h};
    Ok((tx,plaintext))
}

///  KKpsk0:
///    ->
///    <-
pub fn write_transport(tx:Transport,ad:&Seq<U8>,payload:&Seq<U8>) -> Result<(Transport,Seq<U8>),Error> {
    let Transport {send,recv,handshake_hash} = tx;
    let (send,ciphertext) = encrypt_with_ad(send,ad,payload)?;
    let tx = Transport {send,recv,handshake_hash};
    Ok((tx,ciphertext))
}

pub fn read_transport(tx:Transport,ad:&Seq<U8>,ciphertext:&Seq<U8>) -> Result<(Transport,Seq<U8>),Error> {
    let Transport {send,recv,handshake_hash} = tx;
    let (recv,payload) = decrypt_with_ad(recv,ad,ciphertext)?;
    let tx = Transport {send,recv,handshake_hash};
    Ok((tx,payload))
}