#![allow(non_snake_case)]
/*
 * This is a subset of Merlin. Merlin constructs and handles transcripts
 * for use in zero-knowledge protocols. It automates the fiat-shamir
 * transform so non-interactive protocols can be implemented as if
 * they were  interactive.
 *
 * This library implements most of the same functionality as the
 * original rust counterpart but excludes any rng elements.
 */

#![allow(non_snake_case)]

pub mod strobe;
use hacspec_lib::*;
use strobe::*;

pub type Transcript = Strobe;

fn MERLIN_PROTOCOL_LABEL() -> Seq<U8> {
	byte_seq!(77u8, 101u8, 114u8, 108u8, 105u8, 110u8, 32u8, 118u8, 49u8, 46u8, 48u8)
}

// === Internal Functions === //

// Turns a U64 into a byte sequence
fn encode_U64(x: U64) -> Seq<U8> {
	U64_to_le_bytes(x).to_le_bytes()
}

// Turns a usize into a byte sequence
fn encode_usize_as_u32(x: usize) -> Seq<U8> {
	let x_U32 = U32::classify(x as u32);
	U32_to_le_bytes(x_U32).to_le_bytes()
}

// === External Functions === //

/// Initialize a new transcript with the supplied label, which is used
/// as a domain separator.
pub fn new(label: Seq<U8>) -> Transcript {
	let transcript = new_strobe(MERLIN_PROTOCOL_LABEL());
	// b"dom-sep"
	let dom_sep = byte_seq!(100u8, 111u8, 109u8, 45u8, 115u8, 101u8, 112u8);

	append_message(transcript, dom_sep, label)
}

/// Append a prover's message to the transcript
///
/// The label parameter is metadata about the message, and is also
/// appended to the transcript. See the Transcript Protocols section of
/// the Merlin website for details on labels.
pub fn append_message(mut transcript: Transcript, label: Seq<U8>, message: Seq<U8>) -> Transcript {
	let data_len = U32_to_le_bytes(U32::classify(message.len() as u32)).to_be_bytes();

	transcript = meta_ad(transcript, label, false);
	transcript = meta_ad(transcript, data_len, true);
	transcript = ad(transcript, message, false);
	transcript
}

/// Fill the supplied buffer with the verifier's challenge bytes.
///
/// The label parameter is metadata about the challenge, and is also
/// appended to the transcript. See the Transcript Protocols section of
/// the Merlin website for details on labels.
///
/// https://merlin.cool/use/protocol.html
pub fn challenge_bytes(mut transcript: Transcript, label: Seq<U8>, dest: Seq<U8>) -> (Transcript, Seq<U8>) {
	let data_len = encode_usize_as_u32(dest.len());

	transcript = meta_ad(transcript, label, false);
	transcript = meta_ad(transcript, data_len, true);
	prf(transcript, dest, false)
}

/// Convenience method for appending a u64 to the transcript.
///
/// The label parameter is metadata about the message, and is also
/// appended to the transcript. See the Transcript Protocols section of
/// the Merlin website for details on labels.
///
/// https://merlin.cool/use/protocol.html
pub fn append_U64(transcript: Transcript, label: Seq<U8>, x: U64) -> Transcript {
	append_message(transcript, label, encode_U64(x))
}
