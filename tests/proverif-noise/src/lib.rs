#![feature(proc_macro_hygiene)]
#[hax_lib_macros::exclude]
pub mod noise_crypto;
pub mod noise_kkpsk0;
#[hax_lib_macros::exclude]
pub mod noise_lib;
use hacspec_lib::*;
bytes!(ProtocolName, 36);
