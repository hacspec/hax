# Arithmetic

hacspec overloads the arithmetic operators for a wide variety of types
corresponding to mathematical values mentioned in cryptographic specifications.

## The `Numeric` trait

All of these types implement the `Numeric` trait defined by the hacspec standard
library. The arithmetic operators work for all kinds of integers, but also
arrays and sequences (point-wise operations).

Note that the list of types implementing `Numeric` is hardcoded in the
hacspec compiler, and as of this day cannot be extended by the user.

While the Rust compiler can infer the type of integer literals automatically,
this feature is not implemented by the hacspec compiler:

```
let w: u32 = 0; // ERROR: an integer without a suffix will have type usize
let x: u64 = 0x64265u64; // GOOD
let y: u64 = 4u64; // GOOD
```

## Public and secret integers

One of hacspec's goal is to enable users to quickly check whether their
application does not obviously break the constant-time guarantee.
Certain processor instructions take more or less time to complete depending
on their inputs, which can cause secret leakage and break the security of
an application. Hence, hacspec offers for each type of integer (`u8`, `u32`, etc.)
a mirror secret integer type (`U8`, `U32`, etc.) for which operations
that break constant-timedness are forbidden.

This public/private distinction can be found at a lot of places in the standard
library, and is made to forbid functions and data structures from leaking secrets.

Conversions between public and secret integers are restricted to two functions:
`classify` and `declassify`.

## Abstract integers

Some cryptographic specifications talk about modular arithmetic in large
fields, whose size overflows even `u128`. To ease the expression of such
specifications, hacspec offers wrapper types around `BigInt` that can be
declared using the following API:

```rust, noplaypen
abstract_nat_mod!(
    NameOfModularInts,
    NameOfUnderlyingByteRepresentation,
    256, // Number of bits for the representation of the big integer,
    "ffffffffffffffff00000000000065442", // Hex representation of the modulo value as hex
)

abstract_public_nat_mod!(
    ... // Public version of above
)
```

## Integers as bytes

It is often useful to view an integer as a sequence of bytes that can be
manipulated individually. The hacspec standard library provides a number
of function to translate back and forth from integer to sequence of bytes:

```rust, noplaypen
pub fn u16_to_le_bytes(x: u16) -> u16Word;

pub fn u16_from_le_bytes(s: u16Word) -> u16;

pub fn U64_to_be_bytes(x: U64) -> U64Word;

pub fn U64_from_be_bytes(s: U64Word) -> U64;

...
```
