# Proving properties

In the last chapter, we proved one property on the `square` function:
panic freedom. After adding a precondition, the signature of the
`square` function was `x:u8 -> Pure u8 (requires x <. 16uy) (ensures fun _ -> True)`.

This contract stipulates that, given a small input, the function will
_return a value_: it will not panic or diverge. We could enrich the
contract of `square` with a post-condition about the fact it is a
increasing function:

```rust,editable
#[hax_lib::requires(x < 16)]
#[hax_lib::ensures(|result| result >= x)]
fn square_ensures(x: u8) -> u8 {
    x * x
}
```

Such a simple post-condition is automatically proven by F\*. The
properties of our `square` function are not fascinating. Let's study a
more interesting example: [Barrett reduction](https://en.wikipedia.org/wiki/Barrett_reduction).

## A concrete example of contract: Barrett reduction

While the correctness of `square` is obvious, the Barrett reduction is
not.

Given `value` a field element (a `i32` whose absolute value is at most
`BARRET_R`), the function `barrett_reduce` defined below computes
`result` such that:

- `result ≡ value (mod FIELD_MODULUS)`;
- the absolute value of `result` is bound as follows:
  `|result| < FIELD_MODULUS`.

It is easy to write this contract directly as `hax::requires` and
`hax::ensures` annotations, as shown in the snippet below.

```rust,editable
type FieldElement = i32;
const FIELD_MODULUS: i32 = 3329;
const BARRETT_SHIFT: i64 = 26;
const BARRETT_R: i64 = 0x4000000; // 2^26
const BARRETT_MULTIPLIER: i64 = 20159; // ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋

#[hax_lib::requires((i64::from(value) >= -BARRETT_R && i64::from(value) <= BARRETT_R))]
#[hax_lib::ensures(|result| result > -FIELD_MODULUS && result < FIELD_MODULUS
                     && result %  FIELD_MODULUS ==  value % FIELD_MODULUS)]
fn barrett_reduce(value: i32) -> i32 {
    let t = i64::from(value) * BARRETT_MULTIPLIER;
    let t = t + (BARRETT_R >> 1);

    let quotient = t >> BARRETT_SHIFT;
    let quotient = quotient as i32;

    let sub = quotient * FIELD_MODULUS;

    // Here a lemma to prove that `(quotient * 3329) % 3329 = 0`
    // may have to be called in F*.

    value - sub
}
```

<!-- Note that we call to `cancel_mul_mod`, a lemma: in Rust, this have no
effect, but in F*, that establishes that `(quotient * 3329) % 3329` is
zero. -->

Before returning, a lemma may have to be called in F* to prove the correctness
of the reduction.
The lemma is `Math.Lemmas.cancel_mul_mod (v quotient) 3329;`, which establishes
that `(quotient * 3329) % 3329` is zero.
With the help of that one lemma, F\* is able to prove the
reduction computes the expected result.
(We may expose lemmas like this to call from Rust directly in future.)

This Barrett reduction examples is taken from
[libcrux](https://github.com/cryspen/libcrux/tree/main)'s proof of
Kyber which is using hax and F\*.

This example showcases an **intrinsic proof**: the function
`barrett_reduce` not only computes a value, but it also ship a proof
that the post-condition holds. The pre-condition and post-condition
gives the function a formal specification, which is useful both for
further formal verification and for documentation purposes.

## Extrinsic properties with lemmas

Consider the `encrypt` and `decrypt` functions below. Those functions
have no precondition, don't have particularly interesting properties
individually. However, the composition of the two yields an useful
property: encrypting a ciphertext and decrypting the result with a
same key produces the ciphertext again. `|c| decrypt(c, key)` is the
inverse of `|p| encrypt(p, key)`.

```rust,editable
fn encrypt(plaintext: u32, key: u32) -> u32 {
    plaintext ^ key
}

fn decrypt(ciphertext: u32, key: u32) -> u32 {
    ciphertext ^ key
}
```

In this situation, adding a pre- or a post-condition to either
`encrypt` or `decrypt` is not useful: we want to state our inverse
property about both of them. Better, we want this property to be
stated directly in Rust: just as with pre and post-conditions, the
Rust souces should clearly state what is to be proven.

To this end, Hax provides a macro `lemma`. Below, the Rust function
`encrypt_decrypt_identity` takes a key and a plaintext, and then
states the inverse property. The body is empty: the details of the
proof itself are not relevant, at this stage, we only care about the
statement. The proof will be completed manually in the proof
assistant.

```rust,editable
# fn encrypt(plaintext: u32, key: u32) -> u32 {
#     plaintext ^ key
# }
# 
# fn decrypt(ciphertext: u32, key: u32) -> u32 {
#     ciphertext ^ key
# }
# 
#[hax_lib::lemma]
#[hax_lib::requires(true)]
fn encrypt_decrypt_identity(
    key: u32,
    plaintext: u32,
) -> Proof<{ decrypt(encrypt(plaintext, key), key) == plaintext }> {
}
```
