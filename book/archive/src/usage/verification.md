# Verification

## Coq

### QuickCheck / QuickChick

You can test your hacspec code using [QuickCheck](https://github.com/BurntSushi/quickcheck) (a Rust library for randomized property-based testing), by simply implementing `quickcheck::Arbitrary` for the type you want to generate tests for. For example:
```rust,ignore
impl Arbitrary for Fp {
    fn arbitrary(g: &mut Gen) -> Fp {
        let mut a: [u64; 6] = [0; 6];
        for i in 0..6 {
            a[i] = u64::arbitrary(g);
        }
        let mut b: [u8; 48] = [0; 48];
        for i in 0..6 {
            let val: u64 = a[i];
            b[(i*8)..((i+1)*8)].copy_from_slice(&(val.to_le_bytes()));
        }
        Fp::from_byte_seq_le(Seq::<U8>::from_public_slice(&b))
    }
}
```
then you can use the `quickcheck` attribute, to make QuickCheck do property based testing for this function:
```rust,ignore
#[cfg(test)]
#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements.
fn test_fp2_prop_add_neg(a: Fp2) -> bool {
    let b = fp2neg(a);
    fp2fromfp(Fp::ZERO()) == fp2add(a, b)
}
```
which will run when you do `cargo test`. If you then add the tag `#[cfg(proof)]` and export to Coq,
```
cargo hacspec -o coq/src/<output_file_name>.v <input_crate_name>
```
then you get corresponding [QuickChick](https://github.com/QuickChick/QuickChick) test,
```
Definition test_fp2_prop_add_neg (a_320 : fp2) : bool :=
  let b_321 :=
    fp2neg (a_320) in
  (fp2fromfp (nat_mod_zero )) =.? (fp2add (a_320) (b_321)).

QuickChick (forAll g_fp2 (fun a_320 : fp2 =>test_fp2_prop_add_neg a_320)).
```
and generators will be constructed for the types automatically as,
```
Instance show_fp : Show (fp) := Build_Show (fp) (fun x => show (GZnZ.val _ x)).
Definition g_fp : G (fp) := @bindGen Z (fp) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_fp : Gen (fp) := Build_Gen fp g_fp.
```
which you can then run through coq in the folder `coq/`
```
coqc -R src/ Hacspec src/<output_file_name>.v
```
Make sure you run:
```
coqc -R src/ Hacspec src/MachineIntegers.v
coqc -R src/ Hacspec src/Lib.v
```
or `make` to generate the `.vo` files used by `<output_file_name>.v`.

For more information:
- on QuickCheck (in rust): [BurntSushi/quickcheck](https://github.com/BurntSushi/quickcheck)
- on QuickChick: [Software foundations book on QuickChick](https://softwarefoundations.cis.upenn.edu/qc-current/index.html)
