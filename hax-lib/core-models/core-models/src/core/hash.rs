// F* traits have no provided methods: there, `HasherDefaults` provides them.
// DEVIATION(std): they write little-endian bytes where std writes native-endian ones,
// and `write_usize` always writes 8 bytes where std writes `size_of::<usize>()`.
/// See [`std::hash::Hasher`]
#[hax_lib::attributes]
pub trait Hasher {
    /// See [`std::hash::Hasher::finish`]
    #[hax_lib::requires(true)]
    fn finish(&self) -> u64;
    /// See [`std::hash::Hasher::write`]
    #[hax_lib::requires(true)]
    fn write(&mut self, bytes: &[u8]);
    /// See [`std::hash::Hasher::write_u8`]
    #[cfg(not(hax_backend_fstar))]
    fn write_u8(&mut self, i: u8) {
        self.write(&[i])
    }
    /// See [`std::hash::Hasher::write_u16`]
    #[cfg(not(hax_backend_fstar))]
    fn write_u16(&mut self, i: u16) {
        self.write(&[i as u8, (i >> 8) as u8])
    }
    /// See [`std::hash::Hasher::write_u32`]
    #[cfg(not(hax_backend_fstar))]
    fn write_u32(&mut self, i: u32) {
        self.write(&[i as u8, (i >> 8) as u8, (i >> 16) as u8, (i >> 24) as u8])
    }
    /// See [`std::hash::Hasher::write_u64`]
    #[cfg(not(hax_backend_fstar))]
    fn write_u64(&mut self, i: u64) {
        self.write(&[
            i as u8,
            (i >> 8) as u8,
            (i >> 16) as u8,
            (i >> 24) as u8,
            (i >> 32) as u8,
            (i >> 40) as u8,
            (i >> 48) as u8,
            (i >> 56) as u8,
        ])
    }
    /// See [`std::hash::Hasher::write_u128`]
    #[cfg(not(hax_backend_fstar))]
    fn write_u128(&mut self, i: u128) {
        self.write(&[
            i as u8,
            (i >> 8) as u8,
            (i >> 16) as u8,
            (i >> 24) as u8,
            (i >> 32) as u8,
            (i >> 40) as u8,
            (i >> 48) as u8,
            (i >> 56) as u8,
            (i >> 64) as u8,
            (i >> 72) as u8,
            (i >> 80) as u8,
            (i >> 88) as u8,
            (i >> 96) as u8,
            (i >> 104) as u8,
            (i >> 112) as u8,
            (i >> 120) as u8,
        ])
    }
    /// See [`std::hash::Hasher::write_usize`]
    // Through `u64`, as Lean leaves the width of `usize` open and so cannot show
    // its shifts by 32 and more to succeed.
    #[cfg(not(hax_backend_fstar))]
    fn write_usize(&mut self, i: usize) {
        let i = i as u64;
        self.write(&[
            i as u8,
            (i >> 8) as u8,
            (i >> 16) as u8,
            (i >> 24) as u8,
            (i >> 32) as u8,
            (i >> 40) as u8,
            (i >> 48) as u8,
            (i >> 56) as u8,
        ])
    }
    /// See [`std::hash::Hasher::write_i8`]
    #[cfg(not(hax_backend_fstar))]
    fn write_i8(&mut self, i: i8) {
        Hasher::write_u8(self, i as u8)
    }
    /// See [`std::hash::Hasher::write_i16`]
    #[cfg(not(hax_backend_fstar))]
    fn write_i16(&mut self, i: i16) {
        Hasher::write_u16(self, i as u16)
    }
    /// See [`std::hash::Hasher::write_i32`]
    #[cfg(not(hax_backend_fstar))]
    fn write_i32(&mut self, i: i32) {
        Hasher::write_u32(self, i as u32)
    }
    /// See [`std::hash::Hasher::write_i64`]
    #[cfg(not(hax_backend_fstar))]
    fn write_i64(&mut self, i: i64) {
        Hasher::write_u64(self, i as u64)
    }
    /// See [`std::hash::Hasher::write_i128`]
    #[cfg(not(hax_backend_fstar))]
    fn write_i128(&mut self, i: i128) {
        Hasher::write_u128(self, i as u128)
    }
    /// See [`std::hash::Hasher::write_isize`]
    #[cfg(not(hax_backend_fstar))]
    fn write_isize(&mut self, i: isize) {
        Hasher::write_usize(self, i as usize)
    }
    /// See [`std::hash::Hasher::write_length_prefix`]
    #[cfg(not(hax_backend_fstar))]
    fn write_length_prefix(&mut self, len: usize) {
        Hasher::write_usize(self, len)
    }
    /// See [`std::hash::Hasher::write_str`]
    #[cfg(not(hax_backend_fstar))]
    fn write_str(&mut self, s: &str) {
        self.write(rust_primitives::string::str_as_bytes(s));
        Hasher::write_u8(self, 0xff)
    }
}

/// See [`std::hash::Hash`]
#[hax_lib::attributes]
pub trait Hash {
    /// See [`std::hash::Hash::hash`]
    #[hax_lib::requires(true)]
    fn hash<H: Hasher>(&self, state: &mut H);
    /// See [`std::hash::Hash::hash_slice`]
    // F* has no default methods: there, `HashDefaults` provides it.
    #[cfg(not(hax_backend_fstar))]
    fn hash_slice<H: Hasher>(data: &[Self], state: &mut H)
    where
        Self: Sized,
    {
        let mut i = 0;
        while i < rust_primitives::slice::slice_length(data) {
            Hash::hash(rust_primitives::slice::slice_index(data, i), state);
            i += 1;
        }
    }
}

/// See [`std::hash::BuildHasher`]
#[hax_lib::attributes]
pub trait BuildHasher {
    /// See [`std::hash::BuildHasher::Hasher`]
    type Hasher: Hasher;
    /// See [`std::hash::BuildHasher::build_hasher`]
    #[hax_lib::requires(true)]
    fn build_hasher(&self) -> Self::Hasher;
    /// See [`std::hash::BuildHasher::hash_one`]
    // F* has no default methods: there, `BuildHasherDefaults` provides it.
    #[cfg(not(hax_backend_fstar))]
    // The `Self::Hasher` bound repeats the associated type's, as core does:
    // callers pass one dictionary per clause.
    fn hash_one<T: Hash>(&self, x: T) -> u64
    where
        Self: Sized,
        Self::Hasher: Hasher,
    {
        let mut hasher = self.build_hasher();
        Hash::hash(&x, &mut hasher);
        hasher.finish()
    }
}

/// See [`std::hash::BuildHasherDefault`]
//
// DEVIATION(std): the phantom is over `H`, not `fn() -> H` (aeneas does not support
// arrow types), so auto traits and drop check follow `H`, which is stricter than std.
// The verification backends see no difference.
pub struct BuildHasherDefault<H>(std::marker::PhantomData<H>);

// Placeholder for core's `impl Hasher for &mut H`, so `new` is `impl_1` as in core.
impl<H> BuildHasherDefault<H> {}

impl<H> BuildHasherDefault<H> {
    /// See [`std::hash::BuildHasherDefault::new`]
    pub fn new() -> BuildHasherDefault<H> {
        BuildHasherDefault(std::marker::PhantomData)
    }
}

/// See [`std::fmt::Debug`] for [`BuildHasherDefault`]
#[cfg(not(hax_backend_fstar))]
impl<H> crate::fmt::Debug for BuildHasherDefault<H> {
    fn fmt(&self, f: &mut crate::fmt::Formatter) -> crate::fmt::Result {
        crate::fmt::Result::Ok(())
    }
}
// F* placeholder for the `Debug` impl above, which the F* model's blanket `Debug`
// covers: it keeps the impls below at real core's `impl_3`..`impl_7`.
#[cfg(hax_backend_fstar)]
impl<H> BuildHasherDefault<H> {}

impl<H: super::default::Default + Hasher> BuildHasher for BuildHasherDefault<H> {
    type Hasher = H;
    fn build_hasher(&self) -> H {
        H::default()
    }
}

/// See [`std::clone::Clone`] for [`BuildHasherDefault`]
#[cfg(not(hax_backend_fstar))]
impl<H> crate::clone::Clone for BuildHasherDefault<H> {
    fn clone(&self) -> Self {
        BuildHasherDefault(std::marker::PhantomData)
    }
    // Overridden, not left to the default: charon only emits the per-impl
    // `clone_from` symbol when the impl overrides it, and clients resolve to it.
    fn clone_from(self, source: Self) -> Self {
        source
    }
}
// F* placeholder for the `Clone` impl above, which the F* model's blanket `Clone`
// covers.
#[cfg(hax_backend_fstar)]
impl<H> BuildHasherDefault<H> {}

/// See [`std::default::Default`] for [`BuildHasherDefault`]
impl<H> super::default::Default for BuildHasherDefault<H> {
    fn default() -> Self {
        BuildHasherDefault::new()
    }
}

/// See [`std::cmp::PartialEq`] for [`BuildHasherDefault`]
impl<H> crate::cmp::PartialEq<BuildHasherDefault<H>> for BuildHasherDefault<H> {
    fn eq(&self, other: &BuildHasherDefault<H>) -> bool {
        true
    }
    #[cfg(not(hax_backend_fstar))]
    fn ne(&self, other: &BuildHasherDefault<H>) -> bool {
        false
    }
}

/// See [`std::cmp::Eq`] for [`BuildHasherDefault`]
impl<H> crate::cmp::Eq for BuildHasherDefault<H> {}

// `Hasher`'s provided methods, for F*, which has no default methods.
#[cfg(any(hax_backend_fstar, test))]
#[hax_lib::attributes]
pub(crate) trait HasherDefaults: Hasher {
    #[hax_lib::requires(true)]
    fn write_u8(&mut self, i: u8);
    #[hax_lib::requires(true)]
    fn write_u16(&mut self, i: u16);
    #[hax_lib::requires(true)]
    fn write_u32(&mut self, i: u32);
    #[hax_lib::requires(true)]
    fn write_u64(&mut self, i: u64);
    #[hax_lib::requires(true)]
    fn write_u128(&mut self, i: u128);
    #[hax_lib::requires(true)]
    fn write_usize(&mut self, i: usize);
    #[hax_lib::requires(true)]
    fn write_i8(&mut self, i: i8);
    #[hax_lib::requires(true)]
    fn write_i16(&mut self, i: i16);
    #[hax_lib::requires(true)]
    fn write_i32(&mut self, i: i32);
    #[hax_lib::requires(true)]
    fn write_i64(&mut self, i: i64);
    #[hax_lib::requires(true)]
    fn write_i128(&mut self, i: i128);
    #[hax_lib::requires(true)]
    fn write_isize(&mut self, i: isize);
    #[hax_lib::requires(true)]
    fn write_length_prefix(&mut self, len: usize);
    #[hax_lib::requires(true)]
    fn write_str(&mut self, s: &str);
}

// The little-endian writes behind `HasherDefaults`. Its blanket impl cannot call
// its own methods: in F*, that needs the instance being defined.
#[cfg(any(hax_backend_fstar, test))]
fn write_u8_le<H: Hasher>(h: &mut H, i: u8) {
    h.write(&[i])
}
#[cfg(any(hax_backend_fstar, test))]
fn write_u16_le<H: Hasher>(h: &mut H, i: u16) {
    h.write(&[i as u8, (i >> 8) as u8])
}
#[cfg(any(hax_backend_fstar, test))]
fn write_u32_le<H: Hasher>(h: &mut H, i: u32) {
    h.write(&[i as u8, (i >> 8) as u8, (i >> 16) as u8, (i >> 24) as u8])
}
#[cfg(any(hax_backend_fstar, test))]
fn write_u64_le<H: Hasher>(h: &mut H, i: u64) {
    h.write(&[
        i as u8,
        (i >> 8) as u8,
        (i >> 16) as u8,
        (i >> 24) as u8,
        (i >> 32) as u8,
        (i >> 40) as u8,
        (i >> 48) as u8,
        (i >> 56) as u8,
    ])
}
#[cfg(any(hax_backend_fstar, test))]
fn write_u128_le<H: Hasher>(h: &mut H, i: u128) {
    h.write(&[
        i as u8,
        (i >> 8) as u8,
        (i >> 16) as u8,
        (i >> 24) as u8,
        (i >> 32) as u8,
        (i >> 40) as u8,
        (i >> 48) as u8,
        (i >> 56) as u8,
        (i >> 64) as u8,
        (i >> 72) as u8,
        (i >> 80) as u8,
        (i >> 88) as u8,
        (i >> 96) as u8,
        (i >> 104) as u8,
        (i >> 112) as u8,
        (i >> 120) as u8,
    ])
}
// Through `u64`, as F* leaves the width of `usize` open and so rejects its
// shifts by 32 and more.
#[cfg(any(hax_backend_fstar, test))]
fn write_usize_le<H: Hasher>(h: &mut H, i: usize) {
    write_u64_le(h, i as u64)
}

#[cfg(any(hax_backend_fstar, test))]
impl<H: Hasher> HasherDefaults for H {
    fn write_u8(&mut self, i: u8) {
        write_u8_le(self, i)
    }
    fn write_u16(&mut self, i: u16) {
        write_u16_le(self, i)
    }
    fn write_u32(&mut self, i: u32) {
        write_u32_le(self, i)
    }
    fn write_u64(&mut self, i: u64) {
        write_u64_le(self, i)
    }
    fn write_u128(&mut self, i: u128) {
        write_u128_le(self, i)
    }
    fn write_usize(&mut self, i: usize) {
        write_usize_le(self, i)
    }
    fn write_i8(&mut self, i: i8) {
        write_u8_le(self, i as u8)
    }
    fn write_i16(&mut self, i: i16) {
        write_u16_le(self, i as u16)
    }
    fn write_i32(&mut self, i: i32) {
        write_u32_le(self, i as u32)
    }
    fn write_i64(&mut self, i: i64) {
        write_u64_le(self, i as u64)
    }
    fn write_i128(&mut self, i: i128) {
        write_u128_le(self, i as u128)
    }
    fn write_isize(&mut self, i: isize) {
        write_usize_le(self, i as usize)
    }
    fn write_length_prefix(&mut self, len: usize) {
        write_usize_le(self, len)
    }
    fn write_str(&mut self, s: &str) {
        self.write(rust_primitives::string::str_as_bytes(s));
        write_u8_le(self, 0xff)
    }
}

// `Hash`'s provided method, for F*, which has no default methods.
//
// DEVIATION(std): the integer types do not override it here, so in F* an integer
// slice reaches the hasher one element per `write`, where std uses a single `write`.
#[cfg(any(hax_backend_fstar, test))]
#[hax_lib::attributes]
pub(crate) trait HashDefaults: Hash {
    #[hax_lib::requires(true)]
    fn hash_slice<H: Hasher>(data: &[Self], state: &mut H)
    where
        Self: Sized;
}

#[cfg(any(hax_backend_fstar, test))]
impl<T: Hash> HashDefaults for T {
    fn hash_slice<H: Hasher>(data: &[T], state: &mut H) {
        for i in 0..rust_primitives::slice::slice_length(data) {
            Hash::hash(rust_primitives::slice::slice_index(data, i), state);
        }
    }
}

// `BuildHasher`'s provided method, for F*, which has no default methods.
#[cfg(any(hax_backend_fstar, test))]
#[hax_lib::attributes]
pub(crate) trait BuildHasherDefaults: BuildHasher {
    // The `Self::Hasher` bound repeats the associated type's, as core does: F* does
    // not resolve the associated type's own instance.
    #[hax_lib::requires(true)]
    fn hash_one<T: Hash>(&self, x: T) -> u64
    where
        Self::Hasher: Hasher;
}

#[cfg(any(hax_backend_fstar, test))]
impl<B: BuildHasher> BuildHasherDefaults for B {
    fn hash_one<T: Hash>(&self, x: T) -> u64
    where
        Self::Hasher: Hasher,
    {
        let mut hasher = self.build_hasher();
        Hash::hash(&x, &mut hasher);
        hasher.finish()
    }
}

/// Collects the bytes it is fed, so the integer `hash_slice`s below can pass them
/// on in a single `write`.
#[cfg(not(hax_backend_fstar))]
struct ByteBuffer(rust_primitives::sequence::Seq<u8>);

#[cfg(not(hax_backend_fstar))]
#[hax_lib::attributes]
impl Hasher for ByteBuffer {
    // Excluded from coverage: never called, as only the collected bytes are read.
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn finish(&self) -> u64 {
        0
    }
    fn write(&mut self, bytes: &[u8]) {
        rust_primitives::sequence::seq_extend(&mut self.0, bytes)
    }
}

// The integer `Hash` impls std keeps in `core::hash::impls`.
macro_rules! impl_hash_for_int {
    ($($t:ty => $meth:ident),*) => {
        $(
            #[hax_lib::attributes]
            impl Hash for $t {
                fn hash<H: Hasher>(&self, state: &mut H) {
                    #[cfg(not(hax_backend_fstar))]
                    Hasher::$meth(state, *self);
                    #[cfg(hax_backend_fstar)]
                    HasherDefaults::$meth(state, *self);
                }
                // As in std, the whole slice goes to `state` in one `write`.
                #[cfg(not(hax_backend_fstar))]
                fn hash_slice<H: Hasher>(data: &[$t], state: &mut H) {
                    let mut buffer = ByteBuffer(rust_primitives::sequence::seq_empty());
                    let mut i = 0;
                    while i < rust_primitives::slice::slice_length(data) {
                        Hasher::$meth(&mut buffer, *rust_primitives::slice::slice_index(data, i));
                        i += 1;
                    }
                    state.write(rust_primitives::sequence::seq_to_slice(&buffer.0))
                }
            }
        )*
    };
}

impl_hash_for_int!(
    core::primitive::u8 => write_u8,
    core::primitive::u16 => write_u16,
    core::primitive::u32 => write_u32,
    core::primitive::u64 => write_u64,
    core::primitive::u128 => write_u128,
    core::primitive::usize => write_usize,
    core::primitive::i8 => write_i8,
    core::primitive::i16 => write_i16,
    core::primitive::i32 => write_i32,
    core::primitive::i64 => write_i64,
    core::primitive::i128 => write_i128,
    core::primitive::isize => write_isize
);

// The other `Hash` impls std keeps in `core::hash::impls`. F* takes the `Hasher`
// and `Hash` provided methods from `HasherDefaults` and `HashDefaults`.

/// See [`std::hash::Hash`] for `bool`
#[hax_lib::attributes]
impl Hash for core::primitive::bool {
    fn hash<H: Hasher>(&self, state: &mut H) {
        #[cfg(not(hax_backend_fstar))]
        Hasher::write_u8(state, *self as u8);
        #[cfg(hax_backend_fstar)]
        HasherDefaults::write_u8(state, *self as u8);
    }
}

/// See [`std::hash::Hash`] for `str`
#[hax_lib::attributes]
impl Hash for core::primitive::str {
    fn hash<H: Hasher>(&self, state: &mut H) {
        #[cfg(not(hax_backend_fstar))]
        Hasher::write_str(state, self);
        #[cfg(hax_backend_fstar)]
        HasherDefaults::write_str(state, self);
    }
}

/// See [`std::hash::Hash`] for `()`
#[hax_lib::attributes]
impl Hash for () {
    fn hash<H: Hasher>(&self, state: &mut H) {}
}

// Tuples hash their fields in order, as core's `impl_hash_tuple!` does.
macro_rules! impl_hash_for_tuple {
    ($($(#[$attr:meta])* ($($name:ident $idx:tt),+))*) => {$(
        /// See [`std::hash::Hash`] for tuples
        $(#[$attr])*
        #[hax_lib::attributes]
        impl<$($name: Hash),+> Hash for ($($name,)+) {
            fn hash<S: Hasher>(&self, state: &mut S) {
                $(Hash::hash(&self.$idx, state);)+
            }
        }
    )*};
}

impl_hash_for_tuple! {
    // Not in F*, where `(T,)` is `T`: the impl would be an instance deriving
    // `Hash T` from itself.
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    (T 0)
    (T 0, B 1)
    (T 0, B 1, C 2)
    (T 0, B 1, C 2, D 3)
    (T 0, B 1, C 2, D 3, E 4)
    (T 0, B 1, C 2, D 3, E 4, F 5)
    (T 0, B 1, C 2, D 3, E 4, F 5, G 6)
    (T 0, B 1, C 2, D 3, E 4, F 5, G 6, H 7)
    (T 0, B 1, C 2, D 3, E 4, F 5, G 6, H 7, I 8)
    (T 0, B 1, C 2, D 3, E 4, F 5, G 6, H 7, I 8, J 9)
    (T 0, B 1, C 2, D 3, E 4, F 5, G 6, H 7, I 8, J 9, K 10)
    (T 0, B 1, C 2, D 3, E 4, F 5, G 6, H 7, I 8, J 9, K 10, L 11)
}

/// See [`std::hash::Hash`] for `[T]`
#[hax_lib::attributes]
impl<T: Hash> Hash for [T] {
    fn hash<H: Hasher>(&self, state: &mut H) {
        #[cfg(not(hax_backend_fstar))]
        Hasher::write_length_prefix(state, rust_primitives::slice::slice_length(self));
        #[cfg(not(hax_backend_fstar))]
        Hash::hash_slice(self, state);
        #[cfg(hax_backend_fstar)]
        HasherDefaults::write_length_prefix(state, rust_primitives::slice::slice_length(self));
        #[cfg(hax_backend_fstar)]
        HashDefaults::hash_slice(self, state);
    }
}

/// See [`std::hash::Hash`] for `&T`
// Not in F*, where `&T` is `T`: the impl would be an instance deriving `Hash T`
// from itself.
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
#[hax_lib::attributes]
impl<T: ?Sized + Hash> Hash for &T {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(*self, state)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pastey::paste;
    use proptest::prelude::*;

    /// Byte-log hasher implementing both the model's and std's `Hasher`.
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Log(Vec<u8>);

    impl Log {
        fn new() -> Log {
            Log(Vec::new())
        }
        fn fnv(&self) -> u64 {
            let mut h: u64 = 0xcbf2_9ce4_8422_2325;
            for b in &self.0 {
                h ^= *b as u64;
                h = h.wrapping_mul(0x0000_0100_0000_01b3);
            }
            h
        }
    }

    impl std::default::Default for Log {
        fn default() -> Log {
            Log::new()
        }
    }

    impl crate::default::Default for Log {
        fn default() -> Log {
            Log::new()
        }
    }

    impl std::hash::Hasher for Log {
        fn finish(&self) -> u64 {
            self.fnv()
        }
        fn write(&mut self, bytes: &[u8]) {
            self.0.extend_from_slice(bytes)
        }
    }

    /// Records each `write` separately, so tests can compare how the bytes are split.
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Writes(Vec<Vec<u8>>);

    impl std::hash::Hasher for Writes {
        fn finish(&self) -> u64 {
            0
        }
        fn write(&mut self, bytes: &[u8]) {
            self.0.push(bytes.to_vec())
        }
    }

    impl Hasher for Writes {
        fn finish(&self) -> u64 {
            0
        }
        fn write(&mut self, bytes: &[u8]) {
            self.0.push(bytes.to_vec())
        }
    }

    // Only the required methods, so the tests below run the provided ones.
    impl Hasher for Log {
        fn finish(&self) -> u64 {
            self.fnv()
        }
        fn write(&mut self, bytes: &[u8]) {
            self.0.extend_from_slice(bytes)
        }
    }

    // std's integer impls write native-endian bytes, which are little-endian here.
    macro_rules! hash_tests {
        ($($t:ident),*) => {
            paste! { $(
                proptest! {
                    #[test]
                    fn [<test_hash_ $t>](x in any::<$t>()) {
                        let mut m = Log::new();
                        Hash::hash(&x, &mut m);
                        let mut s = Log::new();
                        std::hash::Hash::hash(&x, &mut s);
                        prop_assert_eq!(&m, &s);
                    }

                    // `HashDefaults` feeds the same bytes, one element per `write`.
                    #[test]
                    fn [<test_hash_slice_defaults_ $t>](v in prop::collection::vec(any::<$t>(), 0..8)) {
                        let mut m = Log::new();
                        <$t as HashDefaults>::hash_slice(&v, &mut m);
                        let mut s = Log::new();
                        std::hash::Hash::hash_slice(&v, &mut s);
                        prop_assert_eq!(&m, &s);
                    }

                    #[cfg(not(hax_backend_fstar))]
                    #[test]
                    fn [<test_hash_slice_ $t>](v in prop::collection::vec(any::<$t>(), 0..8)) {
                        let mut m = Writes(Vec::new());
                        <$t as Hash>::hash_slice(&v, &mut m);
                        let mut s = Writes(Vec::new());
                        std::hash::Hash::hash_slice(&v, &mut s);
                        prop_assert_eq!(&m, &s);
                    }
                }
            )* }
        };
    }

    hash_tests!(
        u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
    );

    // std's defaults write native-endian bytes, which are little-endian here.
    #[cfg(not(hax_backend_fstar))]
    macro_rules! write_prop {
        ($($name:ident, $meth:ident, $t:ty;)*) => {
            proptest! {
                $(
                    #[test]
                    fn $name(x in any::<$t>()) {
                        let mut m = Log::new();
                        <Log as Hasher>::$meth(&mut m, x);
                        let mut s = Log::new();
                        <Log as std::hash::Hasher>::$meth(&mut s, x);
                        prop_assert_eq!(&m, &s);
                    }
                )*
            }
        };
    }

    // The same, for the F* copies in `HasherDefaults`.
    macro_rules! write_defaults_prop {
        ($($name:ident, $meth:ident, $t:ty;)*) => {
            proptest! {
                $(
                    #[test]
                    fn $name(x in any::<$t>()) {
                        let mut m = Log::new();
                        <Log as HasherDefaults>::$meth(&mut m, x);
                        let mut s = Log::new();
                        <Log as std::hash::Hasher>::$meth(&mut s, x);
                        prop_assert_eq!(&m, &s);
                    }
                )*
            }
        };
    }

    write_defaults_prop! {
        test_write_defaults_u8, write_u8, u8;
        test_write_defaults_u16, write_u16, u16;
        test_write_defaults_u32, write_u32, u32;
        test_write_defaults_u64, write_u64, u64;
        test_write_defaults_u128, write_u128, u128;
        test_write_defaults_usize, write_usize, usize;
        test_write_defaults_i8, write_i8, i8;
        test_write_defaults_i16, write_i16, i16;
        test_write_defaults_i32, write_i32, i32;
        test_write_defaults_i64, write_i64, i64;
        test_write_defaults_i128, write_i128, i128;
        test_write_defaults_isize, write_isize, isize;
        test_write_defaults_length_prefix, write_length_prefix, usize;
    }

    #[cfg(not(hax_backend_fstar))]
    write_prop! {
        test_write_u8, write_u8, u8;
        test_write_u16, write_u16, u16;
        test_write_u32, write_u32, u32;
        test_write_u64, write_u64, u64;
        test_write_u128, write_u128, u128;
        test_write_usize, write_usize, usize;
        test_write_i8, write_i8, i8;
        test_write_i16, write_i16, i16;
        test_write_i32, write_i32, i32;
        test_write_i64, write_i64, i64;
        test_write_i128, write_i128, i128;
        test_write_isize, write_isize, isize;
        test_write_length_prefix, write_length_prefix, usize;
    }

    proptest! {
        #[test]
        fn test_write(bytes in prop::collection::vec(any::<u8>(), 0..32)) {
            let mut m = Log::new();
            <Log as Hasher>::write(&mut m, &bytes);
            let mut s = Log::new();
            <Log as std::hash::Hasher>::write(&mut s, &bytes);
            prop_assert_eq!(&m, &s);
            prop_assert_eq!(
                <Log as Hasher>::finish(&m),
                <Log as std::hash::Hasher>::finish(&s)
            );
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_write_str(s in "\\PC{0,16}") {
            let mut m = Log::new();
            <Log as Hasher>::write_str(&mut m, &s);
            let mut r = Log::new();
            <Log as std::hash::Hasher>::write_str(&mut r, &s);
            prop_assert_eq!(&m, &r);
        }

        #[test]
        fn test_write_str_defaults(s in "\\PC{0,16}") {
            let mut m = Log::new();
            <Log as HasherDefaults>::write_str(&mut m, &s);
            let mut r = Log::new();
            <Log as std::hash::Hasher>::write_str(&mut r, &s);
            prop_assert_eq!(&m, &r);
        }

        #[test]
        fn test_hash_matches_std_u8(x in any::<u8>()) {
            let mut m = Log::new();
            Hash::hash(&x, &mut m);
            let mut s = Log::new();
            std::hash::Hash::hash(&x, &mut s);
            prop_assert_eq!(&m, &s);
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_build_hasher_default_hash_one(x in any::<u8>()) {
            let m = BuildHasherDefault::<Log>::new();
            let s = std::hash::BuildHasherDefault::<Log>::new();
            prop_assert_eq!(
                BuildHasher::hash_one(&m, x),
                std::hash::BuildHasher::hash_one(&s, x)
            );
        }

        #[test]
        fn test_build_hasher_default_default_hash_one(x in any::<u32>()) {
            let m: BuildHasherDefault<Log> = crate::default::Default::default();
            let s: std::hash::BuildHasherDefault<Log> = std::default::Default::default();
            prop_assert_eq!(
                BuildHasherDefaults::hash_one(&m, x),
                std::hash::BuildHasher::hash_one(&s, x)
            );
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_build_hasher_default_clone_hash_one(x in any::<u32>()) {
            let m = crate::clone::Clone::clone(&BuildHasherDefault::<Log>::new());
            let m = crate::clone::Clone::clone_from(m, BuildHasherDefault::<Log>::new());
            let s = std::clone::Clone::clone(&std::hash::BuildHasherDefault::<Log>::new());
            prop_assert_eq!(
                BuildHasher::hash_one(&m, x),
                std::hash::BuildHasher::hash_one(&s, x)
            );
        }

        #[test]
        fn test_build_hasher_defaults_hash_one(x in any::<u32>()) {
            let m = BuildHasherDefault::<Log>::new();
            let s = std::hash::BuildHasherDefault::<Log>::new();
            prop_assert_eq!(
                BuildHasherDefaults::hash_one(&m, x),
                std::hash::BuildHasher::hash_one(&s, x)
            );
        }

        #[test]
        fn test_build_hasher_build_hasher(bytes in prop::collection::vec(any::<u8>(), 0..8)) {
            let m = BuildHasherDefault::<Log>::new();
            let s = std::hash::BuildHasherDefault::<Log>::new();
            let mut mh = BuildHasher::build_hasher(&m);
            let mut sh = std::hash::BuildHasher::build_hasher(&s);
            <Log as Hasher>::write(&mut mh, &bytes);
            <Log as std::hash::Hasher>::write(&mut sh, &bytes);
            prop_assert_eq!(&mh, &sh);
        }
    }

    /// The bytes that hashing `model` with the model's `Hash` and `std` with std's feed in.
    fn model_and_std_bytes<M: Hash + ?Sized, S: std::hash::Hash + ?Sized>(
        model: &M,
        std: &S,
    ) -> (Log, Log) {
        let mut m = Log::new();
        Hash::hash(model, &mut m);
        let mut s = Log::new();
        std::hash::Hash::hash(std, &mut s);
        (m, s)
    }

    proptest! {
        #[test]
        fn test_hash_bool(x in any::<bool>()) {
            let (m, s) = model_and_std_bytes(&x, &x);
            prop_assert_eq!(m, s);
        }

        #[test]
        fn test_hash_str(x in "\\PC{0,16}") {
            let (m, s) = model_and_std_bytes(x.as_str(), x.as_str());
            prop_assert_eq!(m, s);
        }

        #[test]
        fn test_hash_slice_type(v in prop::collection::vec(any::<u16>(), 0..8)) {
            let (m, s) = model_and_std_bytes(v.as_slice(), v.as_slice());
            prop_assert_eq!(m, s);
        }

        #[test]
        fn test_hash_slice_of_bool(v in prop::collection::vec(any::<bool>(), 0..8)) {
            let (m, s) = model_and_std_bytes(v.as_slice(), v.as_slice());
            prop_assert_eq!(m, s);
        }

        #[test]
        fn test_hash_ref(x in any::<u32>(), y in "\\PC{0,8}") {
            let (m, s) = model_and_std_bytes(&&x, &&x);
            prop_assert_eq!(m, s);
            let (m, s) = model_and_std_bytes(&y.as_str(), &y.as_str());
            prop_assert_eq!(m, s);
        }

        // Every arity, each field distinct, so a wrong field order shows.
        #[test]
        fn test_hash_tuples(v in prop::array::uniform12(any::<u8>()), c in any::<u16>()) {
            macro_rules! check {
                ($($t:expr),*) => {$({
                    let (m, s) = model_and_std_bytes(&$t, &$t);
                    prop_assert_eq!(m, s);
                })*};
            }
            let [a, b, d, e, f, g, h, i, j, k, l, n] = v;
            check!(
                (a,),
                (a, c),
                (a, c, true),
                (a, b, d, e),
                (a, b, d, e, f),
                (a, b, d, e, f, g),
                (a, b, d, e, f, g, h),
                (a, b, d, e, f, g, h, i),
                (a, b, d, e, f, g, h, i, j),
                (a, b, d, e, f, g, h, i, j, k),
                (a, b, d, e, f, g, h, i, j, k, l),
                (a, b, d, e, f, g, h, i, j, k, l, n)
            );
        }
    }

    #[test]
    fn test_hash_unit() {
        let (m, s) = model_and_std_bytes(&(), &());
        assert_eq!(m, s);
    }

    #[test]
    fn test_build_hasher_default_eq() {
        let (a, b) = (
            BuildHasherDefault::<Log>::new(),
            BuildHasherDefault::<Log>::new(),
        );
        let (sa, sb) = (
            std::hash::BuildHasherDefault::<Log>::new(),
            std::hash::BuildHasherDefault::<Log>::new(),
        );
        assert_eq!(crate::cmp::PartialEq::eq(&a, &b), sa == sb);
    }

    #[cfg(not(hax_backend_fstar))]
    #[test]
    fn test_build_hasher_default_ne() {
        let (a, b) = (
            BuildHasherDefault::<Log>::new(),
            BuildHasherDefault::<Log>::new(),
        );
        let (sa, sb) = (
            std::hash::BuildHasherDefault::<Log>::new(),
            std::hash::BuildHasherDefault::<Log>::new(),
        );
        assert_eq!(crate::cmp::PartialEq::ne(&a, &b), sa != sb);
    }

    // The model's `Formatter` renders nothing, so only success is observable.
    #[cfg(not(hax_backend_fstar))]
    #[test]
    fn test_build_hasher_default_debug() {
        let mut f = crate::fmt::Formatter;
        assert!(matches!(
            crate::fmt::Debug::fmt(&BuildHasherDefault::<Log>::new(), &mut f),
            crate::fmt::Result::Ok(())
        ));
    }
}
