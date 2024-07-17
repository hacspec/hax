use crate::traits::*;

pub type I8 = i8;
pub type U8 = u8;
pub type I16 = i16;
pub type U16 = u16;
pub type I32 = i32;
pub type U32 = u32;
pub type I64 = i64;
pub type U64 = u64;
pub type I128 = i128;
pub type U128 = u128;

impl<T> Classify for T {
    type ClassifiedOutput = T;
    fn classify(self) -> Self {self}
}

impl<T> Declassify for T{
    type DeclassifiedOutput = T;
    fn declassify(self) -> T {
        self
    }
}

impl<T> ClassifyEach for T {
    type ClassifiedEachOutput = T;
    fn classify_each(self) -> T {
        self
    }
}

impl<T> DeclassifyEach for T {
    type DeclassifiedEachOutput = T;
    fn declassify_each(self) -> T {
        self
    }
}

impl EncodeOps<U8,4> for U32 {
    fn to_le_bytes(&self) -> [U8;4] {
        (*self as u32).to_le_bytes()
    }
    fn to_be_bytes(&self) -> [U8;4] {
        (*self as u32).to_be_bytes()
    }
    fn from_le_bytes(x:&[U8;4]) -> Self {
        u32::from_le_bytes(*x)
    }
    fn from_be_bytes(x:&[U8;4]) -> Self {
        u32::from_be_bytes(*x)
    }
}

#[hax_lib::attributes]
impl<const N: usize, const B:usize> TryEncodeOps<U8, B> for [U32; N] {
    #[requires(N < 65536 / 4)]
    #[ensures(|result| N < 65536 / 4 && (if B == N * 4 {result.is_ok()} else {result.is_err()}))] 
    fn try_to_le_bytes(&self) -> Result<[U8;B],()> {
        try_to_le_bytes(self)
    }
    #[requires(N < 65536 / 4)]
    #[ensures(|result| N < 65536 / 4 && (if B == N * 4 {result.is_ok()} else {result.is_err()}))] 
    fn try_to_be_bytes(&self) -> Result<[U8;B],()> {
        try_to_be_bytes(self)
    }
}

#[hax_lib::attributes]
impl<const N: usize> TryDecodeOps<U8> for [U32; N] {
    #[requires(N < 65536 / 4)]
    #[ensures(|result| N < 65536 / 4 && (if x.len() == N * 4 {result.is_ok()} else {result.is_err()}))] 
    fn try_from_le_bytes(x:&[U8]) -> Result<[U32; N],()> {
        try_from_le_bytes(x)
    }
    #[requires(N < 65536 / 4)]
    #[ensures(|result| N < 65536 / 4 && (if x.len() == N * 4 {result.is_ok()} else {result.is_err()}))] 
    fn try_from_be_bytes(x:&[U8]) -> Result<[U32; N],()> {
        try_from_be_bytes(x)
    }
}