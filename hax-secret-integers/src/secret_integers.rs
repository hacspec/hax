use core::ops::*;
use crate::traits::*;

#[repr(transparent)]
pub struct Secret<T>(T);

pub const fn secret<T>(x:T) -> Secret<T> {Secret(x)}
fn unwrap<T>(x:Secret<T>) -> T {x.0}

impl<T> Classify for T {
    type ClassifiedOutput = Secret<T>;
    fn classify(self) -> Secret<Self> {secret(self)}
}

impl<T> Declassify for Secret<T> {
    type DeclassifiedOutput = T;
    fn declassify(self) -> T {
        unwrap(self)
    }
}

impl<T> From<T> for Secret<T> {
    fn from(x:T) -> Secret<T> {x.classify()}
}

impl<T: Clone> Clone for Secret<T> {
    fn clone(&self) -> Self {
        Secret(self.0.clone())
    }
}

impl<T: Clone+Copy> Copy for Secret<T> {}

impl<T, const N: usize> ClassifyEach for [T; N] {
    type ClassifiedEachOutput = [Secret<T>; N];
    fn classify_each(self) -> [Secret<T>; N] {
        self.map(|x| x.into())
    }
}

impl<T> ClassifyEach for Vec<T> {
    type ClassifiedEachOutput = Vec<Secret<T>>;
    fn classify_each(self) -> Vec<Secret<T>> {
        self.into_iter().map(|x| x.classify()).collect()
    }
}


impl<T, const N: usize> DeclassifyEach for [Secret<T>; N] {
    type DeclassifiedEachOutput = [T; N];
    fn declassify_each(self) -> [T; N] {
        self.map(|x| x.declassify())
    }
}

impl<T> DeclassifyEach for Vec<Secret<T>> {
    type DeclassifiedEachOutput = Vec<T>;
    fn declassify_each(self) -> Vec<T> {
        self.into_iter().map(|x| x.declassify()).collect()
    }
}


impl<T: Add,V:Into<Secret<T>>> Add<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn add(self, rhs: V) -> Self::Output {
        self.declassify().add(rhs.into().declassify()).classify()
    }
}

impl<T: Sub,V:Into<Secret<T>>> Sub<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn sub(self, rhs: V) -> Self::Output {
        self.declassify().sub(rhs.into().declassify()).into()
    }
}

impl<T:Mul,V:Into<Secret<T>>> Mul<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn mul(self, rhs: V) -> Self::Output {
        self.declassify().mul(rhs.into().declassify()).into()
    }
}

impl<T: BitXor,V:Into<Secret<T>>> BitXor<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn bitxor(self, rhs: V) -> Self::Output {
        self.declassify().bitxor(rhs.into().declassify()).into()
    }
}

impl<T: BitXor+Copy,V:Into<Secret<T>>> BitXorAssign<V> for Secret<T> 
    where T::Output : Into<T> {
    fn bitxor_assign(&mut self, rhs: V) {
        let r = self.declassify().bitxor(rhs.into().declassify()).into();
        *self = r.classify();
    }
}

impl<T: BitOr,V:Into<Secret<T>>> BitOr<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn bitor(self, rhs: V) -> Self::Output {
        self.declassify().bitor(rhs.into().declassify()).into()
    }
}

impl<T: BitOr+Copy,V:Into<Secret<T>>> BitOrAssign<V> for Secret<T> 
    where T::Output : Into<T> {
    fn bitor_assign(&mut self, rhs: V) {
        let r = self.declassify().bitor(rhs.into().declassify()).into();
        *self = r.classify();
    }
}

impl<T: BitAnd,V:Into<Secret<T>>> BitAnd<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn bitand(self, rhs: V) -> Self::Output {
        self.declassify().bitand(rhs.into().declassify()).into()
    }
}

impl<T: BitAnd+Copy,V:Into<Secret<T>>> BitAndAssign<V> for Secret<T> 
    where T::Output : Into<T> {
    fn bitand_assign(&mut self, rhs: V) {
        let r = self.declassify().bitand(rhs.into().declassify()).into();
        *self = r.classify();
    }
}

impl<T: Not> Not for Secret<T> {
    type Output = Secret<T::Output>;
    fn not(self) -> Self::Output {
        self.declassify().not().into()
    }
}

impl<U, T: Shl<U>> Shl<U> for Secret<T> {
    type Output = Secret<T::Output>;
    fn shl(self, rhs: U) -> Self::Output {
        (self.declassify().shl(rhs)).into()
    }
}

impl<U, T: Shr<U>> Shr<U> for Secret<T> {
    type Output = Secret<T::Output>;
    fn shr(self, rhs: U) -> Self::Output {
        (self.declassify().shr(rhs)).into()
    }
}

pub type I8 = Secret<i8>;
pub type U8 = Secret<u8>;
pub type I16 = Secret<i16>;
pub type U16 = Secret<u16>;
pub type I32 = Secret<i32>;
pub type U32 = Secret<u32>;
pub type I64 = Secret<i64>;
pub type U64 = Secret<u64>;
pub type I128 = Secret<i128>;
pub type U128 = Secret<u128>;

impl IntOps for Secret<u32> {
    fn wrapping_add<T:Into<Secret<u32>>>(self,rhs:T) -> Self {
        self.declassify().wrapping_add(rhs.into().declassify()).classify()
    }
    fn wrapping_sub<T:Into<Secret<u32>>>(self,rhs:T) -> Self {
        self.declassify().wrapping_sub(rhs.into().declassify()).classify()
    }
    fn wrapping_mul<T:Into<Secret<u32>>>(self,rhs:T) -> Self {
        self.declassify().wrapping_mul(rhs.into().declassify()).classify()
    }
    fn rotate_left(self,rhs:u32) -> Self {
        self.declassify().rotate_left(rhs).classify()
    }
    fn rotate_right(self,rhs:u32) -> Self {
        self.declassify().rotate_right(rhs).classify()
    }
}

impl EncodeOps<U8,4> for U32 {
    fn to_le_bytes(&self) -> [U8;4] {
        self.declassify().to_le_bytes().classify_each()
    }
    fn to_be_bytes(&self) -> [U8;4] {
        self.declassify().to_be_bytes().classify_each()
    }
    fn from_le_bytes(x:&[U8;4]) -> Self {
        u32::from_le_bytes(x.map(|i| i.declassify())).classify()
    }
    fn from_be_bytes(x:&[U8;4]) -> Self {
        u32::from_be_bytes(x.map(|i| i.declassify())).classify()
    }
}

impl<const N: usize, const B:usize> TryEncodeOps<U8, B> for [U32; N] {
    fn try_to_le_bytes(&self) -> Result<[U8;B],()> {
        try_to_le_bytes(self)
    }
    fn try_to_be_bytes(&self) -> Result<[U8;B],()> {
        try_to_be_bytes(self)
    }
}

impl<const N: usize> TryDecodeOps<U8> for [U32; N] {
    fn try_from_le_bytes(x:&[U8]) -> Result<Self,()> {
        try_from_le_bytes(x)
    }
    fn try_from_be_bytes(x:&[U8]) -> Result<Self,()> {
        try_from_be_bytes(x)
    }
}

impl IntOps for Secret<u64> {
    fn wrapping_add<T:Into<Secret<u64>>>(self,rhs:T) -> Self {
        self.declassify().wrapping_add(rhs.into().declassify()).classify()
    }
    fn wrapping_sub<T:Into<Secret<u64>>>(self,rhs:T) -> Self {
        self.declassify().wrapping_sub(rhs.into().declassify()).classify()
    }
    fn wrapping_mul<T:Into<Secret<u64>>>(self,rhs:T) -> Self {
        self.declassify().wrapping_mul(rhs.into().declassify()).classify()
    }
    fn rotate_left(self,rhs:u32) -> Self {
        self.declassify().rotate_left(rhs).classify()
    }
    fn rotate_right(self,rhs:u32) -> Self {
        self.declassify().rotate_right(rhs).classify()
    }
}

impl EncodeOps<U8,8> for U64 {
    fn to_le_bytes(&self) -> [U8;8] {
        self.declassify().to_le_bytes().classify_each()
    }
    fn to_be_bytes(&self) -> [U8;8] {
        self.declassify().to_be_bytes().classify_each()
    }
    fn from_le_bytes(x:&[U8;8]) -> Self {
        u64::from_le_bytes(x.map(|i| i.declassify())).classify()
    }
    fn from_be_bytes(x:&[U8;8]) -> Self {
        u64::from_be_bytes(x.map(|i| i.declassify())).classify()
    }
}

impl<const N: usize, const B:usize> TryEncodeOps<U8, B> for [U64; N] {
    fn try_to_le_bytes(&self) -> Result<[U8;B],()> {
        try_to_le_bytes(self)
    }
    fn try_to_be_bytes(&self) -> Result<[U8;B],()> {
        try_to_be_bytes(self)
    }
}

impl<const N: usize> TryDecodeOps<U8> for [U64; N] {
    fn try_from_le_bytes(x:&[U8]) -> Result<Self,()> {
        try_from_le_bytes(x)
    }
    fn try_from_be_bytes(x:&[U8]) -> Result<Self,()> {
        try_from_be_bytes(x)
    }
}