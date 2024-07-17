use core::ops::*;
pub trait Classify {
    type Output;
    fn classify(self) -> Self::Output;
}

pub trait Declassify {
    type Output;
    fn declassify(self) -> Self::Output;
}

pub trait ClassifyEach {
    type Output;
    fn classify_each(self) -> Self::Output;
}

pub trait DeclassifyEach {
    type Output;
    fn declassify_each(self) -> Self::Output;
}

pub trait MachineInt : 
    Sized + Clone + Copy +
    Add + Sub + Mul +
    BitAnd + BitOr + BitXor +
    Not + Shl + Shr
    {}
impl MachineInt for u8 {}
impl MachineInt for i8 {}
impl MachineInt for u16 {}
impl MachineInt for i16 {}
impl MachineInt for u32 {}
impl MachineInt for i32 {}
impl MachineInt for u64 {}
impl MachineInt for i64 {}
impl MachineInt for u128 {}
impl MachineInt for i128 {}
impl MachineInt for usize {}
impl MachineInt for isize {}

pub trait IntOps where Self:Sized {
    fn wrapping_add<T:Into<Self>>(self,rhs:T) -> Self;
    fn wrapping_sub<T:Into<Self>>(self,rhs:T) -> Self;
    fn wrapping_mul<T:Into<Self>>(self,rhs:T) -> Self;
    fn rotate_left(self,rhs:u32) -> Self;
    fn rotate_right(self,rhs:u32) -> Self;
}


pub trait EncodeOps<T, const N:usize> {
    fn to_le_bytes(&self) -> [T; N];
    fn to_be_bytes(&self) -> [T; N];
    fn from_le_bytes(x:&[T; N]) -> Self;
    fn from_be_bytes(x:&[T; N]) -> Self;
}

#[inline(always)]
pub(crate) fn try_to_le_bytes<U:Clone, const C: usize, T: EncodeOps<U, C>, const N: usize, const B:usize>(x:&[T;N]) -> Result<[U;B],()> {
    let mut v = Vec::new();
    for i in 0..N {
        v.extend_from_slice(&x[i].to_le_bytes())
    }
    v.try_into().map_err(|_|())
}

#[inline(always)]
pub(crate) fn try_to_be_bytes<U:Clone, const C: usize, T: EncodeOps<U, C>, const N: usize, const B:usize>(x:&[T;N]) -> Result<[U;B],()> {
    let mut v = Vec::new();
    for i in 0..N {
        v.extend_from_slice(&x[i].to_be_bytes())
    }
    v.try_into().map_err(|_|())
}

#[inline(always)]
pub(crate) fn try_from_le_bytes<U, const C: usize, T: EncodeOps<U, C>, const N: usize>(x:&[U]) -> Result<[T; N],()> {
    let mut v = Vec::new();
    for c in x.chunks_exact(C) {
        v.push(T::from_le_bytes(c.try_into().unwrap()))
    }
    v.try_into().map_err(|_|())
}

#[inline(always)]
pub(crate) fn try_from_be_bytes<U, const C: usize, T: EncodeOps<U, C>, const N: usize>(x:&[U]) -> Result<[T; N],()> {
    let mut v = Vec::new();
    for c in x.chunks_exact(C) {
        v.push(T::from_be_bytes(c.try_into().unwrap()))
    }
    v.try_into().map_err(|_|())
}

pub trait TryEncodeOps<T, const N:usize> : Sized {
    fn try_to_le_bytes(&self) -> Result<[T; N],()>;
    fn try_to_be_bytes(&self) -> Result<[T; N],()>;
}

pub trait TryDecodeOps<T> : Sized {
    fn try_from_le_bytes(x:&[T]) -> Result<Self,()>;
    fn try_from_be_bytes(x:&[T]) -> Result<Self,()>;
}
