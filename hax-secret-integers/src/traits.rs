pub trait Classify {
    type ClassifiedOutput;
    fn classify(self) -> Self::ClassifiedOutput;
}

pub trait Declassify {
    type DeclassifiedOutput;
    fn declassify(self) -> Self::DeclassifiedOutput;
}

pub trait ClassifyEach {
    type ClassifiedEachOutput;
    fn classify_each(self) -> Self::ClassifiedEachOutput;
}

pub trait DeclassifyEach {
    type DeclassifiedEachOutput;
    fn declassify_each(self) -> Self::DeclassifiedEachOutput;
}

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
#[hax_lib::requires(C > 0 && C <= 16 && N <= 65536 / C)]
#[hax_lib::ensures(|result| if B == N * C {result.is_ok()} else {result.is_err()} )] 
pub(crate) fn try_to_le_bytes<U:Clone, const C: usize, T: EncodeOps<U, C>, const N: usize, const B:usize>(x:&[T;N]) -> Result<[U;B],()> {
    let mut v = Vec::new();
    for i in 0..N {
        v.extend_from_slice(&x[i].to_le_bytes())
    }
    v.try_into().map_err(|_|())
}

#[inline(always)]
#[hax_lib::requires(C > 0 && C <= 16 && N <= 65536 / C)]
#[hax_lib::ensures(|result| if B == N * C {result.is_ok()} else {result.is_err()} )] 
pub(crate) fn try_to_be_bytes<U:Clone, const C: usize, T: EncodeOps<U, C>, const N: usize, const B:usize>(x:&[T;N]) -> Result<[U;B],()> {
    let mut v = Vec::new();
    for i in 0..N {
        v.extend_from_slice(&x[i].to_be_bytes())
    }
    v.try_into().map_err(|_|())
}

#[inline(always)]
#[hax_lib::requires(C > 0 && C <= 16 && N <= 65536 / C)]
#[hax_lib::ensures(|result| if x.len() == N * C {result.is_ok()} else {result.is_err()} )] 
pub(crate) fn try_from_le_bytes<U, const C: usize, T: EncodeOps<U, C>, const N: usize>(x:&[U]) -> Result<[T; N],()> {
    let mut v = Vec::new();
    for c in x.chunks_exact(C) {
        v.push(T::from_le_bytes(c.try_into().unwrap()))
    }
    v.try_into().map_err(|_|())
}

#[inline(always)]
#[hax_lib::requires(C > 0 && C <= 16 && N <= 65536 / C)]
#[hax_lib::ensures(|result| if x.len() == N * C {result.is_ok()} else {result.is_err()} )] 
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
