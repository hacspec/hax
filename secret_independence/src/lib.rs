use core::ops::*;

#[repr(transparent)]
pub struct Secret<T>(T);

pub trait Classify where Self: Sized {
    fn classify(self) -> Secret<Self> {Secret(self)}
}

impl<T> From<T> for Secret<T> {
    fn from(x:T) -> Secret<T> {Secret(x)}
}

impl<T> Secret<T> {
    pub fn declassify(self) -> T {self.0}
} 

impl<T:Clone> Clone for Secret<T> {
    fn clone(&self) -> Self {
        Secret(self.0.clone())
    }
}

impl<T:Clone+Copy> Copy for Secret<T> {}

impl<T:Sized> Classify for T {}

impl<T: Add,V:Into<Secret<T>>> Add<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn add(self, rhs: V) -> Self::Output {
        self.declassify().add(rhs.into().declassify()).into()
    }
}

/* Alternative, generalize RHS:
impl<U, T: Add<U>> Add<Secret<U>> for Secret<T> {
    type Output = Secret<T::Output>;
    fn add(self, rhs: Secret<U>) -> Self::Output {
        self.declassify().add(rhs.declassify()).into()
    }
}
*/

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

impl<T: BitOr,V:Into<Secret<T>>> BitOr<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn bitor(self, rhs: V) -> Self::Output {
        self.declassify().bitor(rhs.into().declassify()).into()
    }
}

impl<T: BitAnd,V:Into<Secret<T>>> BitAnd<V> for Secret<T> {
    type Output = Secret<T::Output>;
    fn bitand(self, rhs: V) -> Self::Output {
        self.declassify().bitand(rhs.into().declassify()).into()
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

impl<T:Sized, const N:usize> From<Secret<[T;N]>> for [Secret<T>;N] {
    fn from(x:Secret<[T;N]>) -> Self {x.0.map(|v| Secret(v))}
}

impl<T> From<Secret<Vec<T>>> for Vec<Secret<T>> {
    fn from(x:Secret<Vec<T>>) -> Self {x.0.into_iter().map(|v| Secret(v)).collect()}
}

pub trait ClassifyArray<T,const N:usize> {
    fn classify_all(self) -> [Secret<T>;N];
}

impl<T,const N:usize> ClassifyArray<T,N> for [T;N] {
    fn classify_all(self) -> [Secret<T>;N] {
        self.map(|v| v.classify())
    }
}

pub trait ClassifyVec<T> {
    fn classify_all(self) -> Vec<Secret<T>>;
}

impl<T> ClassifyVec<T> for Vec<T> {
    fn classify_all(self) -> Vec<Secret<T>> {
        self.into_iter().map(|v| v.classify()).collect()
    }
}

pub trait DeclassifyArray<T,const N:usize> {
    fn declassify_all(self) -> [T;N];
}

impl<T,const N:usize> DeclassifyArray<T,N> for [Secret<T>;N] {
    fn declassify_all(self) -> [T;N] {
        self.map(|v| v.declassify())
    }
}

pub trait DeclassifyVec<T> {
    fn declassify_all(self) -> Vec<T>;
}

impl<T> DeclassifyVec<T> for Vec<Secret<T>> {
    fn declassify_all(self) -> Vec<T> {
        self.into_iter().map(|v| v.declassify()).collect()
    }
}

pub trait IntOps where Self:Sized {
    fn wrapping_add<T:Into<Secret<u32>>>(self,rhs:T) -> Self;
    fn wrapping_sub<T:Into<Secret<u32>>>(self,rhs:T) -> Self;
    fn wrapping_mul<T:Into<Secret<u32>>>(self,rhs:T) -> Self;
    fn rotate_left(self,rhs:u32) -> Self;
    fn rotate_right(self,rhs:u32) -> Self;
}

pub trait ToBytes<const N:usize> : Copy {
    fn to_le_bytes(self) -> [U8;N];
    fn to_be_bytes(self) -> [U8;N];
}

pub trait FromBytes<T:Into<U8>,const N:usize> : Copy {
    fn from_le_bytes(x:&[T;N]) -> Self;
    fn from_be_bytes(x:&[T;N]) -> Self;
}

pub trait TryToBytes<const C:usize, const N:usize> : Copy {
    fn to_le_bytes(self) -> Result<[U8;N],()>;
    fn to_be_bytes(self) -> Result<[U8;N],()>;
}

pub trait TryFromBytes<T:Into<U8>,const N:usize> : Copy {
    fn from_le_bytes(x:&[T]) -> Result<Self,()>;
    fn from_be_bytes(x:&[T]) -> Result<Self,()>;
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
pub type Bytes<const N:usize> = [U8;N];
pub type ByteSeq = Vec<U8>;

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

impl ToBytes<4> for Secret<u32> {
    fn to_le_bytes(self) -> [U8;4] {
        self.declassify().to_le_bytes().classify().into()
    }
    fn to_be_bytes(self) -> [U8;4] {
        self.declassify().to_be_bytes().classify().into()
    }
}

impl<T:Copy+Into<U8>> FromBytes<T,4> for Secret<u32> {
    fn from_le_bytes(x:&[T;4]) -> Self {
        u32::from_le_bytes(x.map(|i| i.into().declassify())).classify()
    }
    fn from_be_bytes(x:&[T;4]) -> Self {
        u32::from_be_bytes(x.map(|i| i.into().declassify())).classify()
    }
}


impl<const C:usize, T:ToBytes<C>, const M:usize, const N:usize> TryToBytes<C,M> for [T;N] {
    fn to_le_bytes(self) -> Result<[U8;M],()> {
        let mut v = Vec::new();
        for i in 0..N {
            v.extend_from_slice(&self[i].to_le_bytes())
        }
        v.try_into().map_err(|_|())
    }
    fn to_be_bytes(self) -> Result<[U8;M],()> {
        let mut v = Vec::new();
        for i in 0..N {
            v.extend_from_slice(&self[i].to_be_bytes())
        }
        v.try_into().map_err(|_|())
    }
}


impl<U:Into<U8>, const C:usize, T:FromBytes<U,C>, const N:usize> TryFromBytes<U,C> for [T;N] {
    fn from_le_bytes(x:&[U]) -> Result<Self,()> {
        let mut v = Vec::new();
        for c in x.chunks_exact(C) {
            v.push(T::from_le_bytes(c.try_into().unwrap()))
        }
        v.try_into().map_err(|_|())
    }
    fn from_be_bytes(x:&[U]) -> Result<Self,()> {
        let mut v = Vec::new();
        for c in x.chunks_exact(C) {
            v.push(T::from_be_bytes(c.try_into().unwrap()))
        }
        v.try_into().map_err(|_|())
    }
}
