use core::ops::*;
use core::num::Wrapping;

pub struct Secret<T>(T);

impl<T> Secret<T> {
    fn declassify(self) -> T {self.0}
}

impl<T> From<T> for Secret<T> {
    fn from(x:T) -> Secret<T> {Secret(x)}
}

impl<T:Clone> Clone for Secret<T> {
    fn clone(&self) -> Self {
        Secret(self.0.clone())
    }
}

impl<T:Clone+Copy> Copy for Secret<T> {}

pub trait Classify where Self: Sized {
    fn classify(self) -> Secret<Self> {Secret(self)}
}

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


impl Secret<u32> {
    pub fn wrapping_add<T:Into<Secret<u32>>>(self,rhs:T) -> Self {
        self.declassify().wrapping_add(rhs.into().declassify()).classify()
    }
    pub fn wrapping_sub<T:Into<Secret<u32>>>(self,rhs:T) -> Self {
        self.declassify().wrapping_sub(rhs.into().declassify()).classify()
    }
    pub fn wrapping_mul<T:Into<Secret<u32>>>(self,rhs:T) -> Self {
        self.declassify().wrapping_mul(rhs.into().declassify()).classify()
    }
    pub fn rotate_left(self,rhs:u32) -> Self {
        self.declassify().rotate_left(rhs).classify()
    }
    pub fn rotate_right(self,rhs:u32) -> Self {
        self.declassify().rotate_right(rhs).classify()
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

impl<T:Sized, const N:usize> From<Secret<[T;N]>> for [Secret<T>;N] {
    fn from(x:Secret<[T;N]>) -> Self {x.0.map(|v| Secret(v))}
}

impl<V:Iterator> From<Secret<V>> for Vec<Secret<V::Item>> {
    fn from(x:Secret<V>) -> Self {x.0.into_iter().map(|v| Secret(v)).collect()}
}

pub fn add(left: u32, right: i8) -> U32 {
    let a = [0,1,2];
    let b: Secret<[u32;3]> = a.into();
    let c: [U32;3] = b.into();
    c[1] << right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result.declassify(), 4);
    }
}
