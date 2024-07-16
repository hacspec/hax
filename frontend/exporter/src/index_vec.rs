use crate::prelude::*;

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct IndexVec<I: 'static, T: 'static> {
    pub raw: Vec<T>,
    _marker: std::marker::PhantomData<fn(_: &I)>,
}

#[cfg(feature = "rustc")]
impl<I: rustc_index::Idx, T: Sized> IndexVec<I, T> {
    pub fn into_iter_enumerated(
        self,
    ) -> impl DoubleEndedIterator<Item = (I, T)> + ExactSizeIterator {
        rustc_index::IndexVec::from_raw(self.raw).into_iter_enumerated()
    }
    pub fn into_iter(self) -> impl DoubleEndedIterator<Item = T> + ExactSizeIterator {
        self.raw.into_iter()
    }
}

#[cfg(feature = "rustc")]
impl<I: rustc_index::Idx, T: Sized> std::ops::Deref for IndexVec<I, T> {
    type Target = rustc_index::IndexSlice<I, T>;
    fn deref(&self) -> &Self::Target {
        Self::Target::from_raw(&self.raw)
    }
}

#[cfg(feature = "rustc")]
impl<I: rustc_index::Idx, T: Sized> std::ops::DerefMut for IndexVec<I, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Self::Target::from_raw_mut(&mut self.raw)
    }
}

#[cfg(feature = "rustc")]
impl<I: rustc_index::Idx, T> Into<IndexVec<I, T>> for rustc_index::IndexVec<I, T> {
    fn into(self) -> IndexVec<I, T> {
        IndexVec {
            raw: self.raw,
            _marker: std::marker::PhantomData,
        }
    }
}

#[cfg(feature = "rustc")]
impl<S, J: rustc_index::Idx, I: rustc_index::Idx + SInto<S, J>, U: Clone, T: SInto<S, U>>
    SInto<S, IndexVec<J, U>> for rustc_index::IndexSlice<I, T>
{
    fn sinto(&self, s: &S) -> IndexVec<J, U> {
        IndexVec {
            raw: self.raw.sinto(s),
            _marker: std::marker::PhantomData,
        }
    }
}

#[cfg(feature = "rustc")]
impl<I, T> FromIterator<T> for IndexVec<I, T>
where
    I: rustc_index::Idx,
{
    #[inline]
    fn from_iter<It: IntoIterator<Item = T>>(iter: It) -> Self {
        Self {
            raw: Vec::from_iter(iter),
            _marker: std::marker::PhantomData,
        }
    }
}

macro_rules! make_idx_wrapper {
    ($($mod:ident)::+, $type:ident) => {
        #[derive_group(Serializers)]#[derive(Copy, Clone, Eq, Debug, Hash, PartialEq, PartialOrd, Ord, JsonSchema)]
        #[serde(untagged)]
        pub enum $type {
            $type(usize),
        }
        #[cfg(feature = "rustc")]
        const _: () = {
            use rustc_index::Idx;
            type OriginalType = $($mod::)+$type;
            impl Idx for $type {
                fn new(idx: usize) -> Self {
                    $type::$type(idx)
                }
                fn index(self) -> usize {
                    let $type::$type(x) = self;
                    x.index()
                }
            }
            impl<S> SInto<S, $type> for OriginalType {
                fn sinto(&self, _s: &S) -> $type {
                    $type::new(self.index())
                }
            }
        };
    };
}
pub(crate) use make_idx_wrapper;
