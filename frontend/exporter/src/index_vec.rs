use crate::prelude::*;
use rustc_index::{Idx, IndexSlice};

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub struct IndexVec<I: Idx, T> {
    pub raw: Vec<T>,
    _marker: std::marker::PhantomData<fn(_: &I)>,
}

impl<I: Idx, T: Sized> IndexVec<I, T> {
    pub fn into_iter_enumerated(
        self,
    ) -> impl DoubleEndedIterator<Item = (I, T)> + ExactSizeIterator {
        rustc_index::IndexVec::from_raw(self.raw).into_iter_enumerated()
    }
    pub fn into_iter(self) -> impl DoubleEndedIterator<Item = T> + ExactSizeIterator {
        self.raw.into_iter()
    }
}

impl<I: Idx, T: Sized> std::ops::Deref for IndexVec<I, T> {
    type Target = IndexSlice<I, T>;
    fn deref(&self) -> &Self::Target {
        Self::Target::from_raw(&self.raw)
    }
}

impl<I: Idx, T: Sized> std::ops::DerefMut for IndexVec<I, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Self::Target::from_raw_mut(&mut self.raw)
    }
}

impl<I: Idx, T> Into<IndexVec<I, T>> for rustc_index::IndexVec<I, T> {
    fn into(self) -> IndexVec<I, T> {
        IndexVec {
            raw: self.raw,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<S, J: Idx, I: Idx + SInto<S, J>, U: Clone /*TODO: remove me?*/, T: SInto<S, U>>
    SInto<S, IndexVec<J, U>> for IndexSlice<I, T>
{
    fn sinto(&self, s: &S) -> IndexVec<J, U> {
        IndexVec {
            raw: self.raw.sinto(s),
            _marker: std::marker::PhantomData,
        }
    }
}

impl<I, T> FromIterator<T> for IndexVec<I, T>
where
    I: Idx,
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
        #[derive(Copy, Clone, Eq, Debug, Hash, PartialEq, PartialOrd, Ord, Serialize, Deserialize, JsonSchema)]
        #[serde(untagged)]
        pub enum $type {
            $type(usize),
        }
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
