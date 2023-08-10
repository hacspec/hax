use crate::prelude::*;

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub struct IndexVec<I: rustc_index::Idx, T> {
    pub raw: Vec<T>,
    _marker: std::marker::PhantomData<fn(_: &I)>,
}

impl<I: rustc_index::Idx, T> Into<IndexVec<I, T>> for rustc_index::IndexVec<I, T> {
    fn into(self) -> IndexVec<I, T> {
        IndexVec {
            raw: self.raw,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<
        S,
        II: rustc_index::Idx,
        TT: Clone, /*TODO: remove me?*/
        I: rustc_index::Idx + SInto<S, II>,
        T: SInto<S, TT>,
    > SInto<S, IndexVec<II, TT>> for rustc_index::IndexVec<I, T>
{
    fn sinto(&self, s: &S) -> IndexVec<II, TT> {
        IndexVec {
            raw: self.raw.sinto(s),
            _marker: std::marker::PhantomData,
        }
    }
}

impl<
        S,
        II: rustc_index::Idx,
        TT: Clone, /*TODO: remove me?*/
        I: rustc_index::Idx + SInto<S, II>,
        T: SInto<S, TT>,
    > SInto<S, IndexVec<II, TT>> for rustc_index::IndexSlice<I, T>
{
    fn sinto(&self, s: &S) -> IndexVec<II, TT> {
        IndexVec {
            raw: self.raw.sinto(s),
            _marker: std::marker::PhantomData,
        }
    }
}

macro_rules! make_idx_wrapper {
    ($($mod:ident)::+, $type:ident) => {
        #[derive(Copy, Clone, Eq, Debug, Hash, PartialEq, Serialize, Deserialize, JsonSchema)]
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
