/// See [`std::borrow::Borrow`]
trait Borrow<Borrowed> {
    /// See [`std::borrow::Borrow::borrow`]
    fn borrow(&self) -> &Borrowed;
}

impl<T> Borrow<T> for T {
    fn borrow(&self) -> &T {
        self
    }
}

/// See [`std::borrow::BorrowMut`]
// Excluded from F*: hax rejects a `&mut` return.
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
trait BorrowMut<Borrowed>: Borrow<Borrowed> {
    /// See [`std::borrow::BorrowMut::borrow_mut`]
    fn borrow_mut(&mut self) -> &mut Borrowed;
}

#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
impl<T> BorrowMut<T> for T {
    fn borrow_mut(&mut self) -> &mut T {
        self
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_borrow_reflexive(x in any::<u8>()) {
            prop_assert_eq!(
                *super::Borrow::borrow(&x),
                *core::borrow::Borrow::<u8>::borrow(&x)
            );
        }

        #[test]
        fn test_borrow_mut_reflexive(x in any::<u8>(), y in any::<u8>()) {
            let mut model = x;
            let mut std_ = x;
            prop_assert_eq!(
                *super::BorrowMut::borrow_mut(&mut model),
                *core::borrow::BorrowMut::<u8>::borrow_mut(&mut std_)
            );
            *super::BorrowMut::borrow_mut(&mut model) = y;
            *core::borrow::BorrowMut::<u8>::borrow_mut(&mut std_) = y;
            prop_assert_eq!(model, std_);
        }
    }
}
