macro_rules! span_fatal {
    ($s:ident, $span:expr, $($other:tt)*) => {
        $s.base().tcx.sess.span_fatal($span,format!($($other)*))
    }
}

/*
Not useful for now.

macro_rules! no_span_fatal {
    ($s:ident, $($other:tt)*) => {
        $s.base().tcx.sess.fatal(format!($($other)*))
    }
}
pub(crate) use no_span_fatal;
*/

macro_rules! fatal {
    ($s:ident, $($other:tt)*) => {
        {let tcx = $s.base().tcx;
        match $s.base().opt_def_id {
            Some(did) =>
                tcx.sess.span_fatal(tcx.def_span(did), format!($($other)*)),
            None =>
                tcx.sess.fatal(format!($($other)*)),
        }}
    }
}

macro_rules! supposely_unreachable {
    (@$verb:tt $label:literal : $($e:expr),*$(,)?) => {
        $verb !(concat!("
Supposely unreachable place in the Rust AST. The label is ", stringify!($label), ".
This ", stringify!($verb), " happend because I thought some node in the Rust AST could not show up under certain condition(s).

Please report that message along with the crate!

Meta-information:
", $(stringify!( - $e: ), " {:#?}", "\n",)*), $($e,)*);
    };
    ($($t:tt)*) => {
        #[cfg(feature = "minimal-ast")] supposely_unreachable!(@eprintln $($t)*);
        #[cfg(not(feature = "minimal-ast"))] supposely_unreachable!(@println $($t)*);
    };
}

macro_rules! supposely_unreachable_fatal {
    ($($tt:tt)*) => {
        supposely_unreachable!($($tt)*);
        panic!()
    }
}

pub(crate) use fatal;
pub(crate) use span_fatal;
pub(crate) use supposely_unreachable;
pub(crate) use supposely_unreachable_fatal;

pub trait SExpect: Sized {
    type Output;
    fn s_expect<'tcx, S: crate::BaseState<'tcx>>(self, s: &S, message: &str) -> Self::Output;

    fn s_unwrap<'tcx, S: crate::BaseState<'tcx>>(self, s: &S) -> Self::Output {
        self.s_expect(s, "")
    }
}

mod s_expect_impls {
    use super::*;
    struct Dummy;
    impl std::fmt::Debug for Dummy {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "...")
        }
    }

    fn s_expect_error<'tcx>(
        s: &impl crate::BaseState<'tcx>,
        expected: impl std::fmt::Debug,
        got: impl std::fmt::Debug,
        message: &str,
    ) -> ! {
        fatal!(s, "s_expect: expected {expected:?}, got {got:?}. {message}")
    }

    impl<T: std::fmt::Debug> SExpect for Option<T> {
        type Output = T;
        fn s_expect<'tcx, S: crate::BaseState<'tcx>>(self, s: &S, message: &str) -> Self::Output {
            self.unwrap_or_else(|| s_expect_error(s, Some(Dummy), None::<()>, message))
        }
    }

    impl<T: std::fmt::Debug, E: std::fmt::Debug> SExpect for Result<T, E> {
        type Output = T;
        fn s_expect<'tcx, S: crate::BaseState<'tcx>>(self, s: &S, message: &str) -> Self::Output {
            self.unwrap_or_else(|e| s_expect_error(s, Ok::<_, ()>(Dummy), Err::<(), _>(e), message))
        }
    }
}

macro_rules! s_assert {
    ($s:ident, $assertion:expr) => {{
        if $assertion {
            ()
        } else {
            fatal!($s, "assertion failed: {}", stringify!($assertion))
        }
    }};
}
pub(crate) use s_assert;
