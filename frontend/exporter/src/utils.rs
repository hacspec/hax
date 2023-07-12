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

pub(crate) use fatal;
pub(crate) use span_fatal;
pub(crate) use supposely_unreachable;
