// error[HaxFront]: Supposely unreachable place in the Rust AST. The label is "ImplExprPredNotFound".
//                  This error report happend because some assumption about the Rust AST was broken.

pub enum Error {
    Fail,
}

impl Error {
    pub fn for_application_callback() -> impl FnOnce() -> Self {
        || Self::Fail
    }
}
