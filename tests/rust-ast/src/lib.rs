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

// error: The THIR body of item DefId(0:7 ~ rust_ast[d581]::main::_::{constant#1}) was stolen.

const _MY_CONST: bool = true;

pub fn main() {
    const _: [(); 1] = [(); _MY_CONST as usize];
}
